/*
 * WDoMC.c
 *
 *  Created on: 2016-5-10
 *      Author: jianghua
 *  this is the first version of weighted maximum clique based on incremental
 *  maxsat reasoning
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/times.h>
#include <sys/types.h>
#include <limits.h>
#include <unistd.h>
#include <sys/resource.h>
#include <math.h>
#include <assert.h>
#define WORD_LENGTH 100
#define TRUE 1
#define FALSE 0
#define NONE -1
#define DELIMITER 0
#define PASSIVE 0
#define ACTIVE 1
#define P_TRUE 2
#define P_FALSE 0
#define NULL_REASON -1
#define NO_REASON -3
#define CONFLICT -1978
#define MAX_NODE 1000000
#define max_expand_depth 100000
#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item
#define ptr(stack) stack ## _fill_pointer
#define is_neibor(i,j) matrice[i][j]

#define CUR_CLQ_SIZE Clique_Stack_fill_pointer
#define CURSOR Cursor_Stack[Cursor_Stack_fill_pointer-1]
#define MIN(a,b) a<=b?a:b
#define BIT_MAP_SIZE 4097

#define SET_EDGE(row,col) ((*(Adj_Matrix + (row)* MATRIX_ROW_WIDTH + ((col) >> 3))) |= (1 << ((col) & 7)))
#define GET_EDGE(row,col) ((*(Adj_Matrix + (row)* MATRIX_ROW_WIDTH + ((col) >> 3))) & (1 << ((col) & 7)))

#define iMatrix(i) (Adj_Matrix+(i)*MATRIX_ROW_WIDTH)
#define Matrix(i,j) ((*((i) + ((j) >> 3))) & (1 << ((j) & 7)))

static int FORMAT = 1, NB_NODE, NB_NODE_O, NB_EDGE, NB_EDGE_O, MAX_CLQ_SIZE,
		INIT_CLQ_SIZE, HIDDEN_WEIGHT, INIT_ORDERING, NB_BACK_CLIQUE,
		MATRIX_ROW_WIDTH, MAX_SUBGRAPH_SIZE, K_CORE_G = 0;

static int MAX_CLQ_WEIGHT, CUR_CLQ_WEIGHT, INIT_CLQ_WEIGHT, MAX_ISET_WEIGHT,
		CUR_NODE_WEIGHT, UPPER_WEIGHT_BOUND;
static int Max_Degree = 0;
static int Node_Degree[MAX_NODE];
static int Max_Weight = 0;
static int Top_Weight[MAX_NODE];
static int Node_Weight[MAX_NODE];
static char Node_State[MAX_NODE];
static int **Node_Neibors;

static int rankVar[MAX_NODE];

static int Candidate_Stack_fill_pointer = 0;
static int Candidate_Stack[MAX_NODE * 2];
static int Vertex_UB[MAX_NODE * 2];
static int Clique_Stack_fill_pointer;
static int *Clique_Stack, *MaxCLQ_Stack;
static int Cursor_Stack[max_expand_depth];
static int Cursor_Stack_fill_pointer = 0;
static int Weight_Mod = 200;
static unsigned char * Adj_Matrix;

int threshold;

const char* resPath;
const char* dataPath;

static int iSET_COUNT = 0, iSET_TOTAL_WEIGHT = 0;
static int *iSET_Size;
static int *iSET_Weight;
static char *iSET_Tested;
static int **iSET;

/* the new data structures for maxsat reasoning*/

static int **IS, *IS_HEAD, *IS_BACKUP, IS_LENGTH;
#define IS_STAT(i) (*((char *)IS[i]))
#define IS_USED(i) (*(((char *)IS[i])+1))
#define IS_INVO(i) (*(((char *)IS[i])+2))
#define IS_TEST(i) (*(((char *)IS[i])+3))
#define IS_WEIT(i) (*(IS[i]+1))
#define IS_SIZE(i) (*(IS[i]+2))
#define IS_TOPK(i) (*(IS[i]+3))
#define IS_NODES(i) (IS[i]+4)
/************************************/
static int *REASON_STACK;
static int REASON_STACK_fill_pointer = 0;
static int *UNIT_STACK;
static int UNIT_STACK_fill_pointer = 0;
static int *TOP_UNIT_STACK;
static int TOP_UNIT_STACK_fill_pointer = 0;
static int *NEW_UNIT_STACK;
static int NEW_UNIT_STACK_fill_pointer = 0;
static int *B_STACK;
static int B_STACK_fill_pointer = 0;

static int Rollback_Point;
static int Branching_Point;
static int *Old_Name;
static int *Second_Name;
static int NB_CANDIDATE = 0, FIRST_INDEX;
static int START_MAXSAT_THD = 15;
static int BRANCHING_COUNT = 0;
static int CUR_MAX_NODE;

static int Last_Idx = 0;
static int cut_ver = 0, total_cut_ver = 0;
static int cut_inc = 0, total_cut_inc = 0;
static int cut_iset = 0, total_cut_iset = 0;
static int cut_satz = 0, total_cut_satz = 0;
static long long Branches_Nodes[6];
static int LAST_IN;

/*statistical data*/
static long long N0_B, N0_A, N1_B, N1_A, G1_B = 0, G1_A = 0;
static double D0_B, D0_A, D1_B = 0, D1_A = 0, RT1 = 0;
/*****************/

static int * Init_Adj_List;
static int BLOCK_COUNT = 0;
static int *BLOCK_LIST[100];
static double READ_TIME, INIT_TIME, SEARCH_TIME;
static double get_utime() {
	struct rusage utime;
	getrusage(RUSAGE_SELF, &utime);
	return (double) (utime.ru_utime.tv_sec
			+ (double) utime.ru_utime.tv_usec / 1000000);
}
static int weight_desc(const void * a, const void * b) {
	return Node_Weight[*((int *) b)] - Node_Weight[*((int *) a)];
}
static int weight_desc2(const void * a, const void * b) {
	return *(((int *) b) + 1) - *(((int *) a) + 1);
}
static int int_cmp_desc(const void * a, const void * b) {
	return *((int *) b) - *((int *) a);
}
static int int_cmp_asc(const void * a, const void * b) {
	return *((int *) a) - *((int *) b);
}
static int is_adjacent(int node1, int node2) {
	int neibor, *neibors;
	neibors = Node_Neibors[node1];
	for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
		if (neibor == node2) {
			return TRUE;
		}
	}
	return FALSE;
}

static void check_clique_in_result_file(char *input_file) {
	FILE* fp_in = fopen(input_file, "r");
	int i = 0, j, node, clique_size = 0, clique[10240];
	char line[1024100], word[100], *addr_line;

	while (fgets(line, 1024000, fp_in) != NULL ) {
		addr_line = line;
		if (line[0] == 'M') {
			addr_line++;
			while (sscanf(addr_line, "%d", &node) > 0) {
				clique[i++] = node;
				sscanf(addr_line, "%s", word);
				addr_line += strlen(word) + 1;
			}
			clique_size = i;
			break;
		}
	}
	fclose(fp_in);
	if (clique_size > 0) {
		printf("read %d clique:\n", clique_size);
		for (i = 0; i < clique_size; i++)
			printf("%d ", clique[i]);
		printf("\n");

		for (i = 0; i < clique_size; i++) {
			for (j = i + 1; j < clique_size; j++) {
				if (is_adjacent(clique[i], clique[j]) == FALSE) {
					printf("find non-adjacent vertices: %d %d\n", clique[i],
							clique[j]);
					printf("#FALSE:%s\n", input_file);
					return;
				}

			}
		}
		printf("#TRUE:%s\n", input_file);
	} else {
		printf("#NONE:%s\n", input_file);
	}
}

static void allocate_memory_for_adjacency_list(int nb_node, int nb_edge,
		int offset) {
	int i, block_size = 40960000, free_size = 0;
	Init_Adj_List = (int *) malloc((2 * nb_edge + nb_node) * sizeof(int));
	if (Init_Adj_List == NULL ) {
		for (i = 1; i <= NB_NODE; i++) {
			if (Node_Degree[i - offset] + 1 > free_size) {
				Node_Neibors[i] = (int *) malloc(block_size * sizeof(int));
				BLOCK_LIST[BLOCK_COUNT++] = Node_Neibors[i];
				free_size = block_size - (Node_Degree[i - offset] + 1);
			} else {
				Node_Neibors[i] = Node_Neibors[i - 1]
						+ Node_Degree[i - 1 - offset] + 1;
				free_size = free_size - (Node_Degree[i - offset] + 1);
			}
		}
	} else {
		BLOCK_COUNT = 1;
		BLOCK_LIST[BLOCK_COUNT - 1] = Init_Adj_List;
		Node_Neibors[1] = Init_Adj_List;
		for (i = 2; i <= NB_NODE; i++) {
			Node_Neibors[i] = Node_Neibors[i - 1] + Node_Degree[i - 1 - offset]
					+ 1;
		}
	}
}

static int read_graph_wclq_format(char *input_file) {
	int j, node = 1, l_node, r_node, nb_edge = 0, max_node = NONE, offset = 0,
			weight;
	char line[128], word[10];

	char rankfile[30];
    strcpy(rankfile,resPath);
    strcat(rankfile,input_file);
    strcat(rankfile,"_rank.csv");

	FILE* fp = fopen(rankfile, "r");
	if (fp == NULL ) {
		printf("R can not open file varRank.csv");
		return FALSE;
	}

    printf("R reading the file varRank...\n");

    int i = 1;
    int rank;
    while (fgets(line, 127, fp) != NULL ) {
//        fp >> rankVar[i];
        sscanf(line, "%d", &rank);
        rankVar[i] = rank;
//        printf("rank of variable %d is %d\n", i, rankVar[i]);
        i++;
    }

    char filename[30];
    strcpy(filename,dataPath);
    strcat(filename,input_file);

	FILE* fp_in = fopen(filename, "r");
	if (fp_in == NULL ) {
		printf("R can not open file %s\n", filename);
		return FALSE;
	}

	printf("R reading wclq file  ...\n");

	memset(Node_Degree, 0, MAX_NODE*sizeof(int));

	while (fgets(line, 127, fp_in) != NULL ) {
		if (line[0] == 'v') {
			sscanf(line, "%s%d%d", word, &node, &weight);
			if (rankVar[node] <= threshold){
			    Top_Weight[rankVar[node]] = weight;
			    Node_Weight[rankVar[node]] = Top_Weight[rankVar[node]];
			    if (rankVar[node] > max_node)
                    max_node = rankVar[node];
			}
		} else if (line[0] == 'e') {
			sscanf(line, "%s%d%d", word, &l_node, &r_node);
			if (rankVar[l_node] <= threshold && rankVar[r_node] <= threshold && rankVar[l_node] >= 0 && rankVar[r_node] >= 0 && rankVar[l_node] != rankVar[r_node]) {
				nb_edge++;
				Node_Degree[rankVar[l_node]]++;
				Node_Degree[rankVar[r_node]]++;
				if (rankVar[l_node] == 0 || rankVar[r_node] == 0)
					offset = 1;
			}
		}
	}
	NB_NODE = max_node + offset;

	printf("R the graph size is %d\n", NB_NODE);
	if (NB_NODE > MAX_NODE) {
		printf("R the graph goes beyond the max size can be processed: %d\n",
				NB_NODE);
		exit(0);
	}

	Node_Neibors = (int **) malloc((NB_NODE + 1) * sizeof(int *));
	allocate_memory_for_adjacency_list(NB_NODE, nb_edge, offset);
	memset(Node_Degree, 0, (NB_NODE + 1) * sizeof(int));

	nb_edge = 0;
	fseek(fp_in, 0L, SEEK_SET);
	while (fgets(line, 127, fp_in) != NULL ) {
		if (line[0] == 'e') {
			sscanf(line, "%s%d%d", word, &l_node, &r_node);
			if (rankVar[l_node] <= threshold && rankVar[r_node] <= threshold && rankVar[l_node] >= 0 && rankVar[r_node] >= 0 && rankVar[l_node] != rankVar[r_node]) {
				rankVar[l_node] += offset;
				rankVar[r_node] += offset;
				for (j = 0; j < Node_Degree[rankVar[l_node]]; j++) {
					if (Node_Neibors[rankVar[l_node]][j] == rankVar[r_node])
						break;
				}
				if (j == Node_Degree[rankVar[l_node]]) {
					Node_Neibors[rankVar[l_node]][Node_Degree[rankVar[l_node]]] = rankVar[r_node];
					Node_Neibors[rankVar[r_node]][Node_Degree[rankVar[r_node]]] = rankVar[l_node];
					Node_Degree[rankVar[l_node]]++;
					Node_Degree[rankVar[r_node]]++;
					Node_Weight[rankVar[l_node]] += Top_Weight[rankVar[r_node]];
					Node_Weight[rankVar[r_node]] += Top_Weight[rankVar[l_node]];
					nb_edge++;
				}
			}
		}
	}
	NB_EDGE = nb_edge;
	Max_Degree = 0;
	for (node = 1; node <= NB_NODE; node++) {
		Node_Neibors[node][Node_Degree[node]] = NONE;

		if (Node_Degree[node] > Max_Degree)
			Max_Degree = Node_Degree[node];
	}
	MaxCLQ_Stack = (int *) malloc((Max_Degree + 1) * sizeof(int));
	return TRUE;
}

static int read_graph_node_node(char *input_file, int format) {
	int j, node = 1, l_node, r_node, nb_edge = 0, max_node = NONE, offset = 0;
	char line[128], word[10];
	FILE* fp_in = fopen(input_file, "r");
	if (fp_in == NULL ) {
		printf("R can not open file %s\n", input_file);
		return FALSE;
	}
	if (format == 1)
		printf("R reading file <e n1 n2> ...\n");
	else
		printf("R reading file <n1 n2> ...\n");
	memset(Node_Degree, 0, MAX_NODE*sizeof(int));
	while (fgets(line, 127, fp_in) != NULL ) {
		if ((format == 1 && line[0] == 'e')
				|| (format == 2 && line[0] != '%')) {
			if (format == 1)
				sscanf(line, "%s%d%d", word, &l_node, &r_node);
			else
				sscanf(line, "%d%d", &l_node, &r_node);
			if (l_node >= 0 && r_node >= 0 && l_node != r_node) {
				nb_edge++;
				Node_Degree[l_node]++;
				Node_Degree[r_node]++;
				if (l_node > max_node)
					max_node = l_node;
				if (r_node > max_node)
					max_node = r_node;
				if (l_node == 0 || r_node == 0)
					offset = 1;
			}
		}
	}
	NB_NODE = max_node + offset;

	printf("R the graph size is %d\n", NB_NODE);
	if (NB_NODE > MAX_NODE) {
		printf("R the graph goes beyond the max size can be processed: %d\n",
				NB_NODE);
		exit(0);
	}

	for (node = 1; node <= NB_NODE; node++) {
		Top_Weight[node] = node % Weight_Mod + 1;
		Node_Weight[node] = Top_Weight[node];
	}

	Node_Neibors = (int **) malloc((NB_NODE + 1) * sizeof(int *));
	allocate_memory_for_adjacency_list(NB_NODE, nb_edge, offset);
	memset(Node_Degree, 0, (NB_NODE + 1) * sizeof(int));

	nb_edge = 0;
	fseek(fp_in, 0L, SEEK_SET);
	while (fgets(line, 127, fp_in) != NULL ) {
		if ((format == 1 && line[0] == 'e')
				|| (format == 2 && line[0] != '%')) {
			if (format == 1)
				sscanf(line, "%s%d%d", word, &l_node, &r_node);
			else
				sscanf(line, "%d%d", &l_node, &r_node);
			if (l_node >= 0 && r_node >= 0 && l_node != r_node) {
				l_node += offset;
				r_node += offset;
				for (j = 0; j < Node_Degree[l_node]; j++) {
					if (Node_Neibors[l_node][j] == r_node)
						break;
				}
				if (j == Node_Degree[l_node]) {
					Node_Neibors[l_node][Node_Degree[l_node]] = r_node;
					Node_Neibors[r_node][Node_Degree[r_node]] = l_node;
					Node_Degree[l_node]++;
					Node_Degree[r_node]++;
					Node_Weight[l_node] += Top_Weight[r_node];
					Node_Weight[r_node] += Top_Weight[l_node];
					nb_edge++;
				}
			}
		}
	}
	NB_EDGE = nb_edge;
	Max_Degree = 0;
	for (node = 1; node <= NB_NODE; node++) {
		Node_Neibors[node][Node_Degree[node]] = NONE;

		if (Node_Degree[node] > Max_Degree)
			Max_Degree = Node_Degree[node];
	}
	MaxCLQ_Stack = (int *) malloc((Max_Degree + 1) * sizeof(int));
	return TRUE;
}

static int build_simple_graph_instance(char *input_file) {
	char * fileStyle = strrchr(input_file, '.') + 1;
	struct rusage endtime;
	if (strrchr(input_file, '.') == NULL ) {
		read_graph_node_node(input_file, 1);
	} else if (strcmp(fileStyle, "clq") == 0) {
		read_graph_node_node(input_file, 1);
	} else if (strcmp(fileStyle, "edges") == 0) {
		read_graph_node_node(input_file, 2);
	} else if (strcmp(fileStyle, "mtx") == 0) {
		read_graph_node_node(input_file, 2);
	} else if (strcmp(fileStyle, "wclq") == 0) {
		read_graph_wclq_format(input_file);
	} else if (FORMAT == 1) {
		read_graph_node_node(input_file, 1);
	} else if (FORMAT == 2) {
		read_graph_node_node(input_file, 2);
	} else {
		read_graph_node_node(input_file, 1);
	}
	printf("R Instance Information: #node=%d #edge=%d density=%9.8f\n", NB_NODE,
			NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
	NB_NODE_O = NB_NODE;
	NB_EDGE_O = NB_EDGE;
	N0_B = NB_NODE;
	D0_B = ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1));

	READ_TIME = get_utime();
//	getrusage(RUSAGE_SELF, &endtime);
//	READ_TIME = (double) (endtime.ru_utime.tv_sec
//			+ (double) endtime.ru_utime.tv_usec / 1000000);
	printf("R the reading time is %4.2lf \n", READ_TIME);
	return TRUE;
}

//static int choose_candidate_node() {
//	int i, chosen_node = NONE, node, max_degree;
//	max_degree = -1;
//	for (i = 0; i < ptr(Candidate_Stack); i++) {
//		node = Candidate_Stack[i];
//		if (Node_Degree[node] > max_degree) {
//			max_degree = Node_Degree[node];
//			chosen_node = node;
//		}
//	}
//	return chosen_node;
//}
//static int Is_Neibor(int node1, int node2) {
//	int neibor, *neibors = Node_Neibors[node1];
//	for (neibor = *neibors; neibor != NONE; neibor = *(++neibors))
//		if (neibor == node2)
//			return TRUE;
//	return FALSE;
//}
static void sort_by_degree_degeneracy_ordering() {
	int *degree_counter, *where;
	int p1, i, node = NONE, neibor, *neibors, t, j, h, k, idx = 0;
	int cur_degree = 0;
	INIT_CLQ_SIZE = 0;
	printf("I computing initial degree degeneracy ordering...\n");


	int Max_Degree = 0;
	for (int i = 1; i<= NB_NODE; i++){
	    if (Node_Degree[i] > Max_Degree){
	        Max_Degree = Node_Degree[i];
	    }
//        printf("the degree of node %d is %d\n", i, Node_Degree[i]);
//        printf("neighbors of node %d is ", i);
//        for (int j = 0; j < Node_Degree[i]; j++){
//            printf("%d, ", Node_Neibors[i][j]);
//        }
//        printf("\n");
    }
//    printf("the maximum degree is %d\n", Max_Degree);
    MaxCLQ_Stack = (int *) malloc((Max_Degree + 1) * sizeof(int));


	where = Candidate_Stack + NB_NODE + 1;
	degree_counter = Vertex_UB;
	memset(degree_counter, 0, (Max_Degree + 1) * sizeof(int));

	for (node = 1; node <= NB_NODE; node++) {
		degree_counter[Node_Degree[node]]++;
	}
	j = 0;
	for (i = 0; i <= Max_Degree; i++) {
		k = degree_counter[i];
		degree_counter[i] = j;
		j += k;
	}

	for (node = 1; node <= NB_NODE; node++) {
		Candidate_Stack[t = degree_counter[Node_Degree[node]]++] = node;
		where[node] = t;
	}
	for (i = Max_Degree; i > 0; i--) {
		degree_counter[i] = degree_counter[i - 1];
	}
	degree_counter[0] = 0;

	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;

	p1 = 0;
	cur_degree = Node_Degree[Candidate_Stack[p1]];
	while (p1 < NB_NODE) {
		node = Candidate_Stack[p1];
		if (p1 < NB_NODE - 1
				&& Node_Degree[node] == Node_Degree[Candidate_Stack[p1 + 1]]) {
			degree_counter[Node_Degree[node]] = p1 + 1;
		}
		if (Node_Degree[node] == NB_NODE - p1 - 1) {
			INIT_CLQ_SIZE = 0;
			INIT_CLQ_WEIGHT = 0;

			for (i = p1; i < NB_NODE; i++) {
				MaxCLQ_Stack[INIT_CLQ_SIZE++] = Candidate_Stack[i];
				INIT_CLQ_WEIGHT += Top_Weight[Candidate_Stack[i]];
			}
			printf("I initial clique weight is %d\n", INIT_CLQ_WEIGHT);
			break;
		}

		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (where[neibor] > p1) {
				t = where[neibor];
				h = degree_counter[Node_Degree[neibor]];

				k = Candidate_Stack[h];

				Candidate_Stack[h] = neibor;
				where[neibor] = h;

				Candidate_Stack[t] = k;
				where[k] = t;

				degree_counter[Node_Degree[neibor]]++;

				Node_Degree[neibor]--;
				if (Node_Degree[neibor]
						!= Node_Degree[Candidate_Stack[h - 1]]) {
					degree_counter[Node_Degree[neibor]] = h;
				}
			}
		}
		p1++;
	}
}

static void sort_by_degree_degeneracy_weight_ordering() {
	int *degree_counter, *where;
	int p1, i, node = NONE, neibor, *neibors, t, j, h, k;
	int cur_degree = 0, min_weight, min_idx;
	INIT_CLQ_SIZE = 0;
	printf("I computing initial degree degeneracy +weight ordering...\n");

	where = Candidate_Stack + NB_NODE + 1;
	degree_counter = Vertex_UB + NB_NODE + 1;
	memset(degree_counter, 0, (Max_Degree + 1) * sizeof(int));

	for (node = 1; node <= NB_NODE; node++) {
		degree_counter[Node_Degree[node]]++;
	}
	j = 0;
	for (i = 0; i <= Max_Degree; i++) {
		k = degree_counter[i];
		degree_counter[i] = j;
		j += k;
	}

	for (node = 1; node <= NB_NODE; node++) {
		Candidate_Stack[t = degree_counter[Node_Degree[node]]++] = node;
		where[node] = t;
	}
	for (i = Max_Degree; i > 0; i--) {
		degree_counter[i] = degree_counter[i - 1];
	}
	degree_counter[0] = 0;

	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;

	p1 = 0;

	while (p1 < NB_NODE) {
		node = Candidate_Stack[p1];
		cur_degree = Node_Degree[node];
		if (p1 < NB_NODE - 1
				&& Node_Degree[node] == Node_Degree[Candidate_Stack[p1 + 1]]) {
			degree_counter[Node_Degree[node]] = p1 + 1;
		}
		if (cur_degree == NB_NODE - p1 - 1) {
			INIT_CLQ_SIZE = NB_NODE - p1;
			INIT_CLQ_WEIGHT = 0;
			for (i = p1; i < NB_NODE; i++) {
				INIT_CLQ_WEIGHT += Top_Weight[Candidate_Stack[i]];
			}
			printf("I initial clique weight is %d\n", INIT_CLQ_WEIGHT);
			//printf("I maxcore number is %d\n", K_CORE_G);
			break;
		}
		/* find min weight*/
		i = p1 + 1;
		min_idx = p1;
		min_weight = Top_Weight[Candidate_Stack[p1]];
		while (i < NB_NODE && Node_Degree[Candidate_Stack[i]] == cur_degree) {
			if (Top_Weight[Candidate_Stack[i]] < min_weight) {
				min_weight = Top_Weight[Candidate_Stack[i]];
				min_idx = i;
			}
			i++;
		}
		if (min_idx != p1) {
			min_weight = Candidate_Stack[min_idx];
			Candidate_Stack[min_idx] = node;
			Candidate_Stack[p1] = min_weight;
			where[min_weight] = p1;
			where[node] = min_idx;
			node = min_weight;
		}
		/*end*/
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (where[neibor] > p1) {
				t = where[neibor];
				h = degree_counter[Node_Degree[neibor]];

				k = Candidate_Stack[h];

				Candidate_Stack[h] = neibor;
				where[neibor] = h;

				Candidate_Stack[t] = k;
				where[k] = t;

				degree_counter[Node_Degree[neibor]]++;

				Node_Degree[neibor]--;
				if (Node_Degree[neibor]
						!= Node_Degree[Candidate_Stack[h - 1]]) {
					degree_counter[Node_Degree[neibor]] = h;
				}
			}
		}
		p1++;
	}
	Vertex_UB[ptr(Candidate_Stack) - 1] = 0;
	for (i = ptr(Candidate_Stack) - 2; i >= 0; i--) {
		Vertex_UB[i] = Vertex_UB[i + 1] + Top_Weight[Candidate_Stack[i]];
	}
}

static void sort_by_degree_degeneracy_neibor_weight_ordering() {
	int *degree_counter, *where;
	int p1, i, node = NONE, neibor, *neibors, t, j, h, k;
	int cur_degree = 0, min_weight, min_top_weight, min_idx;
	INIT_CLQ_SIZE = 0;
	printf("I computing initial degree degeneracy +weight ordering...\n");

	where = Candidate_Stack + NB_NODE + 1;
	degree_counter = Vertex_UB + NB_NODE + 1;
	memset(degree_counter, 0, (Max_Degree + 1) * sizeof(int));

	for (node = 1; node <= NB_NODE; node++) {
		Node_Weight[node] = Top_Weight[node];
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[node] += Top_Weight[neibor];
		}
	}

	for (node = 1; node <= NB_NODE; node++) {
		degree_counter[Node_Degree[node]]++;
	}
	j = 0;
	for (i = 0; i <= Max_Degree; i++) {
		k = degree_counter[i];
		degree_counter[i] = j;
		j += k;
	}

	for (node = 1; node <= NB_NODE; node++) {
		Candidate_Stack[t = degree_counter[Node_Degree[node]]++] = node;
		where[node] = t;
	}
	for (i = Max_Degree; i > 0; i--) {
		degree_counter[i] = degree_counter[i - 1];
	}
	degree_counter[0] = 0;

	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;

	p1 = 0;

	while (p1 < NB_NODE) {
		node = Candidate_Stack[p1];
		cur_degree = Node_Degree[node];
		if (p1 < NB_NODE - 1
				&& Node_Degree[node] == Node_Degree[Candidate_Stack[p1 + 1]]) {
			degree_counter[Node_Degree[node]] = p1 + 1;
		}
		if (cur_degree == NB_NODE - p1 - 1) {
			INIT_CLQ_SIZE = NB_NODE - p1;
			INIT_CLQ_WEIGHT = 0;
			for (i = p1; i < NB_NODE; i++) {
				INIT_CLQ_WEIGHT += Top_Weight[Candidate_Stack[i]];
			}
			printf("I initial clique weight is %d\n", INIT_CLQ_WEIGHT);
			//printf("I maxcore number is %d\n", K_CORE_G);
			break;
		}
		/* find min weight*/
		i = p1 + 1;
		min_idx = p1;
		min_weight = Node_Weight[Candidate_Stack[p1]];
		min_top_weight = Top_Weight[Candidate_Stack[p1]];
		while (i < NB_NODE && Node_Degree[Candidate_Stack[i]] == cur_degree) {
			if (Node_Weight[Candidate_Stack[i]] < min_weight) {
				min_weight = Node_Weight[Candidate_Stack[i]];
				min_top_weight = Top_Weight[Candidate_Stack[i]];
				min_idx = i;
			} else if (Node_Weight[Candidate_Stack[i]] == min_weight
					&& Top_Weight[Candidate_Stack[i]] < min_top_weight) {
				//min_weight = Node_Weight[Candidate_Stack[i]];
				min_top_weight = Top_Weight[Candidate_Stack[i]];
				min_idx = i;
			}
			i++;
		}
		if (min_idx != p1) {
			min_weight = Candidate_Stack[min_idx];
			Candidate_Stack[min_idx] = node;
			Candidate_Stack[p1] = min_weight;
			where[min_weight] = p1;
			where[node] = min_idx;
			node = min_weight;
		}
		/*end*/
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (where[neibor] > p1) {
				t = where[neibor];
				h = degree_counter[Node_Degree[neibor]];

				k = Candidate_Stack[h];

				Candidate_Stack[h] = neibor;
				where[neibor] = h;

				Candidate_Stack[t] = k;
				where[k] = t;

				degree_counter[Node_Degree[neibor]]++;

				Node_Degree[neibor]--;
				if (Node_Degree[neibor]
						!= Node_Degree[Candidate_Stack[h - 1]]) {
					degree_counter[Node_Degree[neibor]] = h;
				}
				Node_Weight[neibor] -= Top_Weight[node];
			}
		}
		p1++;
	}
	Vertex_UB[ptr(Candidate_Stack) - 1] = 0;
	for (i = ptr(Candidate_Stack) - 2; i >= 0; i--) {
		Vertex_UB[i] = Vertex_UB[i + 1] + Top_Weight[Candidate_Stack[i]];
	}
}

static void sort_by_enhanced_weight_ordering() {
	int *weight_counter, *where, *neibors, neibor, max_weight = 0;
	int i, node = NONE, t, j, k;
	INIT_CLQ_SIZE = 0;
	printf("I computing initial enhanced weight degeneracy ordering...\n");

	where = Candidate_Stack + NB_NODE + 1;
	weight_counter = Vertex_UB;

	for (node = 1; node <= NB_NODE; node++) {
		Node_Weight[node] = Top_Weight[node];
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[node] += Top_Weight[neibor];
		}
		if (Node_Weight[node] > max_weight)
			max_weight = Node_Weight[node];
	}
	assert(max_weight<MAX_NODE*2);
	memset(weight_counter, 0, (max_weight + 1) * sizeof(int));

	for (node = 1; node <= NB_NODE; node++) {
		weight_counter[Node_Weight[node]]++;
	}
	j = 0;
	for (i = 0; i <= max_weight; i++) {
		k = weight_counter[i];
		weight_counter[i] = j;
		j += k;
	}

	for (node = 1; node <= NB_NODE; node++) {
		Candidate_Stack[t = weight_counter[Node_Weight[node]]++] = node;
		where[node] = t;
	}
	for (i = max_weight; i > 0; i--) {
		weight_counter[i] = weight_counter[i - 1];
	}
	weight_counter[0] = 0;

	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;
}

static void sort_by_enhanced_weight_degeneracy_ordering_0_0() {
	int i, j, k, node, neibor, *neibors, min = INT_MAX, min_idx;

	for (i = 1; i <= NB_NODE; i++) {
		Candidate_Stack[i - 1] = i;
	}
	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;

	for (node = 1; node <= NB_NODE; node++) {
		Node_Weight[node] = Top_Weight[node];
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[node] += Top_Weight[neibor];
		}
	}

	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		min = Node_Weight[Candidate_Stack[i]];
		min_idx = i;
		for (j = i + 1; j < ptr(Candidate_Stack) - 1; j++) {
			if (Node_Weight[Candidate_Stack[j]] < min) {
				min = Node_Weight[Candidate_Stack[j]];
				min_idx = j;
			}
//			else if (Node_Weight[Candidate_Stack[j]] == min
//					&& Top_Weight[Candidate_Stack[j]]
//							< Top_Weight[Candidate_Stack[min_idx]]) {
//				min_idx = j;
//			}
		}
		k = Candidate_Stack[i];
		Candidate_Stack[i] = Candidate_Stack[min_idx];
		Candidate_Stack[min_idx] = k;
		printf("%d ", Node_Weight[Candidate_Stack[i]]);

		neibors = Node_Neibors[Candidate_Stack[i]];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[neibor] -= Top_Weight[Candidate_Stack[i]];
		}
	}
	printf("\n");
}
static void sort_by_enhanced_weight_degeneracy_ordering_0_1() {
	int i, j, k, node, neibor, *neibors, min = INT_MAX, min_idx;

	for (i = 1; i <= NB_NODE; i++) {
		Candidate_Stack[i - 1] = i;
	}
	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;

	for (node = 1; node <= NB_NODE; node++) {
		Node_Weight[node] = Top_Weight[node];
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[node] += Top_Weight[neibor];
		}
	}

	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		min = Node_Weight[Candidate_Stack[i]];
		min_idx = i;
		for (j = i + 1; j < ptr(Candidate_Stack) - 1; j++) {
			if (Node_Weight[Candidate_Stack[j]] < min) {
				min = Node_Weight[Candidate_Stack[j]];
				min_idx = j;
			} else if (Node_Weight[Candidate_Stack[j]] == min
					&& Top_Weight[Candidate_Stack[j]]
							< Top_Weight[Candidate_Stack[min_idx]]) {
				min_idx = j;
			}
		}
		k = Candidate_Stack[i];
		Candidate_Stack[i] = Candidate_Stack[min_idx];
		Candidate_Stack[min_idx] = k;
		printf("%d ", Node_Weight[Candidate_Stack[i]]);

		neibors = Node_Neibors[Candidate_Stack[i]];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[neibor] -= Top_Weight[Candidate_Stack[i]];
		}
	}
	printf("\n");
}

static void check_enhanced_weight_degeneracy_ordering() {
	int i, j, node, *neibors, neibor, weight1, weight2;
	for (node = 1; node <= NB_NODE; node++) {
		Node_State[node] = ACTIVE;
		Node_Weight[node] = Top_Weight[node];
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[node] += Top_Weight[neibor];
		}
	}
	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		weight1 = Node_Weight[Candidate_Stack[i]];
		weight2 = INT_MAX;
		for (node = 1; node <= NB_NODE; node++) {
			if (Node_State[node] == ACTIVE && Node_Weight[node] < weight2)
				weight2 = Node_Weight[node];
		}
		assert(weight1 == weight2);
		neibors = Node_Neibors[Candidate_Stack[i]];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[neibor] -= Top_Weight[Candidate_Stack[i]];
		}
		Node_State[Candidate_Stack[i]] = PASSIVE;
	}
	for (node = 1; node <= NB_NODE; node++) {
		assert(Node_State[node]==PASSIVE);
	}
}
static int init_for_degeneracy(int *segment_counter, int *where) {
	int i, j, t, total_weight = 0;
	int node, neibor, *neibors, max_weight = 0;
	for (node = 1; node <= NB_NODE; node++) {
		total_weight += Top_Weight[node];
		Node_Weight[node] = Top_Weight[node];
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[node] += Top_Weight[neibor];
		}
		if (Node_Weight[node] > max_weight)
			max_weight = Node_Weight[node];
	}

	memset(segment_counter, 0, (max_weight + 1) * sizeof(int));

	for (node = 1; node <= NB_NODE; node++) {
		segment_counter[Node_Weight[node]]++;
	}

	j = 0;
	for (i = 0; i <= max_weight; i++) {
		t = segment_counter[i];
		segment_counter[i] = j;
		j += t;
	}

	for (node = 1; node <= NB_NODE; node++) {
		t = segment_counter[Node_Weight[node]]++;
		Candidate_Stack[t] = node;
		where[node] = t;
	}
	for (i = max_weight; i > 0; i--) {
		segment_counter[i] = segment_counter[i - 1];
	}
	segment_counter[0] = 0;

	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;

	return total_weight;
}

static int sort_by_weight_degeneracy_and_core_decomposion() {
	int *segment_counter, *where, *neibors, neibor, max_weight = 0, new_weight,
			total_weight = 0;
	int p1, i, node = NONE, t, j, head, head_node;
	int cur_core = 0, pre_weight, cur_weight;
	INIT_CLQ_SIZE = 0;
	MAX_SUBGRAPH_SIZE = 0;
	printf("I computing weight cores and degeneracy ordering...\n");

	where = Candidate_Stack + NB_NODE + 1;
	segment_counter = Vertex_UB + NB_NODE + 1;
	total_weight = init_for_degeneracy(segment_counter, where);

	p1 = 0;
	cur_core = Node_Weight[Candidate_Stack[p1]];
	K_CORE_G = cur_core;
	while (p1 < NB_NODE) {
		node = Candidate_Stack[p1];
		cur_weight = Node_Weight[node];

		if (cur_weight > cur_core) {
			cur_core = cur_weight;
			K_CORE_G = cur_core;
		}
		Vertex_UB[p1] = cur_core;

		if (p1 < NB_NODE - 1
				&& cur_weight == Node_Weight[Candidate_Stack[p1 + 1]]) {
			segment_counter[cur_weight] = p1 + 1;
		}

		if (cur_weight == total_weight) {

			INIT_CLQ_SIZE = 0;
			INIT_CLQ_WEIGHT = 0;

			for (i = p1; i < NB_NODE; i++) {
				MaxCLQ_Stack[INIT_CLQ_SIZE++] = Candidate_Stack[i];
				INIT_CLQ_WEIGHT += Top_Weight[Candidate_Stack[i]];
			}

			for (i = p1 + 1; i < NB_NODE; i++) {
				Vertex_UB[i] = cur_core;
			}

			printf("I The initial clique weight is %d, W_CORE_G is %d\n",
					INIT_CLQ_WEIGHT, K_CORE_G);
			break;
		}

		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if ((t = where[neibor]) > p1) {
				pre_weight = Node_Weight[neibor];
				Node_Weight[neibor] = Node_Weight[neibor] - Top_Weight[node];
				new_weight = Node_Weight[neibor];
				do {
					head = segment_counter[pre_weight];
					head_node = Candidate_Stack[head];

					Candidate_Stack[head] = neibor;
					where[neibor] = head;

					Candidate_Stack[t] = head_node;
					where[head_node] = t;

					segment_counter[pre_weight] = head + 1;

					pre_weight = Node_Weight[Candidate_Stack[head - 1]];

					t = head;

				} while (head > p1 + 1 && new_weight < pre_weight);

				if (head == p1 + 1
						|| new_weight
								> Node_Weight[Candidate_Stack[head - 1]]) {
					segment_counter[new_weight] = head;
				}
			}
		}
		total_weight -= Top_Weight[node];
		p1++;
	}
	if (INIT_CLQ_WEIGHT == K_CORE_G) {
		MAX_CLQ_SIZE = INIT_CLQ_SIZE;
		MAX_CLQ_WEIGHT = INIT_CLQ_WEIGHT;
		INIT_TIME = get_utime() - READ_TIME;
		SEARCH_TIME = 0;
		printf("I Finding the optimal solution in initial phase!\n");
		printf("I The init time is %4.2lf \n", INIT_TIME);

		return TRUE;
	} else
		return FALSE;

}

static void sort_by_enhanced_weight_degeneracy_ordering() {
	int *segment_counter, *where, *neibors, neibor, max_weight = 0, new_weight,
			total_weight = 0;
	int p1, i, node = NONE, t, j, head, head_node;
	int core_weight = 0, pre_weight, cur_weight;
	INIT_CLQ_SIZE = 0;
	MAX_SUBGRAPH_SIZE = 0;
	printf("I computing initial weight degeneracy ordering...\n");

	where = Candidate_Stack + NB_NODE + 1;
	segment_counter = Vertex_UB + NB_NODE + 1;
	total_weight = init_for_degeneracy(segment_counter, where);
	p1 = 0;
	//core_weight = Node_Weight[Candidate_Stack[p1]];
	while (p1 < NB_NODE) {
		node = Candidate_Stack[p1];
		cur_weight = Node_Weight[node];
		Vertex_UB[p1] = cur_weight;
		if (p1 < NB_NODE - 1
				&& cur_weight == Node_Weight[Candidate_Stack[p1 + 1]]) {
			segment_counter[cur_weight] = p1 + 1;
		}

		if (cur_weight == total_weight) {
			INIT_CLQ_SIZE = NB_NODE - p1;
//			printf("I initial clique is %d\n", INIT_CLQ_SIZE);
//			printf("I maxcore number is %d\n", K_CORE_G);

			for (i = p1 + 1; i < NB_NODE; i++) {
				Vertex_UB[i] = total_weight
						- Top_Weight[Candidate_Stack[i - 1]];
				total_weight = total_weight
						- Top_Weight[Candidate_Stack[i - 1]];
			}
			return;
		}

		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if ((t = where[neibor]) > p1) {
				pre_weight = Node_Weight[neibor];
				Node_Weight[neibor] = Node_Weight[neibor] - Top_Weight[node];
				new_weight = Node_Weight[neibor];
				do {
					head = segment_counter[pre_weight];
					head_node = Candidate_Stack[head];

					Candidate_Stack[head] = neibor;
					where[neibor] = head;

					Candidate_Stack[t] = head_node;
					where[head_node] = t;

					segment_counter[pre_weight] = head + 1;

					pre_weight = Node_Weight[Candidate_Stack[head - 1]];

					t = head;

				} while (head > p1 + 1 && new_weight < pre_weight);

				if (head == p1 + 1
						|| new_weight
								> Node_Weight[Candidate_Stack[head - 1]]) {
					segment_counter[new_weight] = head;
				}
			}
		}
		total_weight -= Top_Weight[node];
		p1++;
	}

//	qsort(Candidate_Stack, NB_NODE, sizeof(int), int_cmp);
//	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
//		assert(Candidate_Stack[i] == NB_NODE - i);
//	}
}
static void sort_by_enhanced_weight_degeneracy_ordering_2() {
	int *segment_counter, *where, *neibors, neibor, max_weight = 0, new_weight,
			total_weight = 0;
	int p1, i, node = NONE, t, j, head, head_node;
	int core_weight = 0, pre_weight, cur_weight, self_weight;
	INIT_CLQ_SIZE = 0;
	MAX_SUBGRAPH_SIZE = 0;
//printf("I computing initial enhanced weight degeneracy ordering...\n");

	where = Candidate_Stack + NB_NODE + 1;
	segment_counter = Vertex_UB + NB_NODE + 1;

	for (node = 1; node <= NB_NODE; node++) {
		total_weight += Top_Weight[node];
		Node_Weight[node] = Top_Weight[node];
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			Node_Weight[node] += Top_Weight[neibor];
		}
		if (Node_Weight[node] > max_weight)
			max_weight = Node_Weight[node];
	}

//assert(NB_NODE + 1 + max_weight<2*MAX_NODE);
	memset(segment_counter, 0, (max_weight + 1) * sizeof(int));

	for (node = 1; node <= NB_NODE; node++) {
		segment_counter[Node_Weight[node]]++;
	}

	j = 0;
	for (i = 0; i <= max_weight; i++) {
		head_node = segment_counter[i];
		segment_counter[i] = j;
		j += head_node;
	}

	for (node = 1; node <= NB_NODE; node++) {
		t = segment_counter[Node_Weight[node]]++;
		Candidate_Stack[t] = node;
		where[node] = t;
	}
	for (i = max_weight; i > 0; i--) {
		segment_counter[i] = segment_counter[i - 1];
	}
	segment_counter[0] = 0;

	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;

	p1 = 0;
//core_weight = Node_Weight[Candidate_Stack[p1]];
	while (p1 < NB_NODE) {
		node = Candidate_Stack[p1];
		cur_weight = Node_Weight[node];
		self_weight = Top_Weight[node];
		i = p1;
		t = p1;
		while (i < NB_NODE && Node_Weight[Candidate_Stack[i]] == cur_weight) {
			if (Top_Weight[Candidate_Stack[i]] < self_weight) {
				t = i;
				self_weight = Top_Weight[Candidate_Stack[i]];
			}
			i++;
		}
		if (t != p1) {
			assert(
					t < NB_NODE
							&& Node_Weight[Candidate_Stack[t]]
									== Node_Weight[Candidate_Stack[p1]]);
			head_node = Candidate_Stack[t];
			Candidate_Stack[t] = node;
			Candidate_Stack[p1] = head_node;
			node = head_node;
		}
		printf("%d ", cur_weight);
//		printf("node= %d weight=%d\n", node, Node_Weight[node]);
//		if (pre_weight > core_weight) {
//			core_weight = pre_weight;
//			K_CORE_G = core_weight;
//		}
		//CORE_NO[p1] = cur_weight;

		if (p1 < NB_NODE - 1
				&& cur_weight == Node_Weight[Candidate_Stack[p1 + 1]]) {
			segment_counter[cur_weight] = p1 + 1;
		}

		if (cur_weight == total_weight) {
			INIT_CLQ_SIZE = NB_NODE - p1;
//			printf("I initial clique is %d\n", INIT_CLQ_SIZE);
//			printf("I maxcore number is %d\n", K_CORE_G);

			for (i = p1 + 1; i < NB_NODE; i++) {
				printf("%d ",
						total_weight - Top_Weight[Candidate_Stack[i - 1]]);
				total_weight = total_weight
						- Top_Weight[Candidate_Stack[i - 1]];
			}
			printf("\n");
			return;
		}

		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if ((t = where[neibor]) > p1) {
				pre_weight = Node_Weight[neibor];
				Node_Weight[neibor] = Node_Weight[neibor] - Top_Weight[node];
				new_weight = Node_Weight[neibor];
				do {
					head = segment_counter[pre_weight];
					head_node = Candidate_Stack[head];

					Candidate_Stack[head] = neibor;
					where[neibor] = head;

					Candidate_Stack[t] = head_node;
					where[head_node] = t;

					segment_counter[pre_weight] = head + 1;

					pre_weight = Node_Weight[Candidate_Stack[head - 1]];

					t = head;

				} while (head > p1 + 1 && new_weight < pre_weight);

				if (head == p1 + 1
						|| new_weight
								> Node_Weight[Candidate_Stack[head - 1]]) {
					segment_counter[new_weight] = head;
				}
			}
		}
		total_weight -= Top_Weight[node];
		p1++;
	}
}
static int sort_by_degeneracy_ordering_bak() {
	int *degree_counter, *where;
	int p1, i, node = NONE, neibor, *neibors, t, j, h, k;
	int cur_degree = 0;
	INIT_CLQ_SIZE = 0;
	printf("I computing initial vertex degeneracy ordering...\n");

	where = Candidate_Stack + NB_NODE + 1;
	degree_counter = Vertex_UB + NB_NODE + 1;
	memset(degree_counter, 0, (Max_Degree + 1) * sizeof(int));

	for (node = 1; node <= NB_NODE; node++) {
		degree_counter[Node_Degree[node]]++;
	}
	j = 0;
	for (i = 0; i <= Max_Degree; i++) {
		k = degree_counter[i];
		degree_counter[i] = j;
		j += k;
	}

	for (node = 1; node <= NB_NODE; node++) {
		Candidate_Stack[t = degree_counter[Node_Degree[node]]++] = node;
		where[node] = t;
	}
	for (i = Max_Degree; i > 0; i--) {
		degree_counter[i] = degree_counter[i - 1];
	}
	degree_counter[0] = 0;

	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;

	p1 = 0;
	cur_degree = Node_Degree[Candidate_Stack[p1]];
	while (p1 < NB_NODE) {
		node = Candidate_Stack[p1];

		if (Node_Degree[node] > cur_degree)
			cur_degree = Node_Degree[node];
		Vertex_UB[p1] = cur_degree;

		if (cur_degree > K_CORE_G)
			K_CORE_G = cur_degree;

		if (p1 < NB_NODE - 1
				&& Node_Degree[node] == Node_Degree[Candidate_Stack[p1 + 1]]) {
			degree_counter[Node_Degree[node]] = p1 + 1;
		}
		if (Node_Degree[node] > MAX_SUBGRAPH_SIZE)
			MAX_SUBGRAPH_SIZE = Node_Degree[node];

		if (Node_Degree[node] == NB_NODE - p1 - 1) {
			INIT_CLQ_SIZE = NB_NODE - p1;
			printf("I initial clique is %d\n", INIT_CLQ_SIZE);
			printf("I maxcore number is %d\n", K_CORE_G);
			MaxCLQ_Stack = (int *) malloc((K_CORE_G + 2) * sizeof(int));
			Clique_Stack = (int *) malloc((K_CORE_G + 2) * sizeof(int));
			memcpy(MaxCLQ_Stack, Candidate_Stack + p1,
					INIT_CLQ_SIZE * sizeof(int));
			for (i = p1 + 1; i < NB_NODE; i++)
				Vertex_UB[i] = cur_degree;
			break;
		}

		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (where[neibor] > p1) {
				t = where[neibor];
				h = degree_counter[Node_Degree[neibor]];

				k = Candidate_Stack[h];

				Candidate_Stack[h] = neibor;
				where[neibor] = h;

				Candidate_Stack[t] = k;
				where[k] = t;

				degree_counter[Node_Degree[neibor]]++;

				Node_Degree[neibor]--;
				if (Node_Degree[neibor]
						!= Node_Degree[Candidate_Stack[h - 1]]) {
					degree_counter[Node_Degree[neibor]] = h;
				}
			}
		}
		p1++;
	}

	if (MAX_SUBGRAPH_SIZE + 1 == INIT_CLQ_SIZE) {
		MAX_CLQ_SIZE = INIT_CLQ_SIZE;
		printf("I find the maximum clique in initial phase!\n");
		return TRUE;
	} else {
		return FALSE;
	}
}

static int re_number_adj(int node) {
	int i, k, j, *neibors, *saved_neibors, neibor, one_neibor, count,
			iset_weight, iset_second_weight, inc1 = 0, inc2 = 0;

	for (i = 0; i < iSET_COUNT - 1; i++) {
		if (iSET_Tested[i] == FALSE) {
			count = 0;
			neibors = iSET[i];
			one_neibor = NONE;
			iset_second_weight = 0;
			iset_weight = iSET_Weight[i];
			for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
				if (is_adjacent(node, neibor) == TRUE) {
					if (one_neibor == NONE) {
						one_neibor = neibor;
						saved_neibors = neibors;
					} else if (one_neibor != NONE) {
						break;
					}
				}
				if (Top_Weight[neibor] == iset_weight)
					count++;
				else if (Top_Weight[neibor] > iset_second_weight)
					iset_second_weight = Top_Weight[neibor];
			}

			if (one_neibor != NONE && neibor == NONE) {

				for (k = i + 1; k < iSET_COUNT; k++) {
					neibors = iSET[k];
					for (neibor = *neibors; neibor != NONE; neibor =
							*(++neibors)) {
						if (one_neibor > neibor) {
							if (is_adjacent(one_neibor, neibor) == TRUE)
								break;
						} else {
							if (is_adjacent(neibor, one_neibor) == TRUE)
								break;
						}
					}
					if (neibor == NONE) {
						inc1 = 0, inc2 = 0;
						if (Top_Weight[node] >= iset_weight) {
							inc1 = Top_Weight[node] - iset_weight;
						} else if (count == 1
								&& Top_Weight[one_neibor] == iset_weight) {
							if (Top_Weight[node] > iset_second_weight)
								inc1 = Top_Weight[node] - iset_weight;
							else
								inc1 = iset_second_weight - iset_weight;
						}

						if (Top_Weight[one_neibor] >= iSET_Weight[k]) {
							inc2 = Top_Weight[one_neibor] - iSET_Weight[k];
						}
						if (inc1 + inc2 + iSET_TOTAL_WEIGHT
								<= MAX_ISET_WEIGHT) {

							*(saved_neibors) = node;

							iSET[k][iSET_Size[k]++] = one_neibor;
							iSET[k][iSET_Size[k]] = NONE;

							iSET_Weight[i] += inc1;
							iSET_Weight[k] += inc2;

							iSET_TOTAL_WEIGHT += inc1 + inc2;

							return TRUE;
						}
					}
				}
			}
		}
	}
	return FALSE;
}

static int re_number_no_keep_ordering(int node) {
	int i, k, *neibors, *saved_neibors, neibor, one_neibor, temp;
	unsigned char *adj_list1 = iMatrix(node), *adj_list2;
	for (i = 0; i < iSET_COUNT - 1; i++) {
		neibors = iSET[i];
		one_neibor = NONE;
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (Matrix(adj_list1,neibor) > 0) {
				if (one_neibor == NONE) {
					one_neibor = neibor;
					saved_neibors = neibors;
				} else if (one_neibor != NONE) {
					break;
				}
			}
		}
		assert(one_neibor != NONE);
		if (one_neibor == NONE) {
			iSET[i][iSET_Size[i]] = node;
			iSET_Size[i]++;
			iSET[i][iSET_Size[i]] = NONE;
			return TRUE;
		}
		if (neibor == NONE) {
			adj_list2 = iMatrix(one_neibor);
			for (k = i + 1; k < iSET_COUNT; k++) {
				neibors = iSET[k];
				for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
					if (Matrix(adj_list2,neibor) > 0)
						break;
				}
				if (neibor == NONE
						&& (Node_Weight[one_neibor] <= iSET_Weight[k]
								|| (Node_Weight[one_neibor] - iSET_Weight[k])
										+ iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT)) {
					*(saved_neibors) = node;
					//iSET_Index[node] = i;
					if (Node_Weight[node] > iSET_Weight[i]) {
						iSET_TOTAL_WEIGHT += Node_Weight[node] - iSET_Weight[i];
						iSET_Weight[i] = Node_Weight[node];
					}

					iSET[k][iSET_Size[k]] = one_neibor;
					iSET_Size[k]++;
					iSET[k][iSET_Size[k]] = NONE;
					//iSET_Index[one_neibor] = k;
					if (Node_Weight[one_neibor] > iSET_Weight[k]) {
						iSET_TOTAL_WEIGHT += Node_Weight[one_neibor]
								- iSET_Weight[k];
						iSET_Weight[k] = Node_Weight[one_neibor];
					}
					return TRUE;
				}

			}
		}
	}
	return FALSE;
}
static int SWAP = 0;
static int re_number(int node) {
	int i, k, j, *neibors, *saved_neibors, neibor, one_neibor, count,
			iset_weight, iset_second_weight, inc1 = 0, inc2 = 0;
	int min_w = NONE, min_iset, *min_ptr;
	unsigned char *adj_list1 = iMatrix(node), *adj_list2;
	for (i = 0; i < iSET_COUNT - 1; i++) {
		if (iSET_Tested[i] == FALSE) {
			count = 0;
			neibors = iSET[i];
			one_neibor = NONE;
			iset_second_weight = 0;
			iset_weight = iSET_Weight[i];
			for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
				if (Matrix(adj_list1,neibor) > 0) {
					if (one_neibor == NONE) {
						one_neibor = neibor;
						saved_neibors = neibors;
					} else if (one_neibor != NONE) {
						break;
					}
				}
				if (Node_Weight[neibor] == iset_weight)
					count++;
				else if (Node_Weight[neibor] > iset_second_weight)
					iset_second_weight = Node_Weight[neibor];
			}

			if (one_neibor != NONE && neibor == NONE) {
				adj_list2 = iMatrix(one_neibor);

				for (k = i + 1; k < iSET_COUNT; k++) {
					neibors = iSET[k];
					for (neibor = *neibors; neibor != NONE; neibor =
							*(++neibors)) {
						if (Matrix(adj_list2,neibor) > 0)
							break;
					}
					if (neibor == NONE) {
						inc1 = 0, inc2 = 0;
						if (Node_Weight[node] >= iset_weight) {
							inc1 = Node_Weight[node] - iset_weight;
						} else if (count == 1
								&& Node_Weight[one_neibor] == iset_weight) {
							if (Node_Weight[node] > iset_second_weight)
								inc1 = Node_Weight[node] - iset_weight;
							else
								inc1 = iset_second_weight - iset_weight;
						}

						if (Node_Weight[one_neibor] >= iSET_Weight[k]) {
							inc2 = Node_Weight[one_neibor] - iSET_Weight[k];
						}
						if (inc1 + inc2 + iSET_TOTAL_WEIGHT
								<= MAX_ISET_WEIGHT) {

							*(saved_neibors) = node;
							//iSET_Index[node] = i;

							iSET[k][iSET_Size[k]++] = one_neibor;
							iSET[k][iSET_Size[k]] = NONE;
							//iSET_Index[one_neibor] = k;

							iSET_Weight[i] += inc1;
							iSET_Weight[k] += inc2;

							iSET_TOTAL_WEIGHT += inc1 + inc2;

							return TRUE;
						}
					}
				}
//				if (Node_Weight[node] > Node_Weight[one_neibor]) {
//					if (min_w == NONE || Node_Weight[one_neibor] < min_w) {
//						min_w = Node_Weight[one_neibor];
//						min_iset = i;
//						min_ptr = saved_neibors;
//					}
//				}
			}
		}
	}
//	if (min_w != NONE) {
//		one_neibor = *min_ptr;
//		*min_ptr = node;
//		if (Node_Weight[node] > iSET_Weight[min_iset]) {
//			iSET_TOTAL_WEIGHT += Node_Weight[node] - iSET_Weight[min_iset];
//			iSET_Weight[min_iset] = Node_Weight[node];
//			//assert(iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT);
//		}
//		i = ptr(Candidate_Stack) - 2;
//		while ((node = Candidate_Stack[i]) != one_neibor)
//			i--;
//		Candidate_Stack[i] = -node;
//		SWAP++;
//		return TRUE;
//	}
	return FALSE;
}

static int addIntoIsetTomitaBis_adj(int node) {

	int j, *current_set, iset_node;

	for (j = 0; j < iSET_COUNT; j++) {
		if (Top_Weight[node] - iSET_Weight[j] + iSET_TOTAL_WEIGHT
				<= MAX_ISET_WEIGHT) {
			current_set = iSET[j];
			for (iset_node = *current_set; iset_node != NONE; iset_node =
					*(++current_set)) {
				if (is_adjacent(node, iset_node) == TRUE)
					break;
			}
			if (iset_node == NONE) {
				iSET_Size[j]++;
				*(current_set) = node;
				*(++current_set) = NONE;
				if (Top_Weight[node] > iSET_Weight[j]) {
					iSET_TOTAL_WEIGHT += Top_Weight[node] - iSET_Weight[j];
					iSET_Weight[j] = Top_Weight[node];
				}
				return TRUE;
			}
		} else {
			iSET_Tested[j] = TRUE;
		}
	}
	if (iSET_TOTAL_WEIGHT + Top_Weight[node] <= MAX_ISET_WEIGHT) {
		iSET_Size[j] = 1;
		iSET[j][0] = node;
		iSET[j][1] = NONE;
		iSET_Weight[j] = Top_Weight[node];
		iSET_TOTAL_WEIGHT += iSET_Weight[j];
		iSET_COUNT++;
		return TRUE;
	} else {
		return FALSE;
	}
}

static int addIntoIsetTomitaBis(int node) {
	int j, *current_set, iset_node;
	unsigned char *adj_list = iMatrix(node);

	for (j = 0; j < iSET_COUNT; j++) {
		if (Node_Weight[node] - iSET_Weight[j] + iSET_TOTAL_WEIGHT
				<= MAX_ISET_WEIGHT) {
			current_set = iSET[j];
			for (iset_node = *current_set; iset_node != NONE; iset_node =
					*(++current_set)) {
				if (Matrix(adj_list,iset_node) > 0)
					break;
			}
			if (iset_node == NONE) {
				iSET_Size[j]++;
				*(current_set) = node;
				*(++current_set) = NONE;
				if (Node_Weight[node] > iSET_Weight[j]) {
					iSET_TOTAL_WEIGHT += Node_Weight[node] - iSET_Weight[j];
					iSET_Weight[j] = Node_Weight[node];
				}
				return TRUE;
			}
		} else {
			iSET_Tested[j] = TRUE;
		}
	}
	if (iSET_TOTAL_WEIGHT + Node_Weight[node] <= MAX_ISET_WEIGHT) {
		iSET_Size[j] = 1;
		//iSET_Topk[j] = 1;
		iSET[j][0] = node;
		iSET[j][1] = NONE;
		//iSET_Index[node] = j;
		iSET_Weight[j] = Node_Weight[node];
		iSET_TOTAL_WEIGHT += iSET_Weight[j];
		iSET_COUNT++;
		return TRUE;
	} else {
		return FALSE;
	}
}

//static int cut_by_iset_less_vertices() {
//	int i = ptr(Candidate_Stack) - 2, node;
//	iSET_COUNT = 0;
//	iSET_TOTAL_WEIGHT = 0;
//	MAX_ISET_WEIGHT = MAX_CLQ_WEIGHT - CUR_CLQ_WEIGHT - CUR_NODE_WEIGHT;
//	for (node = Candidate_Stack[i]; node != DELIMITER; node =
//			Candidate_Stack[--i]) {
//		if (addIntoIsetTomitaBis_adj(node) == FALSE
//				&& re_number_adj(node) == FALSE) {
//			return FALSE;
//		}
//	}
//	return TRUE;
//}

static void is_iset(int idx) {
	int iset_node, *current_set, iset_node2, *current_set2;
	current_set = iSET[idx];
	for (iset_node = *current_set; iset_node != NONE; iset_node =
			*(++current_set)) {
		current_set2 = current_set + 1;
		for (iset_node2 = *current_set2; iset_node2 != NONE; iset_node2 =
				*(++current_set2)) {
			assert(Matrix(iMatrix(iset_node),iset_node2) == 0);
		}
	}

}

static void check_iset1() {
	int i, count, topk, iset_node, *current_set, weight = 0, iset_weight;
//assert(iSET_COUNT > 0);
	for (i = 0; i < iSET_COUNT; i++) {
		is_iset(i);
		count = 0;
		iset_weight = 0;
		current_set = iSET[i];
		for (iset_node = *current_set; iset_node != NONE; iset_node =
				*(++current_set)) {
			//assert(iSET_Index[iset_node] == i);
			count++;
			if (Node_Weight[iset_node] > iset_weight) {
				iset_weight = Node_Weight[iset_node];
				topk = 1;
			} else if (Node_Weight[iset_node] == iset_weight)
				topk++;
		}
		assert(count == iSET_Size[i]);
		assert(topk >= 1);
		//assert(topk == iSET_Topk[i]);
		assert(iSET_Weight[i] == iset_weight && iset_weight > 0);
		weight += iSET_Weight[i];
	}
	assert(weight == iSET_TOTAL_WEIGHT);
	if (MAX_ISET_WEIGHT >= 0)
		assert(iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT);
}

static void check_iset2(int reduced_weight, int reduced_iset_count) {
	int i, count, topk, iset_node, *current_set, weight = 0, iset_weight;
//assert(iSET_COUNT > 0);
	for (i = 0; i < iSET_COUNT; i++) {
		is_iset(i);
		count = 0;
		topk = 0;
		iset_weight = 0;
		current_set = iSET[i];
		for (iset_node = *current_set; iset_node != NONE; iset_node =
				*(++current_set)) {
			//assert(iSET_Index[iset_node] == i);
			assert(Node_Weight[iset_node] > 0);
			count++;
			if (Node_Weight[iset_node] > iset_weight) {
				iset_weight = Node_Weight[iset_node];
				topk = 1;
			} else if (Node_Weight[iset_node] == iset_weight)
				topk++;
		}
		assert(count == iSET_Size[i]);
		if (count > 0) {
			assert(topk >= 1);
		} else {
			assert(topk == 0);
			assert(iSET_Weight[i] == 0);
		}
		//assert(topk == iSET_Topk[i]);
		assert(iSET_Weight[i] == iset_weight);
		weight += iSET_Weight[i];
	}
	assert(reduced_iset_count * reduced_weight + weight == iSET_TOTAL_WEIGHT);
//iSET_TOTAL_WEIGHT = weight;
}

static void build_structures();
static void check_build_structures();

static int cut_by_iset_less_vertices() {
	int i = ptr(Candidate_Stack) - 2, j, node;
	iSET_COUNT = 0;
	iSET_TOTAL_WEIGHT = 0;
	MAX_ISET_WEIGHT = MAX_CLQ_WEIGHT - CUR_CLQ_WEIGHT - CUR_NODE_WEIGHT;
	if (MAX_ISET_WEIGHT <= 0)
		return FALSE;
	for (node = Candidate_Stack[i]; node != DELIMITER; node =
			Candidate_Stack[--i]) {
		for (j = 0; i < iSET_COUNT; j++)
			iSET_Tested[j] = FALSE;
		if (addIntoIsetTomitaBis_adj(node) == FALSE
				&& re_number_adj(node) == FALSE) {
			return FALSE;
		}
	}
	return TRUE;
}

static int cut_by_iset_last_renumber() {
	int i = ptr(Candidate_Stack) - 2, j, node;
	LAST_IN = INT_MAX;
	FIRST_INDEX = NONE;
	iSET_COUNT = 0;
	iSET_TOTAL_WEIGHT = 0;
	MAX_ISET_WEIGHT = MAX_CLQ_WEIGHT - CUR_CLQ_WEIGHT - CUR_NODE_WEIGHT;

	if (MAX_ISET_WEIGHT <= 0) {
		for (node = Candidate_Stack[i]; node != DELIMITER; node =
				Candidate_Stack[--i]) {
			Candidate_Stack[i] = -node;
		}
		Branching_Point = ptr(Candidate_Stack) - 1;
		return FALSE;
	}
	for (node = Candidate_Stack[i]; node != DELIMITER; node =
			Candidate_Stack[--i]) {
		for (j = 0; i < iSET_COUNT; j++)
			iSET_Tested[j] = FALSE;

		if (addIntoIsetTomitaBis(node) == FALSE && re_number(node) == FALSE) {
			Candidate_Stack[i] = -node;
		} else {
			LAST_IN = i;
		}
	}

	i = ptr(Candidate_Stack) - 2;
	for (node = Candidate_Stack[i]; node != DELIMITER; node =
			Candidate_Stack[--i]) {
		if (node < 0) {
			FIRST_INDEX = i;
			break;
		}
	}

	if (FIRST_INDEX == NONE) {
		cut_iset++;
		Vertex_UB[CURSOR]=iSET_TOTAL_WEIGHT+CUR_NODE_WEIGHT;
		return TRUE;
	} else {
#ifndef MaxSAT
		for (node = Candidate_Stack[i = FIRST_INDEX]; node != DELIMITER; node =
				Candidate_Stack[--i]) {
			if (node < 0 && i > LAST_IN) {
				Vertex_UB[i] = UPPER_WEIGHT_BOUND - CUR_CLQ_WEIGHT
						- CUR_NODE_WEIGHT;
			}
		}
#endif
		Branching_Point = FIRST_INDEX + 1;
		return FALSE;
	}
}

#define assign_node(node, value, reason) {\
	Node_State[node] = value;\
	Node_Reason[node] = reason;\
	push(node, FIXED_NODE_STACK);\
}
static int fix_unit_iset(int fix_iset);
static int fix_b_node(int b_node) {
	int i, node, *nodes, iset;
	unsigned char *adj_list;
	ptr(NEW_UNIT_STACK) = 0;
	adj_list = iMatrix(b_node);

	for (i = 0; i < iSET_COUNT; i++) {
		if (IS_STAT(i) == ACTIVE) {
			nodes = IS_NODES(i);
			for (node = *nodes; node != 0; node = *(nodes += 3)) {
				if (node > 0 && Matrix(adj_list,node) == FALSE) {
					*nodes = -node;
					*(nodes + 2) = NO_REASON;
					IS_SIZE(i)--;

					if (*(nodes + 1) == IS_WEIT(i)) {
						IS_TOPK(i)--;
						if (IS_TOPK(i) == 0) {
							return i;
						} else if (IS_TOPK(i) == 1) {
							push(i, TOP_UNIT_STACK);
						}
					}

					if (IS_SIZE(i) == 1)
						push(i, NEW_UNIT_STACK);
				}
			}
		}
	}
	for (i = 0; i < ptr(NEW_UNIT_STACK); i++) {
		iset = NEW_UNIT_STACK[i];
		if (IS_STAT(iset) == ACTIVE && (iset = fix_unit_iset(iset)) != NONE) {
			return iset;
		}
	}

	return NONE;
}

static int fix_node_in_iset(int *fix_node, int fix_iset) {
	int i, node, *nodes;
	unsigned char *adj_list;
	*(fix_node + 2) = fix_iset;
	IS_STAT(fix_iset) = PASSIVE;

	adj_list = iMatrix(*(fix_node));
	for (i = 0; i < iSET_COUNT; i++) {
		if (IS_STAT(i) == ACTIVE) {
			nodes = IS_NODES(i);
			for (node = *nodes; node != 0; node = *(nodes += 3)) {
				if (node > 0 && Matrix(adj_list,node) == FALSE) {
					*nodes = -node;
					*(nodes + 2) = fix_iset;
					IS_SIZE(i)--;

					if (*(nodes + 1) == IS_WEIT(i)) {
						IS_TOPK(i)--;
						if (IS_TOPK(i) == 0) {
							return i;
						} else if (IS_TOPK(i) == 1) {
							push(i, TOP_UNIT_STACK);
						}
					}

					if (IS_SIZE(i) == 1)
						push(i, NEW_UNIT_STACK);
				}
			}
		}
	}

	return NONE;
}

#define fix_node(node,iset) ((node > NB_NODE)? fix_newNode_for_iset(node, iset):fix_oldNode_for_iset(node, iset))

static int fix_unit_iset(int fix_iset) {
	int node, *nodes = IS_NODES(fix_iset);
	for (node = *(nodes); node != 0; node = *(nodes += 3)) {
		if (node > 0) {
			return fix_node_in_iset(nodes, fix_iset);
		}
	}
	nodes = IS_NODES(fix_iset);
	for (node = *(nodes); node != 0; node = *(nodes += 3)) {
		printf("is_state=%d,iset=%d,size=%d,topk=%d,node=%d\n",
				IS_STAT(fix_iset), fix_iset, IS_SIZE(fix_iset),
				IS_TOPK(fix_iset), node);
	}
	printf("error in fix_node_iset\n");
	printf("iSET COUNT=%d\n", iSET_COUNT);
	//print_all_iset();
	exit(0);
}

//static int fix_node_iset(int fix_iset) {
//	int fix_node, *nodes = iSET[fix_iset];
//	for (fix_node = *(nodes); fix_node != NONE; fix_node = *(++nodes)) {
//		if (Node_State[fix_node] == ACTIVE) {
//			return fix_oldNode_for_iset(fix_node, fix_iset);
////			if (fix_node > MAX_VERTEX_NO)
////				return fix_newNode_for_iset(fix_node, fix_iset);
////			else
////				return fix_oldNode_for_iset(fix_node, fix_iset);
//		}
//	}
//	nodes = iSET[fix_iset];
//	for (fix_node = *(nodes); fix_node != NONE; fix_node = *(++nodes)) {
//		printf("iset=%d,node=%d,active=%d\n", fix_iset, fix_node,
//				Node_State[fix_node]);
//	}
//	printf("error in fix_node_iset\n");
//	printf("iSET COUNT=%d\n", iSET_COUNT);
////print_all_iset();
//	exit(0);
//}

static int new_unit_iset_process() {
	int i = 0, j = 0, iset_idx, empty_iset;
	ptr(NEW_UNIT_STACK) = 0;
	for (i = 0; i < ptr(UNIT_STACK); i++) {
		iset_idx = UNIT_STACK[i];
		if (IS_STAT(iset_idx) == ACTIVE && IS_SIZE(iset_idx) == 1) {
			if ((empty_iset = fix_unit_iset(iset_idx)) > NONE) {
				return empty_iset;
			}
		}
	}
	return NONE;
}

static int unit_iset_process() {
	int i = 0, j = 0, iset_idx, empty_iset;
	for (i = 0; i < ptr(UNIT_STACK); i++) {
		iset_idx = UNIT_STACK[i];
		if (IS_STAT(iset_idx) == ACTIVE) {
			assert(IS_SIZE(iset_idx) == 1);
			ptr(NEW_UNIT_STACK) = 0;
			if ((empty_iset = fix_unit_iset(iset_idx)) > NONE) {
				return empty_iset;
			} else {
				for (j = 0; j < ptr(NEW_UNIT_STACK); j++) {
					iset_idx = NEW_UNIT_STACK[j];
					if (IS_STAT(iset_idx) == ACTIVE) {
						assert(IS_SIZE(iset_idx) == 1);
						if ((empty_iset = fix_unit_iset(iset_idx)) > NONE)
							return empty_iset;
					}
				}
			}
		}
	}
	ptr(NEW_UNIT_STACK) = 0;
	return NONE;
}

static int top_unit_iset_process() {
	int i = 0, j = 0, iset_idx, empty_iset;
	for (i = 0; i < ptr(TOP_UNIT_STACK); i++) {
		iset_idx = TOP_UNIT_STACK[i];
		if (IS_STAT(iset_idx) == ACTIVE) {
			assert(IS_TOPK(iset_idx) == 1);
			assert(IS_SIZE(iset_idx)>1);
			ptr(NEW_UNIT_STACK) = 0;
			if ((empty_iset = fix_unit_iset(iset_idx)) > NONE) {
				return empty_iset;
			} else {
				for (j = 0; j < ptr(NEW_UNIT_STACK); j++) {
					iset_idx = NEW_UNIT_STACK[j];
					if (IS_STAT(iset_idx) == ACTIVE) {
						assert(IS_SIZE(iset_idx) == 1);
						if ((empty_iset = fix_unit_iset(iset_idx)) > NONE)
							return empty_iset;
					}
				}
			}
		}
	}
	ptr(NEW_UNIT_STACK) = 0;
	return NONE;
}

static int unit_iset_process_used_first() {
	int j, iset, iset_start = 0, used_iset_start = 0, my_iset;
	do {
		for (j = used_iset_start; j < ptr(NEW_UNIT_STACK); j++) {
			iset = NEW_UNIT_STACK[j];
			if (IS_STAT(iset) == ACTIVE && IS_USED(iset) == TRUE)
				if ((my_iset = fix_unit_iset(iset)) != NONE)
					return my_iset;
		}
		used_iset_start = j;
		for (j = iset_start; j < ptr(NEW_UNIT_STACK); j++) {
			iset = NEW_UNIT_STACK[j];
			if (IS_STAT(iset) == ACTIVE) {
				if ((my_iset = fix_unit_iset(iset)) != NONE)
					return my_iset;
				iset_start = j + 1;
				break;
			}
		}
	} while (j < ptr(NEW_UNIT_STACK));
	return NONE;
}

static int NB_TOPK = 0;
static void TEST_TOPK_EMPTY_ISET(int iset_idx) {
	int count = 0, node, *nodes;
	nodes = iSET[iset_idx];
	for (node = *nodes; node != NONE; node = *(++nodes)) {
		count++;
	}

	qsort(iSET[iset_idx], count, sizeof(int), weight_desc);
	assert(Node_Weight[iSET[iset_idx][0]] == iSET_Weight[iset_idx]);
	/*TEST*/
	nodes = iSET[iset_idx];
	for (node = *nodes; node != NONE; node = *(++nodes)) {
		if (*(nodes + 1) != NONE) {
			assert(Node_Weight[node] >= Node_Weight[*(nodes + 1)]);
		}
		if (Node_Weight[node] == iSET_Weight[iset_idx]) {
			assert(Node_State[node]==P_FALSE);
		}
	}
	NB_TOPK++;
}

static void reduce_iset(int iset_idx, int delta) {
	int size = 0, topk = 0, weight = 0, _new_weight = 0;
	int node, *nodes = IS_NODES(iset_idx), *fill;
	fill = nodes;
	for (node = *nodes; node != 0; node = *(nodes += 3)) {
		if (*(nodes + 1) > delta) {
			_new_weight = *(nodes + 1) - delta;
			if (_new_weight > weight) {
				weight = _new_weight;
				topk = 1;
			} else if (_new_weight == weight) {
				topk++;
			}
			*fill = node;
			*(++fill) = _new_weight;
			*(++fill) = 0;
			fill++;
			size++;
		}
	}
	*fill = 0;
	IS_WEIT(iset_idx) = weight;
	IS_SIZE(iset_idx) = size;
	IS_TOPK(iset_idx) = topk;
}

static void reduce_iset_top_weight(int iset_idx, int delta, int t_weight) {
	int topk = 0, weight = 0, node_weight, size = 0;
	int node, *nodes = IS_NODES(iset_idx), *fill = nodes;
	weight = IS_WEIT(iset_idx) - delta;

	if (weight == 0) {
		IS_STAT(iset_idx) = PASSIVE;
		IS_SIZE(iset_idx) = 0;
		IS_WEIT(iset_idx) = 0;
		IS_TOPK(iset_idx) = 0;
		*fill = 0;
	} else {
		for (node = *nodes; node != 0; node = *(nodes += 3)) {
			node_weight = *(nodes + 1);
			if (node_weight > t_weight) {
				if (node_weight - delta >= t_weight) {
					node_weight -= delta;
				} else {
					node_weight = t_weight;
				}
				if (node_weight > 0) {
					*fill = node;
					*(++fill) = node_weight;
					*(++fill) = 0;
					fill++;
					size++;
					if (node_weight == weight)
						topk++;
				}

			} else {
				break;
			}
		}
		for (node = *nodes; node != 0; node = *(nodes += 3)) {
			*fill = node;
			*(++fill) = *(nodes + 1);
			*(++fill) = 0;
			fill++;
			size++;
			if (node_weight == weight)
				topk++;
		}
		IS_WEIT(iset_idx) = weight;
		IS_SIZE(iset_idx) = size;
		IS_TOPK(iset_idx) = topk;
		*fill = 0;
	}
}
static void reduce_iset_topk_new(int iset_idx, int delta, int t_weight) {
	int topk = 0, weight = 0, node_weight;
	int node, *nodes = IS_NODES(iset_idx), *fill = nodes;
	weight = IS_WEIT(iset_idx) - delta;

	for (node = *nodes; node != 0; node = *(nodes += 3)) {
		node_weight = *(nodes + 1);
		if (node_weight > t_weight) {
			if (node_weight - delta >= t_weight) {
				*(nodes + 1) = node_weight - delta;

			} else {
				*(nodes + 1) = t_weight;
			}
		}
		if (*(nodes + 1) == weight)
			topk++;
	}
	IS_WEIT(iset_idx) = weight;
	IS_TOPK(iset_idx) = topk;
}
static void reduce_iset_topk(int iset_idx, int delta) {
	int topk = 0, weight = 0;
	int node, *nodes = IS_NODES(iset_idx), *fill = nodes;
	weight = IS_WEIT(iset_idx) - delta;

	if (weight == 0) {
//		for (node = *nodes; node != NONE; node = *(++nodes)) {
//			Node_State[node] = PASSIVE;
//		}
		IS_STAT(iset_idx) = PASSIVE;
		IS_SIZE(iset_idx) = 0;
		IS_WEIT(iset_idx) = 0;
		IS_TOPK(iset_idx) = 0;
		*fill = 0;
	} else {
		for (node = *nodes; node != 0; node = *(nodes += 3)) {
			if (*(nodes + 1) > weight) {
				*(nodes + 1) = weight;
				topk++;
			} else if (*(nodes + 1) == weight)
				topk++;
		}
		IS_WEIT(iset_idx) = weight;
		IS_TOPK(iset_idx) = topk;
	}
}
static int INVOLVE_NEW;
static int get_delta(int iset) {
	int delta, node, *nodes, flag = FALSE;
	nodes = IS_NODES(iset);
	delta = IS_WEIT(iset);
	for (node = *nodes; node != 0; node = *(nodes += 3)) {
		if (node > 0) {
			if (flag == FALSE) {
				flag = TRUE;
			} else {
				delta -= *(nodes + 1);
				break;
			}
		}
	}
	return delta;
}
static int find_reasons_and_delta(int reason_start, int top_reason_start) {
	int i, iset, node, *nodes, _reason, reason_iset, delta = NONE, _delta;
	for (i = top_reason_start; i < ptr(REASON_STACK); i++) {
		iset = REASON_STACK[i];
		nodes = IS_NODES(iset);
		for (node = *nodes; node != 0; node = *(nodes += 3)) {
			if (node < 0) {
				_reason = *(nodes + 2);
				if (_reason == NO_REASON) {
					INVOLVE_NEW = TRUE;
				} else if (IS_INVO(_reason) == FALSE) {
					push(_reason, REASON_STACK);
					//*(nodes + 2) = NULL_REASON;
					IS_INVO(_reason) = TRUE;
				}
			}
		}
	}
	for (i = reason_start + 1; i < ptr(REASON_STACK); i++) {
		_delta = get_delta(REASON_STACK[i]);
		if (delta == NONE || _delta < delta)
			delta = _delta;
	}
	return delta;
}

static int identify_topk_conflict_sets_bak(int t_delta, int topk_idx) {
	int i, _reason, reason_start = ptr(REASON_STACK), iset_weight, *nodes, node,
			reason_iset, count = 0, delta = NONE, max_delta = 0;
	char flag;
	int *top_start, top_weight, top_reason_start, max_reason;

	INVOLVE_NEW = FALSE;
	push(topk_idx, REASON_STACK);
	IS_INVO(topk_idx) = TRUE;

	top_start = IS_NODES(topk_idx);
	top_weight = *(top_start + 1);
	top_reason_start = ptr(REASON_STACK);

	while (1) {
		flag = TRUE;
		if (*top_start == 0)
			break;
		for (node = *top_start; node != 0; node = *(top_start += 3)) {
			if (*(top_start + 1) == top_weight) {
				if (node < 0) {
					_reason = *(top_start + 2);
					if (_reason == NO_REASON) {
						INVOLVE_NEW = TRUE;
					} else if (IS_INVO(_reason) == FALSE) {
						push(_reason, REASON_STACK);
						//*(top_start + 2) = NULL_REASON;
						IS_INVO(_reason) = TRUE;
					}
				} else {
					flag = FALSE;
					for (i = top_reason_start; i < ptr(REASON_STACK); i++)
						IS_INVO(REASON_STACK[i]) = FALSE;
					ptr(REASON_STACK) = top_reason_start;
					break;
				}
			} else {
				break;
			}
		}
		if (flag == FALSE) {
			assert(max_delta > 0);
			break;
		} else {
			if (node == 0)
				top_weight = 0;
			else
				top_weight = *(top_start + 1);

			delta = find_reasons_and_delta(reason_start, top_reason_start);

			if (delta == NONE || delta > IS_WEIT(topk_idx) - top_weight)
				delta = IS_WEIT(topk_idx) - top_weight;

			assert(delta > 0);

			if (delta > max_delta) {
				max_delta = delta;
				max_reason = ptr(REASON_STACK);
				top_reason_start = ptr(REASON_STACK);

				if (max_delta >= t_delta)
					break;
			} else {
				delta = max_delta;
				for (i = max_reason; i < ptr(REASON_STACK); i++)
					IS_INVO(REASON_STACK[i]) = FALSE;
				ptr(REASON_STACK) = max_reason;
				break;
			}
		}
	}

	assert(max_delta > 0);
	for (i = reason_start; i < ptr(REASON_STACK); i++) {
		IS_USED(REASON_STACK[i]) = TRUE;
		IS_INVO(REASON_STACK[i]) = FALSE;
	}
	push(NONE, REASON_STACK);

	if (max_delta > t_delta)
		return t_delta;
	else
		return max_delta;
}

static int check_t_weight(int iset) {
	int node, *nodes, weight, flag = FALSE;
	nodes = IS_NODES(iset);
	weight = *(nodes + 1);
	for (node = *nodes; node != 0; node = *(nodes += 3)) {
		if (*(nodes + 1) != weight) {
			weight = *(nodes + 1);
		}
		if (node > 0) {
			if (flag == TRUE) {
				break;
			} else {
				assert(*(nodes+1)==IS_WEIT(iset));
				flag = TRUE;
			}
		}
	}
	if (node == 0) {
		return 0;
	} else {
		return weight;
	}
}

static int expand_topk_empty_reasons(int topk_idx) {
	int reason, weight = IS_WEIT(topk_idx);
	int node, *nodes = IS_NODES(topk_idx);
	int last_node = *nodes;
	int delta = weight;

	ptr(REASON_STACK) = 0;
	push(topk_idx, REASON_STACK);
	IS_INVO(topk_idx) = TRUE;

	for (node = *nodes; node != 0; node = *(nodes += 3)) {
		if (*(nodes + 1) != weight) {
			weight = *(nodes + 1);
			last_node = node;
		}
		if (node > 0)
			break;
	}
	if (node == 0) {
		last_node = 0;
		push(0, REASON_STACK);
	} else {
		delta -= weight;
		push(weight, REASON_STACK);
	}

	nodes = IS_NODES(topk_idx);
	for (node = *nodes; node != last_node; node = *(nodes += 3)) {
		assert(node < 0);
		reason = *(nodes + 2);
		if (reason == NO_REASON) {
			INVOLVE_NEW = TRUE;
		} else if (IS_INVO(reason) == FALSE) {
			push(reason, REASON_STACK);
			push(check_t_weight(reason), REASON_STACK);
			IS_INVO(reason) = TRUE;
		}
	}
	return delta;
}

//static int expand_reasons(int iset, int delta_weight) {
//	int reason, node, *nodes;
//
//	nodes = IS_NODES(iset);
//	for (node = *nodes; *(nodes + 1) != delta_weight; node = *(nodes += 3)) {
//		reason = *(nodes + 2);
//		if (reason == NO_REASON) {
//			INVOLVE_NEW = TRUE;
//		} else if (IS_INVO(reason) == FALSE) {
//			push(reason, REASON_STACK);
//			push(check_t_weight(reason), REASON_STACK);
//			IS_INVO(reason) = TRUE;
//		}
//	}
//	return IS_WEIT(iset) - delta_weight;
//}

static int identify_topk_conflict_sets(int t_delta, int topk_idx) {
	int i, iset, t_weight, reason, *nodes, node, delta = NONE, min_delta;
	INVOLVE_NEW = FALSE;
	min_delta = expand_topk_empty_reasons(topk_idx);

	for (i = 2; i < ptr(REASON_STACK); i += 2) {
		iset = REASON_STACK[i];
		t_weight = REASON_STACK[i + 1];
		delta = IS_WEIT(REASON_STACK[i]) - t_weight;
		if (delta < min_delta)
			min_delta = delta;

		nodes = IS_NODES(iset);
		for (node = *nodes; node != 0; node = *(nodes += 3)) {
			if (*(nodes + 1) > t_weight) {
				reason = *(nodes + 2);
				if (reason == NO_REASON) {
					INVOLVE_NEW = TRUE;
				} else if (IS_INVO(reason) == FALSE) {
					push(reason, REASON_STACK);
					push(check_t_weight(reason), REASON_STACK);
					IS_INVO(reason) = TRUE;
				}
			}
		}
	}

	if (INVOLVE_NEW == FALSE)
		return min_delta;
	else if (min_delta > t_delta)
		return t_delta;
	else
		return min_delta;
}

//static int identify_top1_conflict_sets(int topk_idx) {
//	int i, reason_start = ptr(REASON_STACK), iset_weight, iset, *nodes, node,
//			reason_iset, count = 0, delta;
//	/*sort nodes by weight*/
//	nodes = iSET[topk_idx];
//	for (node = *nodes; node != NONE; node = *(++nodes)) {
//		count++;
//	}
//	qsort(iSET[topk_idx], count, sizeof(int), weight_desc);
//
//	/*TEST*/
////	assert(iSET_Topk[topk_idx] == 0);
////	assert(Node_Weight[iSET[topk_idx][0]] == iSET_Weight[topk_idx]);
////	nodes = iSET[topk_idx];
////	for (node = *nodes; node != NONE; node = *(++nodes)) {
////		if (*(nodes + 1) != NONE) {
////			assert(Node_Weight[node] >= Node_Weight[*(nodes + 1)]);
////		}
////		if (Node_Weight[node] == iSET_Weight[topk_idx]) {
////			assert(Node_State[node]==P_FALSE);
////		}
////	}
//	/*END*/
//
//	push(topk_idx, REASON_STACK);
//	iSET_Involved[topk_idx] = TRUE;
//
//	nodes = iSET[topk_idx];
//	iset_weight = iSET_Weight[topk_idx];
//	if (iset_weight <= 0)
//		printf("iset_weight=%d\n", iset_weight);
//	assert(iset_weight > 0);
//	for (node = *nodes; node != NONE; node = *(++nodes)) {
//		if (Node_Weight[node] == iset_weight) {
//			assert(Node_State[node] == P_FALSE);
//			if (Node_Reason[node] != NO_REASON
//					&& iSET_Involved[Node_Reason[node]] == FALSE) {
//				reason_iset = Node_Reason[node];
//				push(reason_iset, REASON_STACK);
//				Node_Reason[node] = NO_REASON;
//				iSET_Involved[reason_iset] = TRUE;
//			}
//		} else
//			break;
//	}
//
//	if (node == NONE)
//		delta = iset_weight;
//	else
//		delta = iset_weight - Node_Weight[node];
//
//	assert(delta > 0);
//	/*********************/
//
//	for (i = reason_start + 1; i < ptr(REASON_STACK); i++) {
//		iset = REASON_STACK[i];
//		nodes = iSET[iset];
//		for (node = *nodes; node != NONE; node = *(++nodes))
//			if (Node_State[node] == P_FALSE && Node_Reason[node] != NO_REASON
//					&& iSET_Involved[Node_Reason[node]] == FALSE) {
//				reason_iset = Node_Reason[node];
//				push(reason_iset, REASON_STACK);
//				Node_Reason[node] = NO_REASON;
//				iSET_Involved[reason_iset] = TRUE;
//			}
//	}
//	for (i = reason_start; i < ptr(REASON_STACK); i++) {
//		iSET_Involved[REASON_STACK[i]] = FALSE;
//		iSET_Used[REASON_STACK[i]] = TRUE;
//	}
//
//	reset_context_for_maxsatz();
//
//	/***find the min weight iset*/
//	for (i = reason_start + 1; i < ptr(REASON_STACK); i++) {
//		if (iSET_Weight[REASON_STACK[i]] < delta)
//			delta = iSET_Weight[REASON_STACK[i]];
//	}
//	/*reduce iset*/
//	assert(delta > 0);
//	reduce_iset_topk(REASON_STACK[reason_start], delta);
//	for (i = reason_start + 1; i < ptr(REASON_STACK); i++) {
//		reduce_iset(REASON_STACK[i], delta);
//	}
//
//	/*TEST*/
////check_iset2(delta, ptr(REASON_STACK) - reason_start);
//	/******/
//	iset_weight = 0;
//	for (i = 0; i < iSET_COUNT; i++) {
//		iset_weight += iSET_Weight[i];
//	}
//	assert(
//			iset_weight + (ptr(REASON_STACK) - reason_start) * delta == iSET_TOTAL_WEIGHT);
//	iSET_TOTAL_WEIGHT = iset_weight;
//	HIDDEN_WEIGHT += (ptr(REASON_STACK) - reason_start - 1) * delta;
//	ptr(REASON_STACK) = reason_start;
//	return delta;
//}

//static void identify_conflict_sets(int iset_idx) {
//	int i, reason_start = ptr(REASON_STACK), iset, *nodes, node, reason_iset;
//	push(iset_idx, REASON_STACK);
//	iSET_Involved[iset_idx] = TRUE;
//	for (i = reason_start; i < ptr(REASON_STACK); i++) {
//		iset = REASON_STACK[i];
//		nodes = iSET[iset];
//		for (node = *nodes; node != NONE; node = *(++nodes))
//			if (Node_State[node] == P_FALSE && Node_Reason[node] != NO_REASON
//					&& iSET_Involved[Node_Reason[node]] == FALSE) {
//				reason_iset = Node_Reason[node];
//				push(reason_iset, REASON_STACK);
//				Node_Reason[node] = NO_REASON;
//				iSET_Involved[reason_iset] = TRUE;
//			}
//	}
//	for (i = reason_start; i < ptr(REASON_STACK); i++) {
//		iSET_Involved[REASON_STACK[i]] = FALSE;
//		iSET_Used[REASON_STACK[i]] = TRUE;
//	}
//}

# define SAVE_CONTEXT memcpy(IS_BACKUP, IS_HEAD, IS_LENGTH * sizeof(int));
# define RESTORE_CONTEXT memcpy(IS_HEAD,IS_BACKUP, IS_LENGTH * sizeof(int));

//static int fix_anyNode_for_iset(int fix_node, int fix_iset) {
//	if (fix_node > MAX_VERTEX_NO)
//		return fix_newNode_for_iset(fix_node, fix_iset);
//	else
//		return fix_oldNode_for_iset(fix_node, fix_iset);
//}
static void init_for_maxsat_reasoning() {
	int i;
	ptr(UNIT_STACK) = 0;
	ptr(REASON_STACK) = 0;
	ptr(NEW_UNIT_STACK) = 0;
	ptr(TOP_UNIT_STACK) = 0;

	for (i = 0; i < iSET_COUNT; i++) {
		IS_USED(i) = FALSE;
		IS_INVO(i) = FALSE;

		if (IS_SIZE(i) > 0) {
			IS_STAT(i) = ACTIVE;
			if (IS_SIZE(i) == 1)
				push(i, UNIT_STACK);
			else if (IS_TOPK(i) == 1)
				push(i, TOP_UNIT_STACK);
		} else {
			IS_STAT(i) = PASSIVE;
		}
	}
}

//static int reduce_weight_by_maxsat_reasoning_tree() {
//	int i, j, topk_empty_iset, node, *nodes, iset_idx = iSET_COUNT - 1;
//	ptr(UNIT_STACK) = 0;
//	ptr(REASON_STACK) = 0;
//	ptr(NEW_UNIT_STACK) = 0;
//	ptr(FIXED_NODE_STACK) = 0;
//	ptr(PASSIVE_iSET_STACK) = 0;
//	ptr(REDUCED_iSET_STACK) = 0;
//	ptr(REDUCED_TOPK_STACK) = 0;
//
//	for (i = 0; i < iSET_COUNT; i++) {
//		if (iSET_Size[i] > 0) {
//			assert(iSET_Weight[i] > 0);
//			iSET_Used[i] = FALSE;
//			iSET_State[i] = ACTIVE;
//			iSET_Involved[i] = FALSE;
//			if (iSET_Size[i] == 1)
//				push(i, UNIT_STACK);
//		} else {
//			iSET_State[i] = PASSIVE;
//			assert(iSET_Weight[i] == 0);
//		}
//	}
//	nodes = iSET[iset_idx];
//	node = *nodes;
//	assert(iSET_Size[iset_idx] == 1);
//	assert(Node_State[node] == ACTIVE);
//
//	for (i = 0; i < ptr(UNIT_STACK); i++) {
//		iset_idx = UNIT_STACK[i];
//		if (iSET_State[iset_idx] == ACTIVE && iSET_Size[iset_idx] == 1) {
//			ptr(NEW_UNIT_STACK) = 0;
//			fix_node_iset(iset_idx);
//			for (j = 0; j < ptr(NEW_UNIT_STACK); j++) {
//				iset_idx = NEW_UNIT_STACK[j];
//				if (iSET_State[iset_idx] == ACTIVE) {
//					fix_node_iset(iset_idx);
//				}
//			}
//		}
//	}
//
//	if ((topk_empty_iset = fix_oldNode_for_iset(node, iset_idx)) != NONE
//			|| (topk_empty_iset = unit_iset_process_used_first()) != NONE
//			|| (topk_empty_iset = unit_iset_process()) != NONE) {
//		//return identify_topk_conflict_sets(topk_empty_iset);
//		return identify_top1_conflict_sets(topk_empty_iset);
//	} else
//		return 0;
//}

static int select_idependent_branching_nodes(int first_index) {
	int i = first_index, j, node, weight = 0;
	unsigned char *adj_list;
	ptr(B_STACK) = 0;
	while ((node = Candidate_Stack[i]) != DELIMITER) {
		if (node < 0) {
			node = -node;
			adj_list = iMatrix(node);
			for (j = 0; j < ptr(B_STACK); j += 2) {
				if (Matrix(adj_list,B_STACK[j]) > 0)
					break;
			}
			if (j == ptr(B_STACK)) {
				push(node, B_STACK);
				push(i, B_STACK);
				i--;		//only one
				break;		//only one
			} else {
				break;
			}

		}
		i--;
	}
	while ((node = Candidate_Stack[i]) != DELIMITER) {
		if (node < 0)
			break;
		else
			i--;
	}
	return i;
}

//static int open_new_iset_new(int i, int *last_iset) {
//	int *current_set, node, iset_node, last_idx = NONE;
//	unsigned char *adj_list;
//	iSET_Size[iSET_COUNT] = 0;
//	iSET[iSET_COUNT][0] = NONE;
//	iSET_Used[iSET_COUNT] = FALSE;
//	iSET_State[iSET_COUNT] = ACTIVE;
//
//	while ((node = Candidate_Stack[i]) != DELIMITER) {
//		if (Node_State[node] == PASSIVE) {
//			adj_list = iMatrix(node);
//			current_set = iSET[iSET_COUNT];
//			for (iset_node = *current_set; iset_node != NONE; iset_node =
//					*(++current_set)) {
//				if (Matrix(adj_list,iset_node) > 0)
//					break;
//			}
//			if (iset_node == NONE) {
//				iSET_Size[iSET_COUNT]++;
//				*(current_set) = node;
//				*(++current_set) = NONE;
//				iSET_Index[node] = iSET_COUNT;
//				Node_State[node] = ACTIVE;
//				Node_Reason[node] = NO_REASON;
//				last_idx = i;
//			} else {
//				break;
//			}
//		}
//		i--;
//	}
//
//	if (last_idx != NONE) {
//
//		if (iSET_Size[iSET_COUNT] == 1) {
//			push(UNIT_STACK[0], UNIT_STACK);
//			UNIT_STACK[0] = iSET_COUNT;
//		}
//		if (node == DELIMITER)
//			*last_iset = TRUE;
//		else
//			*last_iset = FALSE;
//		iSET_COUNT++;
//		return last_idx;
//	} else {
//		return NONE;
//	}
//}

//static int cut_by_inc_maxsat() {
//	int i, j, node, flag = TRUE, last_iset;
//	ADDED_NODE = NB_NODE + 1;
//	ptr(CONFLICT_ISET_STACK) = 0;
//	ptr(UNIT_STACK) = 0;
//	cut_satz++;
//	for (i = 0; i < iSET_COUNT; i++) {
//		if (iSET_Size[i] == 1)
//			push(i, UNIT_STACK);
//	}
//	while ((node = Candidate_Stack[FIRST_INDEX]) != DELIMITER) {
//		if ((j = open_new_iset_new(FIRST_INDEX, &last_iset)) == NONE) {
//			flag = TRUE;
//			break;
//		}
//		if ((node = inc_maxsatz_on_last_iset()) == NONE) {
//			FIRST_INDEX = j - 1;
//		} else {
//			if (last_iset == TRUE && test_by_eliminate_failed_nodes() == TRUE) {
//				flag = TRUE;
//			} else {
//				while (Candidate_Stack[FIRST_INDEX] != node)
//					FIRST_INDEX--;
//				Branching_Point = FIRST_INDEX + 1;
//				flag = FALSE;
//				cut_satz--;
//			}
//			break;
//		}
//	}
//
//	i = ptr(Candidate_Stack) - 2;
//	while ((node = Candidate_Stack[i--]) != DELIMITER) {
//		Node_State[node] = PASSIVE;
//	}
//	if (flag == TRUE) {
//		Vertex_UB[CURSOR]=MAX_CLQ_SIZE - CUR_CLQ_SIZE;
//	}
//	return flag;
//}

static void check_iset3() {
	int i, count, topk, iset_node, *current_set, weight = 0, iset_weight;
	for (i = 0; i < iSET_COUNT; i++) {
		is_iset(i);
		count = 0;
		topk = 0;
		iset_weight = 0;
		current_set = iSET[i];
		for (iset_node = *current_set; iset_node != NONE; iset_node =
				*(++current_set)) {
			//assert(iSET_Index[iset_node] == i);
			assert(Node_Weight[iset_node] > 0);
			count++;
			if (Node_Weight[iset_node] > iset_weight) {
				iset_weight = Node_Weight[iset_node];
				topk = 1;
			} else if (Node_Weight[iset_node] == iset_weight)
				topk++;
		}
		assert(count == iSET_Size[i]);
		if (count > 0) {
			assert(topk >= 1);
		} else {
			assert(topk == 0);
			assert(iSET_Weight[i] == 0);
		}
		//assert(topk == iSET_Topk[i]);
		assert(iSET_Weight[i] == iset_weight);
		weight += iSET_Weight[i];
	}
	assert(weight == iSET_TOTAL_WEIGHT);
}

static int test_weight_compatibility(int b_node, int b_weight, int t_weight) {
	int iset, delta = 0;
	IS_BACKUP = IS_HEAD + IS_LENGTH;
	memcpy(IS_BACKUP, IS_HEAD, IS_LENGTH * sizeof(int));
	if ((iset = fix_b_node(b_node)) != NONE
			|| (iset = unit_iset_process()) != NONE || (iset =
					top_unit_iset_process()) != NONE) {
		delta = identify_topk_conflict_sets(b_weight, iset);
	}
	memcpy(IS_HEAD, IS_BACKUP, IS_LENGTH * sizeof(int));
	return delta;
}

static void reduce_iset_weight_new(int delta) {
	int i, topk_iset;
	for (i = 0; i < ptr(REASON_STACK); i++) {
		topk_iset = REASON_STACK[i];
		if (topk_iset < 0) {
			reduce_iset_topk(-topk_iset, delta);
			//IS_INVO(-topk_iset) = TRUE;
		} else {
			reduce_iset(topk_iset, delta);
			//IS_INVO(topk_iset) = TRUE;
		}
		iSET_TOTAL_WEIGHT -= delta;
		HIDDEN_WEIGHT += delta;
	}
}

static void reduce_iset_weight_new_new(int delta) {
	int i;
	for (i = 0; i < ptr(REASON_STACK); i += 2) {
		if (REASON_STACK[i + 1] == 0) {
			reduce_iset(REASON_STACK[i], delta);
		} else {
			reduce_iset_topk_new(REASON_STACK[i], delta, REASON_STACK[i + 1]);
		}

		iSET_TOTAL_WEIGHT -= delta;
		HIDDEN_WEIGHT += delta;
	}
}

static void reduce_iset_weight(int t_weight, int delta) {
	int i, j, topk_iset, b_node;
	for (i = 0; i < ptr(REASON_STACK); i++) {
		topk_iset = REASON_STACK[i];
		if (IS_INVO(topk_iset) == FALSE) {
			reduce_iset_topk(topk_iset, delta);
			IS_INVO(topk_iset) = TRUE;
			iSET_TOTAL_WEIGHT -= delta;
			HIDDEN_WEIGHT += delta;
		}

		for (j = i + 1; j < ptr(REASON_STACK); j++) {
			if (REASON_STACK[j] == NONE) {
				i = j;
				break;
			}
			if (IS_INVO(REASON_STACK[j]) == FALSE) {
				reduce_iset_topk(REASON_STACK[j], delta);
				IS_INVO(REASON_STACK[j]) = TRUE;
				iSET_TOTAL_WEIGHT -= delta;
				HIDDEN_WEIGHT += delta;
			}
		}
	}
//	for (i = 0; i < ptr(B_STACK); i += 2) {
//		b_node = B_STACK[i];
//		if (b_node != NONE && Node_Weight[b_node] > t_weight) {
//			Node_Weight[b_node] -= delta;
//		}
//	}
}

//static void do_maxsat_reasoning_on_branching_nodes() {
//	int delta, t_weight = MAX_ISET_WEIGHT - HIDDEN_WEIGHT - iSET_TOTAL_WEIGHT;
//	assert(t_weight >= 0);
//	while (1) {
//		init_for_maxsat_reasoning();
//		delta = test_weight_compatibility(t_weight);
//		if (delta > 0) {
//			reduce_iset_weight(t_weight, delta);
//		} else
//			break;
//	}
//}

static void add_new_unit_iset(int b_node, int b_weight) {
	int *fill;
	IS[iSET_COUNT] = IS_HEAD + IS_LENGTH;
	IS_STAT(iSET_COUNT) = ACTIVE;
	IS_WEIT(iSET_COUNT) = b_weight;
	IS_SIZE(iSET_COUNT) = 1;
	IS_TOPK(iSET_COUNT) = 1;
	fill = IS_NODES(iSET_COUNT);
	*fill = b_node;
	*(++fill) = b_weight;
	*(++fill) = NULL_REASON;
	*(++fill) = 0;
	IS_LENGTH += 8;
	iSET_COUNT++;
	iSET_TOTAL_WEIGHT += b_weight;
}

static int check_branching_nodes() {
	int i, len = 4, first_idx = NONE;
	int node, *nodes, *fill, base_delta = MAX_ISET_WEIGHT - HIDDEN_WEIGHT
			- iSET_TOTAL_WEIGHT;
	IS[iSET_COUNT] = IS_HEAD + IS_LENGTH;
	IS_SIZE(iSET_COUNT) = 0;
	fill = IS_NODES(iSET_COUNT);
//iSET_Size[iSET_COUNT] = 0;

	for (i = 0; i < ptr(B_STACK); i += 2) {
		node = B_STACK[i];
		if (node != NONE) {
			assert(Node_Weight[node] >= 0);
			assert(Node_Weight[node] <= base_delta);
			Candidate_Stack[B_STACK[i + 1]] = node;
			NB_TOPK++;
			if (Node_Weight[node] > 0) {
				*fill = node;
				*(++fill) = Node_Weight[node];
				*(++fill) = 0;
				fill++;
				IS_SIZE(iSET_COUNT)++;
				len += 3;
//				Node_State[node] = ACTIVE;
//				iSET[iSET_COUNT][iSET_Size[iSET_COUNT]++] = node;
//				iSET_Index[node] = iSET_COUNT;
			}
		} else if (first_idx == NONE) {
			first_idx = B_STACK[i + 1];
		}
	}
//	if (first_idx != NONE) {
//		FIRST_INDEX = first_idx;
//		return FALSE;
//	} else {
	if (IS_SIZE(iSET_COUNT) > 0) {
		IS_STAT(iSET_COUNT) = ACTIVE;
		IS_WEIT(iSET_COUNT) = 0;
		IS_TOPK(iSET_COUNT) = 0;
		*fill = 0;
		len++;
		//iSET[iSET_COUNT][iSET_Size[iSET_COUNT]] = NONE;
		nodes = IS_NODES(iSET_COUNT);
		for (node = *nodes; node != 0; node = *(nodes += 3)) {
			if (*(nodes + 1) > IS_WEIT(iSET_COUNT)) {
				IS_WEIT(iSET_COUNT) = *(nodes + 1);
				IS_TOPK(iSET_COUNT) = 1;
			} else if (*(nodes + 1) == IS_WEIT(iSET_COUNT)) {
				IS_TOPK(iSET_COUNT)++;
			}
		}
		iSET_TOTAL_WEIGHT += IS_WEIT(iSET_COUNT);
		if (IS_SIZE(iSET_COUNT) > 1)
			qsort(IS_NODES(iSET_COUNT), IS_SIZE(iSET_COUNT), 3 * sizeof(int),
					weight_desc2);
		iSET_COUNT++;
		IS_LENGTH += len;
	}
	return TRUE;
//}
}

static void check_build_structures() {
	int i, j, node, *nodes;
	for (i = 0; i < iSET_COUNT; i++) {
		assert(IS_STAT(i)==ACTIVE);
		assert(IS_WEIT(i)==iSET_Weight[i]);
		assert(IS_SIZE(i)==iSET_Size[i]);
		//assert(IS_TOPK(i)==iSET_Topk[i]);
	}
	for (i = 0; i < iSET_COUNT; i++) {
		j = 0;
		nodes = IS_NODES(i);
		for (node = *nodes; node != 0; node = *(nodes += 3)) {
			assert(node > 0);
			assert(*(nodes + 1) == Node_Weight[node]);
			assert(node == iSET[i][j]);
			j++;
		}
		assert(iSET[i][j]==NONE);
	}
}

static void build_structures() {
	int i, *addr, node, *nodes;
	char * head;
	addr = IS_HEAD;
	IS_LENGTH = 0;
	for (i = 0; i < iSET_COUNT; i++) {
		IS[i] = addr;

		head = (char *) addr;
		*head = ACTIVE;     //iSET_State;
		*(++head) = FALSE;  //iSET_Used;
		*(++head) = FALSE;  //iSET_Involved;
		*(++head) = FALSE;  //iSET_Tested;

		*(++addr) = iSET_Weight[i];
		*(++addr) = iSET_Size[i];
		*(++addr) = 0;
		IS_LENGTH += 4;

		qsort(iSET[i], iSET_Size[i], sizeof(int), weight_desc);
		nodes = iSET[i];
		for (node = *nodes; node != NONE; node = *(++nodes)) {
			*(++addr) = node;
			*(++addr) = Node_Weight[node];
			*(++addr) = NULL_REASON;
			if (Node_Weight[node] == IS_WEIT(i))
				IS_TOPK(i)++;
			IS_LENGTH += 3;
		}
		*(++addr) = 0;
		addr++;
		IS_LENGTH += 1;
	}
}
static int NB_DELTA = 0;
static int cut_by_inc_maxsat_reasoning() {
	int i, k, node, t_weight, delta, b_weight, w1, w2;
	HIDDEN_WEIGHT = 0;
	build_structures();
	k = FIRST_INDEX;
	while ((node = Candidate_Stack[k]) != DELIMITER) {
		if (node < 0) {
			node = -node;

			w1 = HIDDEN_WEIGHT;
			w2 = iSET_TOTAL_WEIGHT;
			memcpy(IS_HEAD + IS_LENGTH * 2, IS_HEAD, IS_LENGTH * sizeof(int));

			b_weight = Node_Weight[node];
			t_weight = MAX_ISET_WEIGHT - HIDDEN_WEIGHT - iSET_TOTAL_WEIGHT;

			while (b_weight > t_weight) {
				init_for_maxsat_reasoning();
				delta = test_weight_compatibility(node, b_weight, t_weight);
				if (delta > 0) {
					NB_DELTA++;
					reduce_iset_weight_new_new(delta);
					if (INVOLVE_NEW == TRUE)
						b_weight -= delta;
					else {
						HIDDEN_WEIGHT -= delta;
						t_weight += delta;
					}
				} else
					break;
			}
			if (b_weight > t_weight) {
				HIDDEN_WEIGHT = w1;
				iSET_TOTAL_WEIGHT = w2;
				memcpy(IS_HEAD, IS_HEAD + IS_LENGTH * 2,
						IS_LENGTH * sizeof(int));
			} else {
				NB_TOPK++;
				Candidate_Stack[k] = node;
				if (b_weight > 0)
					add_new_unit_iset(node, b_weight);
			}
		}
		k--;
	}
	while ((node = Candidate_Stack[FIRST_INDEX]) != DELIMITER) {
		if (node < 0)
			break;
		else
			FIRST_INDEX--;
	}

	if (Candidate_Stack[FIRST_INDEX] == DELIMITER) {
		Vertex_UB[CURSOR]=MAX_CLQ_WEIGHT - CUR_CLQ_WEIGHT;
		cut_satz++;
		return TRUE;
	} else {
		Branching_Point = FIRST_INDEX + 1;
		for (node = Candidate_Stack[i= FIRST_INDEX]; node != DELIMITER; node =
				Candidate_Stack[--i]) {
			if (node < 0 && i > LAST_IN) {
				Vertex_UB[i] = UPPER_WEIGHT_BOUND - CUR_CLQ_WEIGHT
				- CUR_NODE_WEIGHT;
			}
		}
		return FALSE;
	}
}

static void rebuild_matrix(int start) {
	int i = start, j = 1, node, neibor, *neibors;

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Candidate_Stack[i] = j;
		Second_Name[j] = node;
		Node_Degree[node] = j++;
		Node_State[node] = ACTIVE;
	}
	memset(Adj_Matrix, 0,
			(MAX_SUBGRAPH_SIZE + 1) * (MATRIX_ROW_WIDTH) * sizeof(char));

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		neibors = Node_Neibors[Second_Name[node]];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (Node_State[neibor] == ACTIVE) {
				SET_EDGE(node, Node_Degree[neibor]);
				SET_EDGE(Node_Degree[neibor], node);
			}
		}
	}
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Node_State[Second_Name[node]] = PASSIVE;
		Node_Weight[node] = Top_Weight[Second_Name[node]];
	}
}

static int REBUILD_MATRIX = FALSE;
static void store_maximal_weighted_clique() {
	memcpy(MaxCLQ_Stack, Clique_Stack, CUR_CLQ_SIZE * sizeof(int));

	if (CUR_CLQ_SIZE == 0)
		MaxCLQ_Stack[CUR_CLQ_SIZE] = Candidate_Stack[CURSOR];
		else
		MaxCLQ_Stack[CUR_CLQ_SIZE]=Second_Name[Candidate_Stack[CURSOR]];

	MAX_CLQ_SIZE = CUR_CLQ_SIZE + 1;

	MAX_CLQ_WEIGHT = CUR_CLQ_WEIGHT + CUR_NODE_WEIGHT;

	printf("C %8d |%8d |%8d %10d %10d %10d|%10d %10.2lf \n",
			Cursor_Stack[0] + 1, MAX_CLQ_WEIGHT, cut_ver, cut_inc, cut_iset,
			cut_satz, BRANCHING_COUNT, get_utime() - READ_TIME - INIT_TIME);
	fflush(stdout);
	total_cut_ver += cut_ver;
	cut_ver = 0;
	total_cut_inc += cut_inc;
	cut_inc = 0;
	total_cut_iset += cut_iset;
	cut_iset = 0;
	total_cut_satz += cut_satz, cut_satz = 0;
	Last_Idx = CURSOR;
	if (MAX_CLQ_WEIGHT == UPPER_WEIGHT_BOUND) {
		ptr(Cursor_Stack) = 1;
		ptr(Clique_Stack) = 0;
		Rollback_Point = NB_NODE + 1;
		CUR_CLQ_WEIGHT = 0;
		Vertex_UB[CURSOR]=MAX_CLQ_WEIGHT;
	}
}
static int compute_subgraphs_weight(int start) {
	int i = start, j = 0, node, neibor, *neibors, max_weight = 0;
	int nb_node = 0, nb_edge = 0;

//	/*<TEST>*/
//	for (node = 1; node <= NB_NODE; node++)
//		assert(Node_State[node] == PASSIVE);
//	/*</TEST>*/

	j = 0;
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Node_State[node] = ACTIVE;
		Node_Weight[node] = Top_Weight[node];
		Node_Degree[node] = j;
		iSET_Size[j] = 0;
		j++;
	}
	nb_node = j;
	N1_B = nb_node;
	/*TEST*/
//	if (j > MAX_VERTEX_NO)
//		printf("****%d %d\n", j, MAX_VERTEX_NO);
//	assert(j <= MAX_VERTEX_NO);
	/******/

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (Node_State[neibor] == ACTIVE) {
				nb_edge++;
				j = Node_Degree[node];
				iSET[j][iSET_Size[j]++] = neibor;
				Node_Weight[node] += Top_Weight[neibor];

				j = Node_Degree[neibor];
				iSET[j][iSET_Size[j]++] = node;
				Node_Weight[neibor] += Top_Weight[node];
			}
		}
	}
	max_weight = 0;
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		j = Node_Degree[node];
		iSET[j][iSET_Size[j]] = NONE;
		Node_State[node] = PASSIVE;
		if (Node_Weight[node] > max_weight)
			max_weight = Node_Weight[node];

	}
	/*TEST*/
//	int _weight = 0;
//	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
//			Candidate_Stack[++i]) {
//		_weight = Top_Weight[node];
//		neibors = iSET[Node_Degree[node]];
//		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
//			if (node > neibor)
//				assert(is_adjacent(node, neibor));
//			else
//				assert(is_adjacent(neibor, node));
//			_weight += Top_Weight[neibor];
//		}
//		assert(_weight == Node_Weight[node]);
//	}
	/******/
	D1_B += ((float) nb_edge * 2 / nb_node / (nb_node - 1));
	G1_B++;
	return max_weight;

}
static void store_maximal_weighted_clique2() {
	memcpy(MaxCLQ_Stack, Clique_Stack, CUR_CLQ_SIZE * sizeof(int));

	MAX_CLQ_SIZE = CUR_CLQ_SIZE;

	MAX_CLQ_WEIGHT = MAX_CLQ_WEIGHT + CUR_NODE_WEIGHT;

	printf("C %8d |%8d |%8d %10d %10d %10d|%10d \n", Cursor_Stack[0] + 1,
			MAX_CLQ_WEIGHT, cut_ver, cut_inc, cut_iset, cut_satz,
			BRANCHING_COUNT);
	total_cut_ver += cut_ver;
	cut_ver = 0;
	total_cut_inc += cut_inc;
	cut_inc = 0;
	total_cut_iset += cut_iset;
	cut_iset = 0;
	total_cut_satz += cut_satz, cut_satz = 0;
	Last_Idx = CURSOR;
	ptr(Clique_Stack) = 0;
	Rollback_Point = NB_NODE + 1;
	CUR_CLQ_WEIGHT = 0;
}

static int init_for_me(int start, int *segment_counter, int *where) {
	int i, j, k, t, node;
	int max_weight = 0, total_weight = 0;

	max_weight = compute_subgraphs_weight(start);
	memset(segment_counter, 0, (max_weight + 1) * sizeof(int));
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Vertex_UB[i] = node;

		total_weight += Top_Weight[node];

		segment_counter[Node_Weight[node]]++;

	}
	Vertex_UB[i] = DELIMITER;

	//assert(total_weight >= max_weight && max_weight > 0);

	j = start;
	for (i = 0; i <= max_weight; i++) {
		k = segment_counter[i];
		segment_counter[i] = j;
		j += k;
	}

	for (node = Vertex_UB[i = start]; node != DELIMITER; node =
			Vertex_UB[++i]) {
		t = segment_counter[Node_Weight[node]]++;
		Candidate_Stack[t] = node;
		where[node] = t;
	}

	for (i = max_weight; i > 0; i--) {
		segment_counter[i] = segment_counter[i - 1];
	}
	segment_counter[0] = start;

	return total_weight;
}

static float compute_subgraph_density(int start) {
	int i = start, node, neibor, *neibors;
	int nb_node = 0, nb_edge = 0;

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Node_State[node] = 99;
		nb_node++;
	}
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (Node_State[neibor] == 99) {
				nb_edge++;
			}
		}
	}

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Node_State[node] = PASSIVE;
	}
	return ((float) nb_edge * 2 / nb_node / (nb_node - 1));;
}

static int compute_subgraph_degree(int start) {
	int i = start, j = 0, node, neibor, *neibors, max_degree = 0;
	int nb_node = 0, nb_edge = 0;

	j = 0;
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Node_Weight[node] = Top_Weight[node];
		Node_State[node] = ACTIVE;
		Node_Degree[node] = 0;
		iSET_Size[node] = j;
		j++;
	}
	nb_node = j;
	N1_B = nb_node;

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (Node_State[neibor] == ACTIVE) {
				nb_edge++;
				iSET[iSET_Size[node]][Node_Degree[node]++] = neibor;
				iSET[iSET_Size[neibor]][Node_Degree[neibor]++] = node;
				Node_Weight[node] += Top_Weight[neibor];
				Node_Weight[neibor] += Top_Weight[node];
			}
		}
	}
	max_degree = 0;
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		iSET[iSET_Size[node]][Node_Degree[node]] = NONE;
		Node_State[node] = PASSIVE;
		if (Node_Degree[node] > max_degree)
			max_degree = Node_Degree[node];

	}

	return max_degree;
}

static int reduce_first_level_subgraphs(int start) {
	int *degree_counter, *where;
	int end, p1, i, node = NONE, neibor, *neibors, t, j, h, k, weight = 0;
	//int max_degree = 0;
	//CUR_MAX_NODE = 0;
	Max_Degree = compute_subgraph_degree(start);

	where = Candidate_Stack + ptr(Candidate_Stack) + 1;
	degree_counter = Vertex_UB + ptr(Candidate_Stack) + 1;
	memset(degree_counter, 0, (Max_Degree + 1) * sizeof(int));

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		degree_counter[Node_Degree[node]]++;
		Vertex_UB[i] = node;
	}
	Vertex_UB[i] = DELIMITER;

	end = i - 1;
	j = start;
	for (i = 0; i <= Max_Degree; i++) {
		k = degree_counter[i];
		degree_counter[i] = j;
		j += k;
	}

	for (node = Vertex_UB[i = start]; node != DELIMITER; node =
			Vertex_UB[++i]) {
		t = degree_counter[Node_Degree[node]]++;
		Candidate_Stack[t] = node;
		where[node] = t;
	}

	for (i = Max_Degree; i > 0; i--) {
		degree_counter[i] = degree_counter[i - 1];
	}
	degree_counter[0] = start;

	p1 = start;
	while ((node = Candidate_Stack[p1]) != DELIMITER) {

		if (p1 < end
				&& Node_Degree[node] == Node_Degree[Candidate_Stack[p1 + 1]]) {
			degree_counter[Node_Degree[node]] = p1 + 1;
		}
		if (Node_Degree[node] == end - p1) {
			i = p1;
			while ((node = Candidate_Stack[i++]) != DELIMITER)
				weight += Top_Weight[node];

			if (weight == MAX_CLQ_WEIGHT) {
				ptr(Clique_Stack) = 0;
				push(Candidate_Stack[CURSOR], Clique_Stack);
				while ((node = Candidate_Stack[p1++]) != DELIMITER)
					push(node, Clique_Stack);
				store_maximal_weighted_clique2();

				for (node = Candidate_Stack[i = start]; node != DELIMITER;
						node = Candidate_Stack[++i]) {
					Node_Weight[node] = Top_Weight[node];
				}
				return TRUE;
			} else {
				break;
			}
		}

		neibors = iSET[iSET_Size[node]];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors))
			if (where[neibor] > p1) {
				t = where[neibor];
				h = degree_counter[Node_Degree[neibor]];
				k = Candidate_Stack[h];

				Candidate_Stack[h] = neibor;
				where[neibor] = h;
				Candidate_Stack[t] = k;
				where[k] = t;

				degree_counter[Node_Degree[neibor]]++;
				Node_Degree[neibor]--;
				Node_Weight[neibor] -= Top_Weight[node];
				if (Node_Degree[neibor]
						!= Node_Degree[Candidate_Stack[h - 1]]) {
					degree_counter[Node_Degree[neibor]] = h;
				}
			}
		p1++;
	}

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Vertex_UB[i] = Node_Weight[node];
		Node_Weight[node] = Top_Weight[node];
	}
	return FALSE;
}

static int reduce_first_level_subgraphs_new(int start) {
	int *segment_counter, *where, *neibors, neibor, max_weight = 0, new_weight,
			total_weight = 0;
	int p1, i, node = NONE, t, j, head, head_node;
	int max_core = 0, pre_weight, cur_weight;

	where = Candidate_Stack + ptr(Candidate_Stack) + 1;
	segment_counter = Vertex_UB + ptr(Candidate_Stack) + 1;

	total_weight = init_for_me(start, segment_counter, where);

	p1 = start;
	max_core = Node_Weight[Candidate_Stack[p1]];
	while ((node = Candidate_Stack[p1]) != DELIMITER) {

		cur_weight = Node_Weight[node];

		if (cur_weight > max_core) {
			max_core = cur_weight;
		}
		Vertex_UB[p1] = cur_weight;

		if (Candidate_Stack[p1 + 1] != DELIMITER
				&& cur_weight == Node_Weight[Candidate_Stack[p1 + 1]]) {
			segment_counter[cur_weight] = p1 + 1;
		}

		if (cur_weight == total_weight) {
			if (total_weight == MAX_CLQ_WEIGHT) {
				ptr(Clique_Stack) = 0;
				push(Candidate_Stack[CURSOR], Clique_Stack);
				while ((node = Candidate_Stack[p1++]) != DELIMITER)
					push(node, Clique_Stack);
				store_maximal_weighted_clique2();

				for (node = Candidate_Stack[i = start]; node != DELIMITER;
						node = Candidate_Stack[++i]) {
					Node_Weight[node] = Top_Weight[node];
				}
				return TRUE;
			} else {
				total_weight -= Top_Weight[node];

				while ((node = Candidate_Stack[++p1]) != DELIMITER) {
					Vertex_UB[p1] = total_weight;
					total_weight -= Top_Weight[node];
				}
				//assert(total_weight == 0);
			}
			break;
		}

		neibors = iSET[Node_Degree[node]];

		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if ((t = where[neibor]) > p1) {
				pre_weight = Node_Weight[neibor];
				Node_Weight[neibor] = Node_Weight[neibor] - Top_Weight[node];
				new_weight = Node_Weight[neibor];
				do {
					head = segment_counter[pre_weight];
					head_node = Candidate_Stack[head];

					Candidate_Stack[head] = neibor;
					where[neibor] = head;

					Candidate_Stack[t] = head_node;
					where[head_node] = t;

					segment_counter[pre_weight] = head + 1;

					pre_weight = Node_Weight[Candidate_Stack[head - 1]];

					t = head;

				} while (head > p1 + 1 && new_weight < pre_weight);

				if (head == p1 + 1
						|| new_weight
								> Node_Weight[Candidate_Stack[head - 1]]) {
					segment_counter[new_weight] = head;
				}
			}
		}
		total_weight -= Top_Weight[node];
		p1++;
	}
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Node_Weight[node] = Top_Weight[node];
	}
	if (max_core + CUR_NODE_WEIGHT > MAX_CLQ_WEIGHT) {
		CUR_MAX_NODE = 0;
		for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
				Candidate_Stack[++i]) {
			if (Vertex_UB[i] > MAX_CLQ_WEIGHT - CUR_NODE_WEIGHT)
				break;
		}
		j = start;
		for (node = Candidate_Stack[i]; node != DELIMITER; node =
				Candidate_Stack[++i]) {
			Vertex_UB[j] = Vertex_UB[i];
			Candidate_Stack[j++] = node;
			if (node > CUR_MAX_NODE)
				CUR_MAX_NODE = node;
		}
		Candidate_Stack[j] = DELIMITER;
		ptr(Candidate_Stack) = j + 1;
		NB_CANDIDATE = j - start;

		RT1 += (double) NB_CANDIDATE / (double) N1_B;
		if (NB_CANDIDATE > 0) {
			G1_A++;
			//D1_A += compute_subgraph_density(start);
		}
		return FALSE;
	} else {
		Vertex_UB[CURSOR]=max_core + CUR_NODE_WEIGHT;
		return TRUE;
	}
}

//static int reduce_first_level_subgraphs(int start) {
//	int *segment_counter, *where;
//	int end, p1, i, node = NONE, neibor, *neibors, t, j, k, head_node, head;
//	int max_weight, total_weight = 0, cur_weight = 0, max_core = 0, pre_weight,
//			new_weight;
//	//printf("{reduce_first_level_subgraphs:");
//	max_weight = compute_subgraphs_weight(start);
//	//assert(ptr(Candidate_Stack) + 1+max_weight+1<MAX_NODE*2);
//
//	where = Candidate_Stack + ptr(Candidate_Stack) + 1;
//	segment_counter = Vertex_UB + ptr(Candidate_Stack) + 1;
//	memset(segment_counter, 0, (max_weight + 1) * sizeof(int));
//
//	total_weight = 0;
//	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
//			Candidate_Stack[++i]) {
//		total_weight += Top_Weight[node];
//		segment_counter[Node_Weight[node]]++;
//		Vertex_UB[i] = node;
//	}
//	Vertex_UB[i] = DELIMITER;
//	assert(total_weight >= max_weight && max_weight > 0);
//	end = i - 1;
//
//	j = start;
//	for (i = 0; i <= max_weight; i++) {
//		k = segment_counter[i];
//		segment_counter[i] = j;
//		j += k;
//	}
//
//	for (node = Vertex_UB[i = start]; node != DELIMITER; node =
//			Vertex_UB[++i]) {
//		t = segment_counter[Node_Weight[node]]++;
//		Candidate_Stack[t] = node;
//		where[node] = t;
//	}
//
//	for (i = max_weight; i > 0; i--) {
//		segment_counter[i] = segment_counter[i - 1];
//	}
//	segment_counter[0] = start;
//
//	p1 = start;
//	max_core = 0;
//	while ((node = Candidate_Stack[p1]) != DELIMITER) {
//		cur_weight = Node_Weight[node];
//
//		if (cur_weight > max_core) {
//			max_core = cur_weight;
//		}
//		Vertex_UB[p1] = cur_weight;
//
//		if (p1 < end && cur_weight == Node_Weight[Candidate_Stack[p1 + 1]]) {
//			segment_counter[cur_weight] = p1 + 1;
//		}
//
//		if (cur_weight == total_weight) {
//			if (cur_weight == MAX_CLQ_WEIGHT) {
//				ptr(Clique_Stack) = 0;
//				push(Candidate_Stack[CURSOR], Clique_Stack);
//				while ((node = Candidate_Stack[p1++]) != DELIMITER)
//					push(node, Clique_Stack);
//				store_maximal_weighted_clique2();
//
//				for (node = Candidate_Stack[i = start]; node != DELIMITER;
//						node = Candidate_Stack[++i]) {
//					Node_Weight[node] = Top_Weight[node];
//				}
//				return TRUE;
//			} else {
//				total_weight -= Top_Weight[node];
//
//				while ((node = Candidate_Stack[++p1]) != DELIMITER) {
//					Vertex_UB[p1] = total_weight;
//					total_weight -= Top_Weight[node];
//				}
//			}
//			break;
//		}
//
//		neibors = iSET[Node_Degree[node]];
//		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors))
//			if ((t = where[neibor]) > p1) {
//				pre_weight = Node_Weight[neibor];
//				Node_Weight[neibor] -= Top_Weight[node];
//				new_weight = Node_Weight[neibor];
//				do {
//					head = segment_counter[pre_weight];
//					head_node = Candidate_Stack[head];
//
//					Candidate_Stack[head] = neibor;
//					where[neibor] = head;
//
//					Candidate_Stack[t] = head_node;
//					where[head_node] = t;
//
//					segment_counter[pre_weight] = head + 1;
//
//					pre_weight = Node_Weight[Candidate_Stack[head - 1]];
//
//					t = head;
//
//				} while (head > p1 + 1 && new_weight < pre_weight);
//
//				if (head == p1 + 1
//						|| new_weight
//								> Node_Weight[Candidate_Stack[head - 1]]) {
//					segment_counter[new_weight] = head;
//				}
//			}
//		total_weight -= Top_Weight[node];
//		p1++;
//	}
//	for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
//			Candidate_Stack[++i]) {
//		Node_Weight[node] = Top_Weight[node];
//	}
//	if (max_core + CUR_NODE_WEIGHT > MAX_CLQ_WEIGHT) {
//		CUR_MAX_NODE = 0;
//		for (node = Candidate_Stack[i = start]; node != DELIMITER; node =
//				Candidate_Stack[++i]) {
//			if (Vertex_UB[i] > MAX_CLQ_WEIGHT - CUR_NODE_WEIGHT)
//				break;
//		}
//		j = start;
//		for (node = Candidate_Stack[i]; node != DELIMITER; node =
//				Candidate_Stack[++i]) {
//			Vertex_UB[j] = Vertex_UB[i];
//			Candidate_Stack[j++] = node;
//			if (node > CUR_MAX_NODE)
//				CUR_MAX_NODE = node;
//		}
//		Candidate_Stack[j] = DELIMITER;
//		ptr(Candidate_Stack) = j + 1;
//		return FALSE;
//	} else {
//		Vertex_UB[CURSOR]=max_core + CUR_NODE_WEIGHT;
//		return TRUE;
//	}
//}
static int cut_by_inc_ub() {
	int i = CURSOR, neibor, max_weight=0,max = 0,*neibors;
	int node=Candidate_Stack[CURSOR];
	int start=ptr(Candidate_Stack);
	unsigned char * adj_list;
	NB_CANDIDATE=0;
	CUR_MAX_NODE=0;
	max_weight=CUR_NODE_WEIGHT;
	if(CUR_CLQ_SIZE==0) {
		neibors = Node_Neibors[node];
		CUR_MAX_NODE=*(neibors);
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			i=NB_NODE-neibor;
			if (max < Vertex_UB[i]) {
				max = Vertex_UB[i];
			}
			Vertex_UB[ptr(Candidate_Stack)] = Vertex_UB[i];

			push(neibor, Candidate_Stack);
			max_weight+=Top_Weight[neibor];
			NB_CANDIDATE++;
		}
	} else {
		adj_list=iMatrix(node);
		while(Candidate_Stack[i]!=DELIMITER)i--;
		for (neibor = Candidate_Stack[++i]; neibor != DELIMITER; neibor =
				Candidate_Stack[++i]) {
			if (neibor>0 && Matrix(adj_list,neibor)>0) {
				if (max < Vertex_UB[i]) {
					max = Vertex_UB[i];
				}
				Vertex_UB[ptr(Candidate_Stack)] = Vertex_UB[i];

				push(neibor, Candidate_Stack);
				max_weight+=Node_Weight[neibor];
				NB_CANDIDATE++;
			}
		}
	}
	push(DELIMITER, Candidate_Stack);
	if((max+CUR_NODE_WEIGHT+CUR_CLQ_WEIGHT<=MAX_CLQ_WEIGHT)||(CUR_CLQ_WEIGHT+max_weight<=MAX_CLQ_WEIGHT)) {
		cut_inc++;
		return TRUE;
	}
	if(NB_CANDIDATE==0){
		if(CUR_CLQ_WEIGHT+CUR_NODE_WEIGHT>MAX_CLQ_WEIGHT)
				store_maximal_weighted_clique();
		return TRUE;
	}
	if(CUR_CLQ_SIZE==0){
		if(NB_CANDIDATE<10&&cut_by_iset_less_vertices()==TRUE){
			cut_iset++;
			return TRUE;
		}else if(reduce_first_level_subgraphs(start)) {
			cut_inc++;
			return TRUE;
		} else if(REBUILD_MATRIX==TRUE || CUR_MAX_NODE >MAX_SUBGRAPH_SIZE){
			rebuild_matrix(start);
			REBUILD_MATRIX=TRUE;
		}
	}
	return FALSE;
}

static int find_3_clique(int node) {
	int neibor1, neibor2, neibor3, *neibors1, *neibors2, *neibors3;
	neibors1 = Node_Neibors[node];
	for (neibor1 = *neibors1; neibor1 != NONE; neibor1 = *(++neibors1)) {
		neibors2 = neibors1 + 1;
		for (neibor2 = *neibors2; neibor2 != NONE; neibor2 = *(++neibors2)) {
			if (is_adjacent(neibor1, neibor2) == TRUE) {
				neibors3 = neibors2 + 1;
				for (neibor3 = *neibors3; neibor3 != NONE; neibor3 =
						*(++neibors3)) {
					if (is_adjacent(neibor1, neibor3) == TRUE
							&& is_adjacent(neibor2, neibor3) == TRUE) {
						MaxCLQ_Stack[0] = Old_Name[node];
						MaxCLQ_Stack[1] = Old_Name[neibor1];
						MaxCLQ_Stack[2] = Old_Name[neibor2];
						MaxCLQ_Stack[3] = Old_Name[neibor3];
						MAX_CLQ_SIZE = 4;
						return TRUE;
					}
				}
			}
		}
	}
	return FALSE;
}

static void init_for_search_bak(int using_init_clique) {
	int i, node;
	int neibor, neibor2, *neibors, *neibors2;
	cut_ver = 0;
	cut_inc = 0;
	cut_iset = 0;
	cut_satz = 0;
	total_cut_ver = 0;
	total_cut_inc = 0;
	total_cut_iset = 0;
	total_cut_satz = 0;

	Branches_Nodes[0] = 0;
	Branches_Nodes[1] = 0;
	Branches_Nodes[2] = 0;
	Branches_Nodes[3] = 0;
	Branches_Nodes[4] = 0;
	Branches_Nodes[5] = 0;

	Last_Idx = NB_NODE;
	NB_BACK_CLIQUE = 0;
	MAX_CLQ_SIZE = 0;
	ptr(Clique_Stack) = 0;
	ptr(Cursor_Stack) = 0;
	Rollback_Point = 0;
	push(NB_NODE - INIT_CLQ_SIZE - 1, Cursor_Stack);
	MAX_CLQ_SIZE = INIT_CLQ_SIZE;
	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		node = Candidate_Stack[i];
		Vertex_UB[i] = Node_Degree[node] + 1;
		Node_State[node] = PASSIVE;
	}
	if (INIT_CLQ_SIZE == 3) {
		for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
			node = Candidate_Stack[i];
			if (Vertex_UB[i] > 3) {
				if (find_3_clique(node) == TRUE) {
					INIT_CLQ_SIZE = 4;
					break;
				} else {
					Vertex_UB[i] = 3;
				}
			}
		}
	}
	if (INIT_CLQ_SIZE == 4 && Vertex_UB[i] > 4) {
		for (; i < ptr(Candidate_Stack) - 1; i++) {
			node = Candidate_Stack[i];
			neibors = Node_Neibors[node];
			for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
				neibors2 = neibors + 1;
				for (neibor2 = *neibors2; neibor2 != NONE; neibor2 =
						*(++neibors2)) {
					if (is_adjacent(neibor, neibor2) == FALSE) {
						Vertex_UB[i]--;
						break;
					}
				}
				if (neibor2 != NONE)
					break;
			}
		}
	}
//	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
//		node = Candidate_Stack[i];
//		Vertex_UB[i] = Node_Degree[node] + 1;
//		Node_State[node] = PASSIVE;
//		if (INIT_CLQ_SIZE == 3 && Vertex_UB[i] > 3) {
//			if (find_3_clique(node) == TRUE) {
//				printf("FIND CLIQUE 4!\n");
//				INIT_CLQ_SIZE = 4;
//				Vertex_UB[i] = 4;
//			} else {
//				Vertex_UB[i] = 3;
//			}
//		}
//		if (INIT_CLQ_SIZE == 4 && Vertex_UB[i] == 5) {
//			neibors = Node_Neibors[node];
//			for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
//				neibors2 = neibors + 1;
//				for (neibor2 = *neibors2; neibor2 != NONE; neibor2 =
//						*(++neibors2)) {
//					if (is_adjacent(neibor, neibor2) == FALSE) {
//						Vertex_UB[i] = 4;
//						break;
//					}
//				}
//				if (Vertex_UB[i] == 4)
//					break;
//			}
//		}
//	}
//		if ((Vertex_UB[i] > INIT_CLQ_SIZE)
//				&& (Vertex_UB[i] - INIT_CLQ_SIZE <= 2)) {
//			neibors = Node_Neibors[node];
//			for (j = 1; j < Node_Degree[node]; j++) {
//				node1 = neibors[j - 1];
//				node2 = neibors[j];
//				neibors2 = Node_Neibors[node1];
//				for (neibor = *neibors2; neibor != NONE; neibor =
//						*(++neibors2)) {
//					if (neibor == node2) {
//						break;
//					}
//				}
//				if (neibor == NONE) {
//					Vertex_UB[i]--;
//					j++;
//				}
//				if (Vertex_UB[i] == INIT_CLQ_SIZE) {
//					success++;
//					break;
//				}
//			}
//
//		}

}

static void init_for_search() {
	int i, j, neibor, neibor2, *neibors, *neibors2;
	cut_ver = 0;
	cut_inc = 0;
	cut_iset = 0;
	cut_satz = 0;
	total_cut_ver = 0;
	total_cut_inc = 0;
	total_cut_iset = 0;
	total_cut_satz = 0;

	Branches_Nodes[0] = 0;
	Branches_Nodes[1] = 0;
	Branches_Nodes[2] = 0;
	Branches_Nodes[3] = 0;
	Branches_Nodes[4] = 0;
	Branches_Nodes[5] = 0;

	Last_Idx = NB_NODE;
	NB_BACK_CLIQUE = 0;

	MAX_CLQ_SIZE = 0;
	ptr(Clique_Stack) = 0;
	ptr(Cursor_Stack) = 0;
	Rollback_Point = 0;

	MAX_CLQ_WEIGHT = 0;
	CUR_CLQ_WEIGHT = 0;
	//	INIT_CLQ_WEIGHT = 0;

	if (INIT_CLQ_SIZE > 0) {
		//		for (i = 1; i <= INIT_CLQ_SIZE; i++) {
		//			MaxCLQ_Stack[i - 1] = Candidate_Stack[NB_NODE - i];
		//			INIT_CLQ_WEIGHT += Top_Weight[Candidate_Stack[NB_NODE - i]];
		//		}
		MAX_CLQ_SIZE = INIT_CLQ_SIZE;
		MAX_CLQ_WEIGHT = INIT_CLQ_WEIGHT;
	}
	push(NB_NODE, Cursor_Stack);
}

static void init_for_search_bak2(int using_init_clique) {
	int i, node;
	int neibor, neibor2, *neibors, *neibors2;
	cut_ver = 0;
	cut_inc = 0;
	cut_iset = 0;
	cut_satz = 0;
	total_cut_ver = 0;
	total_cut_inc = 0;
	total_cut_iset = 0;
	total_cut_satz = 0;

	Branches_Nodes[0] = 0;
	Branches_Nodes[1] = 0;
	Branches_Nodes[2] = 0;
	Branches_Nodes[3] = 0;
	Branches_Nodes[4] = 0;
	Branches_Nodes[5] = 0;

	Last_Idx = NB_NODE;
	NB_BACK_CLIQUE = 0;
	MAX_CLQ_SIZE = 0;
	ptr(Clique_Stack) = 0;
	ptr(Cursor_Stack) = 0;
	Rollback_Point = 0;
	push(NB_NODE - INIT_CLQ_SIZE - 1, Cursor_Stack);
	MAX_CLQ_SIZE = INIT_CLQ_SIZE;
	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		node = Candidate_Stack[i];
		Vertex_UB[i] = Node_Degree[node] + 1;
		if (INIT_CLQ_SIZE == 3 && Vertex_UB[i] > 3) {
			if (find_3_clique(node) == TRUE) {
				printf("I improve the initial clique to 4\n");
				INIT_CLQ_SIZE = 4;
			} else {
				Vertex_UB[i] = 3;
			}
		}
		if (INIT_CLQ_SIZE == 4 && Vertex_UB[i] == 5) {
			neibors = Node_Neibors[node];
			for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
				neibors2 = neibors + 1;
				for (neibor2 = *neibors2; neibor2 != NONE; neibor2 =
						*(++neibors2)) {
					if (is_adjacent(neibor, neibor2) == FALSE) {
						Vertex_UB[i] = 4;
						break;
					}
				}
				if (Vertex_UB[i] == 4)
					break;
			}
		}
	}
}

static void allocate_memory() {
	int i;
	int size = MAX_SUBGRAPH_SIZE + 1;
	Second_Name = (int *) malloc(size * sizeof(int));
	iSET = (int **) malloc(size * sizeof(int *));
	iSET[0] = (int *) malloc(size * size * sizeof(int));
	for (i = 1; i < size; i++) {
		iSET[i] = iSET[i - 1] + size;
	}
	iSET_Size = (int *) malloc((NB_NODE + 1) * sizeof(int));
	iSET_Weight = (int *) malloc(size * sizeof(int));
	iSET_Tested = (char *) malloc(size * sizeof(char));
	//MaxCLQ_Stack = (int *) malloc(size * sizeof(int));
	Clique_Stack = (int *) malloc(size * sizeof(int));
	memset(iSET_Tested, 0, size * sizeof(char));

	/* data structures for maxsat reasoning*/
	IS = (int **) malloc(size * sizeof(int *));
	IS_HEAD = Node_Degree;
	UNIT_STACK = (int *) malloc((size) * sizeof(int));
	TOP_UNIT_STACK = (int *) malloc((size) * sizeof(int));
	NEW_UNIT_STACK = (int *) malloc((size) * sizeof(int));
	REASON_STACK = (int *) malloc((size) * 10 * sizeof(int));
	/***************/

	//allocate_memory_for_maxsat();
}

static void search_maxclique(double cutoff, int using_init_clique) {
	int node;

	BRANCHING_COUNT = 0;
	if (using_init_clique == TRUE) {
		printf(
				"C  ----------------------------------------------------------------------------------\n");
		printf(
				"C    Index |  Weight |NB_Vertex  NB_IncUB    NB_Iset  NB_MaxSat|  NB_Branch      time\n");
	}
	while (CURSOR> 0) {
	    SEARCH_TIME = get_utime() - READ_TIME - INIT_TIME;
	    if (SEARCH_TIME >= cutoff){
	        printf("Not solving to optimality; user time limit\n");
	        break;
	    }

		node=Candidate_Stack[--CURSOR];

		if(CUR_CLQ_SIZE>0 && node>0)
		continue;

		if(node==DELIMITER) {
			ptr(Candidate_Stack)=CURSOR+1;
			ptr(Cursor_Stack)--;
			ptr(Clique_Stack)--;
			CUR_CLQ_WEIGHT-=Top_Weight[Clique_Stack[ptr(Clique_Stack)]];
			Vertex_UB[CURSOR]=MAX_CLQ_WEIGHT-CUR_CLQ_WEIGHT;
		} else {
			if(node<0) {
				node=-node;
				Candidate_Stack[CURSOR]=-Candidate_Stack[CURSOR];
			}
			if(CUR_CLQ_SIZE==0) {
				CUR_NODE_WEIGHT=Top_Weight[node];
				UPPER_WEIGHT_BOUND=MAX_CLQ_WEIGHT+CUR_NODE_WEIGHT;
			} else
			CUR_NODE_WEIGHT=Node_Weight[node];

			if(Vertex_UB[CURSOR] <= MAX_CLQ_WEIGHT - CUR_CLQ_WEIGHT) {
				cut_ver++;
			}
			else {
				BRANCHING_COUNT++;
				Rollback_Point=ptr(Candidate_Stack);
				if(cut_by_inc_ub()==TRUE

				||cut_by_iset_last_renumber()==TRUE
#ifdef MaxSAT
			|| (iSET_COUNT>0 && cut_by_inc_maxsat_reasoning()==TRUE)
#endif
			) {
				ptr(Candidate_Stack)=Rollback_Point;
			} else {
				CUR_CLQ_WEIGHT+=CUR_NODE_WEIGHT;
				if (CUR_CLQ_SIZE == 0)
				push(node, Clique_Stack);
				else
				push(Second_Name[node], Clique_Stack);
				push(Branching_Point,Cursor_Stack);
			}
		}
	}
}
	if (using_init_clique == TRUE) {
		SEARCH_TIME = get_utime() - READ_TIME - INIT_TIME;
		printf(
				"C  ----------------------------------------------------------------------------------\n");
		printf("C %8d |%8d |%8d %10d %10d %10d|%10d %10.2lf \n", CURSOR+1,MAX_CLQ_WEIGHT,cut_ver,cut_inc, cut_iset, cut_satz,BRANCHING_COUNT,SEARCH_TIME);
		total_cut_ver += cut_ver;
		total_cut_inc += cut_inc;
		total_cut_iset += cut_iset;
		total_cut_satz += cut_satz;
		printf(
				"C  ----------------------------------------------------------------------------------\n");
		printf("C %8d |%8d |%8d %10d %10d %10d|%10d %10.2lf\n", CURSOR+1,MAX_CLQ_WEIGHT,total_cut_ver,total_cut_inc, total_cut_iset, total_cut_satz,BRANCHING_COUNT,SEARCH_TIME);
	}
	;
}

static void check_maxw_clique() {
	int i, j, weight = 0, node1, node2;
	if (INIT_CLQ_SIZE < MAX_CLQ_SIZE) {
		for (i = 0; i < MAX_CLQ_SIZE; i++) {
			weight += Top_Weight[MaxCLQ_Stack[i]];
		}
	} else {
		for (i = 0; i < MAX_CLQ_SIZE; i++) {
			weight += Top_Weight[MaxCLQ_Stack[i]];
		}
	}
	assert(weight == MAX_CLQ_WEIGHT);
	for (i = 0; i < MAX_CLQ_SIZE; i++) {
		node1 = MaxCLQ_Stack[i];
		for (j = i + 1; j < MAX_CLQ_SIZE; j++) {
			node2 = MaxCLQ_Stack[j];
			if (node1 > node2) {
				assert(is_adjacent(node1, node2) == TRUE);
			} else {
				assert(is_adjacent(node2, node1) == TRUE);
			}
		}
	}
}

static void printMaxClique() {
	int i, weight = 0;
	printf("M ");
	if (INIT_CLQ_SIZE < MAX_CLQ_SIZE) {
		for (i = 0; i < MAX_CLQ_SIZE; i++) {
			printf("%d ", Old_Name[MaxCLQ_Stack[i]]);
		}
	} else {
		for (i = 0; i < MAX_CLQ_SIZE; i++) {
			printf("%d ", MaxCLQ_Stack[i]);
		}
	}
	printf("\n");
}

static void build_init_matrix() {
	int node, neibor, *neibors;
	MATRIX_ROW_WIDTH = MAX_SUBGRAPH_SIZE / 8 + 1;
	Adj_Matrix = (unsigned char *) malloc(
			(MAX_SUBGRAPH_SIZE + 1) * MATRIX_ROW_WIDTH * sizeof(char));

	memset(Adj_Matrix, 0,
			(MAX_SUBGRAPH_SIZE + 1) * MATRIX_ROW_WIDTH * sizeof(char));

	for (node = 1; node <= MAX_SUBGRAPH_SIZE; node++) {
		Second_Name[node] = node;
		Node_Weight[node] = Top_Weight[node];
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			SET_EDGE(node, neibor);
			SET_EDGE(neibor, node);
		}
	}
}

static int * Adj_List;
#define New_Name Node_Degree
static int search_in_2_k_core_graph() {
	int i = 0, node, neibor1, neibor2, neibor, *neibors, find = FALSE;
	for (i = 0; i < NB_NODE; i++) {
		node = Candidate_Stack[i];
		if (Node_Degree[node] == 2) {
			neibor1 = Node_Neibors[node][0];
			neibor2 = Node_Neibors[node][1];

			neibors = Node_Neibors[neibor1];
			for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
				if (neibor == neibor2) {
					find = TRUE;
					break;
				}
			}
			if (find == TRUE) {
				MaxCLQ_Stack[0] = Old_Name[node];
				MaxCLQ_Stack[1] = Old_Name[neibor1];
				MaxCLQ_Stack[2] = Old_Name[neibor2];
				INIT_CLQ_SIZE = 3;
				MAX_CLQ_SIZE = 3;
				break;
			}
		} else if (Node_Degree[node] > 2) {
			break;
		}
	}
	if (find == TRUE) {
		printf("I find maximum clique in initial phase.");
		return TRUE;
	} else if (i == NB_NODE) {
		printf("I find maximum clique in initial phase.");
		MAX_CLQ_SIZE = 2;
		return TRUE;
	} else {
		return FALSE;
	}
}
//static void search_in_4_k_core_graph() {
//	int i = 0, node, neibor1, neibor2, neibor, *neibors, find = FALSE;
//	for (i = 0; i < NB_NODE; i++) {
//		node = Candidate_Stack[i];
//		if (Node_Degree[node] == 4) {
//			neibor1 = Node_Neibors[node][0];
//			neibor2 = Node_Neibors[node][1];
//
//			neibors = Node_Neibors[neibor1];
//			for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
//				if (neibor == neibor2) {
//					find = TRUE;
//					break;
//				}
//			}
//			if (find == TRUE)
//				break;
//		} else if (Node_Degree[node] > 2) {
//			break;
//		}
//	}
//	if (find == TRUE) {
//		printf("the max clique is 3\n ");
//	} else if (i == NB_NODE) {
//		printf("the max clique is 2\n ");
//	} else {
//		printf(" failure!");
//	}
//}

static void free_block() {
	int i = 0;
	for (i = 0; i < BLOCK_COUNT; i++)
		free(BLOCK_LIST[i]);
}

static void reduce_instance_0() {
	int i, j, nb, node, *neibors, *neibors2, *addr;
	MAX_SUBGRAPH_SIZE = 0;
//	j = 0;
	for (node = Candidate_Stack[i = 0]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Node_State[node] = ACTIVE;
//		if (CORE_NO[i] < INIT_CLQ_WEIGHT) {
//			Node_State[node] = PASSIVE;
//		} else {
//			Vertex_UB[j] = CORE_NO[i];
//			Candidate_Stack[j++] = node;
//			Node_State[node] = ACTIVE;
//		}
	}
//	NB_NODE = j;
//	Candidate_Stack[j] = DELIMITER;
//	ptr(Candidate_Stack) = j + 1;
	Old_Name = (int *) malloc((NB_NODE + 1) * sizeof(int));
	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		Old_Name[NB_NODE - i] = Candidate_Stack[i];
		Node_Weight[NB_NODE - i] = Top_Weight[Candidate_Stack[i]];
		New_Name[Candidate_Stack[i]] = NB_NODE - i;
		Candidate_Stack[i] = NB_NODE - i;
	}

	NB_EDGE = 0;
	for (i = NB_NODE; i > 0; i--) {
		Top_Weight[i] = Node_Weight[i];
		neibors = Node_Neibors[Old_Name[i]];
		neibors2 = neibors;
		nb = 0;
		for (node = *neibors; node != NONE; node = *(++neibors)) {
			if (Node_State[node] == ACTIVE && New_Name[node] < i) {
				(*neibors2) = New_Name[node];
				neibors2++;
				nb++;
			}
		}
		(*neibors2) = NONE;
		NB_EDGE += nb;
		qsort(Node_Neibors[Old_Name[i]], nb, sizeof(int), int_cmp_desc);
	}

	Adj_List = (int *) malloc((NB_EDGE + NB_NODE) * sizeof(int));
	addr = Adj_List;

	if (Adj_List == NULL ) {
		printf("can't allocate memory for Adj_List!\n");
		exit(0);
	}

	for (i = NB_NODE; i > 0; i--) {
		Node_Degree[i] = 0;
		Node_State[i] = PASSIVE;
		neibors = Node_Neibors[Old_Name[i]];
		for (node = *neibors; node != NONE; node = *(++neibors)) {
			*(addr++) = node;
			Node_Degree[i]++;
		}
		*(addr++) = NONE;
		if (Node_Degree[i] > MAX_SUBGRAPH_SIZE)
			MAX_SUBGRAPH_SIZE = Node_Degree[i];
	}
	free_block();
	Node_Neibors[NB_NODE] = Adj_List;
	for (i = NB_NODE - 1; i > 0; i--) {
		Node_Neibors[i] = Node_Neibors[i + 1] + Node_Degree[i + 1] + 1;
	}

	printf("I the reduced graph #node %d #edge %d #density %9.8f\n", NB_NODE,
			NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
	printf("I the largest subgraph is %d\n", MAX_SUBGRAPH_SIZE);

}

static void reduce_instance_for_weight() {
	int i, j, nb, node, *neibors, *neibors2, *addr;
	MAX_SUBGRAPH_SIZE = 0;
	i = 0;
	while (Vertex_UB[i] <= INIT_CLQ_WEIGHT) {
		Node_State[Candidate_Stack[i]] = PASSIVE;
		i++;
	}
	j = 0;

	for (node = Candidate_Stack[i]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		Vertex_UB[j] = Vertex_UB[i];
		Candidate_Stack[j++] = node;
		Node_State[node] = ACTIVE;
	}
	NB_NODE = j;

	Candidate_Stack[j] = DELIMITER;
	ptr(Candidate_Stack) = j + 1;
	Old_Name = (int *) malloc((NB_NODE + 1) * sizeof(int));
	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		Old_Name[NB_NODE - i] = Candidate_Stack[i];
		Node_Weight[NB_NODE - i] = Top_Weight[Candidate_Stack[i]];
		New_Name[Candidate_Stack[i]] = NB_NODE - i;
		Candidate_Stack[i] = NB_NODE - i;
	}

	NB_EDGE = 0;
	for (i = NB_NODE; i > 0; i--) {
		Top_Weight[i] = Node_Weight[i];
		neibors = Node_Neibors[Old_Name[i]];
		neibors2 = neibors;
		nb = 0;
		for (node = *neibors; node != NONE; node = *(++neibors)) {
			if (Node_State[node] == ACTIVE && New_Name[node] < i) {
				(*neibors2) = New_Name[node];
				neibors2++;
				nb++;
			}
		}
		(*neibors2) = NONE;
		NB_EDGE += nb;
		qsort(Node_Neibors[Old_Name[i]], nb, sizeof(int), int_cmp_desc);
	}

	Adj_List = (int *) malloc((NB_EDGE + NB_NODE) * sizeof(int));
	addr = Adj_List;

	if (Adj_List == NULL ) {
		printf("can't allocate memory for Adj_List!\n");
		exit(0);
	}

	for (i = NB_NODE; i > 0; i--) {
		Node_Degree[i] = 0;
		Node_State[i] = PASSIVE;
		neibors = Node_Neibors[Old_Name[i]];
		for (node = *neibors; node != NONE; node = *(++neibors)) {
			*(addr++) = node;
			Node_Degree[i]++;
		}
		*(addr++) = NONE;
		if (Node_Degree[i] > MAX_SUBGRAPH_SIZE)
			MAX_SUBGRAPH_SIZE = Node_Degree[i];
	}
	free_block();
	Node_Neibors[NB_NODE] = Adj_List;
	for (i = NB_NODE - 1; i > 0; i--) {
		Node_Neibors[i] = Node_Neibors[i + 1] + Node_Degree[i + 1] + 1;
	}

	printf("I the reduced graph #node %d #edge %d #density %9.8f \n", NB_NODE,
			NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
	N0_A = NB_NODE;
	D0_A = ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1));
	printf("I the largest subgraph is %d\n", MAX_SUBGRAPH_SIZE);
	INIT_TIME = get_utime() - READ_TIME;
	printf("I the initial time is %4.2lf \n", INIT_TIME);
}

static void reduce_instance_for_degree() {
	int i, j, nb, node, *neibors, *neibors2, *addr;
	MAX_SUBGRAPH_SIZE = 0;
	N0_B = NB_NODE;
	j = 0;
	i = 0;
	for (node = Candidate_Stack[i]; node != DELIMITER; node =
			Candidate_Stack[++i]) {
		if (Node_Weight[node] <= INIT_CLQ_WEIGHT) {
			Node_State[node] = PASSIVE;
		} else {
			Candidate_Stack[j++] = node;
			Node_State[node] = ACTIVE;
		}
	}
	NB_NODE = j;
	Candidate_Stack[j] = DELIMITER;
	ptr(Candidate_Stack) = j + 1;

	Old_Name = (int *) malloc((NB_NODE + 1) * sizeof(int));

	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		Old_Name[NB_NODE - i] = Candidate_Stack[i];
		Node_Weight[NB_NODE - i] = Top_Weight[Candidate_Stack[i]];
		New_Name[Candidate_Stack[i]] = NB_NODE - i;
		Candidate_Stack[i] = NB_NODE - i;
	}

	NB_EDGE = 0;
	for (i = NB_NODE; i > 0; i--) {
		Vertex_UB[NB_NODE - i] = Node_Weight[i];
		Top_Weight[i] = Node_Weight[i];
		neibors = Node_Neibors[Old_Name[i]];
		neibors2 = neibors;

		nb = 0;
		for (node = *neibors; node != NONE; node = *(++neibors)) {
			if (Node_State[node] == ACTIVE && New_Name[node] < i) {
				(*neibors2) = New_Name[node];
				Vertex_UB[NB_NODE - i] += Node_Weight[New_Name[node]];
				neibors2++;
				nb++;
			}
		}
		(*neibors2) = NONE;
		NB_EDGE += nb;
		qsort(Node_Neibors[Old_Name[i]], nb, sizeof(int), int_cmp_desc);
	}

	Adj_List = (int *) malloc((NB_EDGE + NB_NODE) * sizeof(int));
	addr = Adj_List;

	if (Adj_List == NULL ) {
		printf("can't allocate memory for Adj_List!\n");
		exit(0);
	}

	for (i = NB_NODE; i > 0; i--) {
		Node_Degree[i] = 0;
		Node_State[i] = PASSIVE;
		neibors = Node_Neibors[Old_Name[i]];
		for (node = *neibors; node != NONE; node = *(++neibors)) {
			*(addr++) = node;
			Node_Degree[i]++;
		}
		*(addr++) = NONE;
		if (Node_Degree[i] > MAX_SUBGRAPH_SIZE)
			MAX_SUBGRAPH_SIZE = Node_Degree[i];
	}
	free_block();
	Node_Neibors[NB_NODE] = Adj_List;
	for (i = NB_NODE - 1; i > 0; i--) {
		Node_Neibors[i] = Node_Neibors[i + 1] + Node_Degree[i + 1] + 1;
	}

	printf("I the reduced graph #node %d #edge %d #density %9.8f \n", NB_NODE,
			NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
	N0_A = NB_NODE;
	D0_A = ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1));
	printf("I the largest subgraph is %d\n", MAX_SUBGRAPH_SIZE);
	INIT_TIME = get_utime() - READ_TIME;
	printf("I the initial time is %4.2lf \n", INIT_TIME);
}

void print_version() {
	printf("c Hello! I am WLMC build at %s %s.\n", __TIME__, __DATE__);
#ifdef MaxSAT
	printf("c compiling with MaxSAT Reasoning.\n");
#endif
	return;
}

static void check_result(char *input_file, char *result_file) {
	char * fileStyle = strrchr(input_file, '.') + 1;
	if (strcmp(fileStyle, "clq") == 0) {
		read_graph_node_node(input_file, 1);
	} else if (strcmp(fileStyle, "edges") == 0) {
		read_graph_node_node(input_file, 2);
	} else if (FORMAT == 1) {
		read_graph_node_node(input_file, 1);
	} else if (FORMAT == 2) {
		read_graph_node_node(input_file, 2);
	} else {
		read_graph_node_node(input_file, 1);
	}
	printf("R Instance Information: #node=%d #edge=%d density=%9.8f\n", NB_NODE,
			NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
	check_clique_in_result_file(result_file);

}

void set_node_weight() {
	int node;
	Max_Weight = -1;
	for (node = 1; node <= NB_NODE; node++) {
		Top_Weight[node] = node % Weight_Mod + 1;
		if (Top_Weight[node] > Max_Weight)
			Max_Weight = Top_Weight[node];
	}
}

static int cmp_degree(const void * a, const void * b) {
	return Node_Degree[*((int *) a)] - Node_Degree[*((int *) b)];
}

void sort_node_by_weight_degree() {
	int i, j, k, t, node;
	//int *where = Candidate_Stack + NB_NODE + 1;
	int * weight_counter = Vertex_UB + NB_NODE + 1;
	memset(weight_counter, 0, (Max_Weight + 1) * sizeof(int));
	INIT_CLQ_SIZE = 0;
	printf("I computing initial vertex weight ordering...\n");
	for (node = 1; node <= NB_NODE; node++) {
		weight_counter[Top_Weight[node]]++;
	}
	j = 0;
	for (i = 1; i <= Max_Weight; i++) {
		k = weight_counter[i];
		weight_counter[i] = j;
		j += k;
	}

	for (node = 1; node <= NB_NODE; node++) {
		t = weight_counter[Top_Weight[node]]++;
		Candidate_Stack[t] = node;
	}
	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;
	/*check*/
//	for (i = 0; i < ptr(Candidate_Stack) - 2; i++) {
//		assert(
//				Top_Weight[Candidate_Stack[i]]
//						<= Top_Weight[Candidate_Stack[i + 1]]);
//	}
//	qsort(Candidate_Stack, NB_NODE, sizeof(int), int_cmp);
//	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
//		assert(Candidate_Stack[i] == NB_NODE - i);
//	}
//	return;
	/*end check*/
	j = 0;
	for (i = 1; i <= Max_Weight; i++) {
		qsort(Candidate_Stack + j, weight_counter[i] - weight_counter[i - 1],
				sizeof(int), cmp_degree);
		j = weight_counter[i];
	}

	Vertex_UB[ptr(Candidate_Stack) - 1] = 0;
	for (i = ptr(Candidate_Stack) - 2; i >= 0; i--) {
		Vertex_UB[i] = Vertex_UB[i + 1] + Top_Weight[Candidate_Stack[i]];
	}

	/*check*/
//	int node1, node2;
//	for (i = 0; i < ptr(Candidate_Stack); i++) {
//		node1 = Candidate_Stack[i];
//		node2 = Candidate_Stack[i + 1];
//		if (node1 == DELIMITER || node2 == DELIMITER)
//			break;
//
//		assert(Top_Weight[node1] <= Top_Weight[node2]);
//		if (Top_Weight[node1] == Top_Weight[node2])
//			assert(Node_Degree[node1] <= Node_Degree[node2]);
//	}
//	qsort(Candidate_Stack, NB_NODE, sizeof(int), int_cmp);
//	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
//		assert(Candidate_Stack[i] == NB_NODE - i);
//	}
}

//void parse_parmerters(int argc, char *argv[]) {
//	int i;
//	if (argc > 3) {
//		for (i = 2; i < argc; i++) {
//			if (strcmp(argv[i], "-o") == 0)
//				sscanf(argv[++i], "%d", &INIT_ORDERING);
//			else if (strcmp(argv[i], "-f") == 0)
//				sscanf(argv[++i], "%d", &FORMAT);
//			else if (strcmp(argv[i], "-check") == 0) {
//				check_result(argv[1], argv[i + 1]);
//			} else if (strcmp(argv[i], "-i") == 0) {
//				sscanf(argv[++i], "%d", &START_MAXSAT_THD);
//			} else if (strcmp(argv[i], "-w") == 0) {
//				sscanf(argv[++i], "%d", &Weight_Mod);
//			}
//		}
//	}
//	printf("# begin searching on %s ...\n", argv[1]);
//	printf("I INIT_ORDERING=%d FORMAT=%d Weight_Mod=%d\n", INIT_ORDERING,
//			FORMAT, Weight_Mod);
//}




//int main(int argc, char *argv[]) {

int wlmc(int NB_NODE1, int NB_EDGE1, double cutoff, int** AdjacentList, int* Node_Degree1, int* Node_Weight1, int* Node_Bound1){

    NB_NODE = NB_NODE1;
    NB_EDGE = NB_EDGE1;

    READ_TIME = get_utime();

    Node_Neibors = (int **) malloc((NB_NODE + 1) * sizeof(int *));
	allocate_memory_for_adjacency_list(NB_NODE, NB_EDGE, 0);
    for (int i = 0; i < NB_NODE; i++){
        Node_Degree[i+1] = Node_Degree1[i];
        Node_Weight[i+1] = Node_Bound1[i];
        Top_Weight[i+1] = Node_Weight1[i];
        Node_Neibors[i+1] = (int *) malloc((Node_Degree[i+1]+1) * sizeof(int));
        for (int j = 0u; j < Node_Degree[i+1]; ++j){
            Node_Neibors[i+1][j] = AdjacentList[i][j] + 1;
        }
        Node_Neibors[i+1][Node_Degree[i+1]] = NONE;
    }

	int ret = 0;
	FORMAT = 1;
	INIT_ORDERING = 1;
//	print_version1();
//	parse_parmerters(argc, argv);
//	clear_structures();

    sort_by_degree_degeneracy_ordering();
    reduce_instance_for_degree();

    allocate_memory();
    build_init_matrix();
    init_for_search();
    search_maxclique(cutoff, TRUE);
    //check_maxw_clique();
//    printMaxClique();

//	printf(
//			">>%s |V| %d |E| %d density %0.8lf kcore %d max_weight %d tree %d read_time %4.2lf init_time %4.2lf search_time %4.2lf total %4.2lf \\\\\n",
//			File_Name, NB_NODE_O, NB_EDGE_O,
//			((float) NB_EDGE_O * 2 / NB_NODE_O / (NB_NODE_O - 1)), K_CORE_G + 1,
//			MAX_CLQ_WEIGHT, BRANCHING_COUNT, READ_TIME, INIT_TIME, SEARCH_TIME,
//			READ_TIME + INIT_TIME + SEARCH_TIME);

//	return TRUE;
    return MAX_CLQ_WEIGHT;
}

