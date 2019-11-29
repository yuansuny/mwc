/******************************************************************************************/
/* Copyright 2017 (c) Hua Jiang & Chu-Min Li                                               */
/*                                                                                        */
/* This is a software for finding a maximum weight clique in an undirected graph          */
/* or to prove the optimality of a maximum weight clique in an undirected graph           */

/* It is provided for research purpose.                                                   */
/* For all other purposes, please contact Hua Jiang (jh_hgt@163.com)                      */
/* To compile the software use command: make, OR gcc -O3 -DMaxSAT TSM-Release.c -o tsm-mwc*/
/*                                                                                        */
/* For solving a graph, please use command:                                               */
/*                        ./tsm-mwc *.clq (*.mtx, *.edges, *.wclq)                        */
/******************************************************************************************/

/*
 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.
 */

//#define NDEBUG
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
#define UNASSIGNED 2
#define P_TRUE 1
#define P_FALSE 0
#define NULL_REASON -1
#define NO_REASON -3
#define CONFLICT -1978
#define MAX_NODE 1000000
#define max_expand_depth 100000
#define STACK_LENGTH (MAX_NODE*2)
#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item
#define ptr(stack) stack ## _fill_pointer
#define is_neibor(i,j) matrice[i][j]

#define CUR_CLQ_SIZE Clique_Stack_fill_pointer
#define CURSOR Cursor_Stack[Cursor_Stack_fill_pointer-1]
#define MIN(a,b) a<=b?a:b
#define BIT_MAP_SIZE 4097
#define Node_Reason Node_Degree

#define SET_EDGE(row,col) ((*(Adj_Matrix + (row)* MATRIX_ROW_WIDTH + ((col) >> 3))) |= (1 << ((col) & 7)))
#define GET_EDGE(row,col) ((*(Adj_Matrix + (row)* MATRIX_ROW_WIDTH + ((col) >> 3))) & (1 << ((col) & 7)))

#define iMatrix(i) (Adj_Matrix+(i)*MATRIX_ROW_WIDTH)
#define Matrix(i,j) ((*((i) + ((j) >> 3))) & (1 << ((j) & 7)))

static int * Adj_List;
#define New_Name Node_Degree

static int FORMAT = 1, NB_NODE, NB_NODE_O, NB_EDGE, NB_EDGE_O, MAX_CLQ_SIZE, INIT_CLQ_SIZE, INIT_ORDERING, NB_BACK_CLIQUE, MATRIX_ROW_WIDTH, MATRIX_SIZE = 0, MAX_SUBGRAPH_SIZE, K_CORE_G = 0;

static long long MAX_CLQ_WEIGHT, CUR_CLQ_WEIGHT, INIT_CLQ_WEIGHT, OPT_CLQ_WEIGHT, MAX_ISET_WEIGHT, CUR_NODE_WEIGHT, UPPER_WEIGHT_BOUND;
static long long Max_Degree = 0;
static long long Node_Degree[MAX_NODE];
//static int Max_Weight = 0;
static long long Top_Weight[MAX_NODE];
static long long Node_Weight[MAX_NODE];
static char Node_Value[MAX_NODE];
int **Node_Neibors;

static int Candidate_Stack_fill_pointer = 0;
static long long Candidate_Stack[MAX_NODE * 2];
static long long Vertex_UB[MAX_NODE * 2];
static int Clique_Stack_fill_pointer;
static int *Clique_Stack, *MaxCLQ_Stack;
static int Cursor_Stack[max_expand_depth];
static int Cursor_Stack_fill_pointer = 0;
static int Weight_Mod = 200;
static unsigned char * Adj_Matrix;

static int iSET_COUNT = 0;
static long long iSET_TOTAL_WEIGHT = 0;
static int *iSET_Size;
static long long *iSET_Weight;
static char *iSET_Tested;
static long long **iSET;
static int NEW_NODE_IDX = 0, MAX_OLD_NODE = 0, MAX_ISET_COUNT = 0;
static int RESERVED_LENGTH = 100;
static int LARGE_WEIGHT = FALSE;

int threshold;
char* File_Name;
const char* resPath;
const char* dataPath;
static int rankVar[MAX_NODE];


/* the structures for maxsat reasoning*/

static struct iSET_State *IS;
static long long *iNode_TAIL;

struct iSET_State {
	char satisfied;
	char used;
	char involved;
	char active;
	int size;
	int topk;
	long long weight;  //int unassigned;
	long long t_weight;  //int unassigned;
	long long *nodes;
};

static long long *REASON_STACK;
static int REASON_STACK_fill_pointer = 0;
static int *UNIT_STACK;
static int UNIT_STACK_fill_pointer = 0;
//static int *TOP_UNIT_STACK;
//static int TOP_UNIT_STACK_fill_pointer = 0;
static int *NEW_UNIT_STACK;
static int NEW_UNIT_STACK_fill_pointer = 0;
static int *FIXED_NODES_STACK;
static int FIXED_NODES_STACK_fill_pointer = 0;
static int *SATISFIED_iSETS_STACK;
static int SATISFIED_iSETS_STACK_fill_pointer = 0;
static int *TOPK_REDUCED_STACK;
static int TOPK_REDUCED_STACK_fill_pointer = 0;

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

static int LAST_IN;

/*statistical data*/
static long long N0_B, N0_A, N1_B, G1_B = 0;
static double D0_B, D0_A, D1_B = 0;
/*****************/
static int * Init_Adj_List;
static int BLOCK_COUNT = 0;
static int *BLOCK_LIST[100];
static double READ_TIME, INIT_TIME, SEARCH_TIME;
static double get_utime() {
	struct rusage utime;
	getrusage(RUSAGE_SELF, &utime);
	return (double) (utime.ru_utime.tv_sec + (double) utime.ru_utime.tv_usec / 1000000);
}

//static void check_iset();

static int int_cmp_desc(const void * a, const void * b) {
	return *((int *) b) - *((int *) a);
}

static void free_block() {
	int i = 0;
	for (i = 0; i < BLOCK_COUNT; i++)
		free(BLOCK_LIST[i]);
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
	int i = 0, j, node, clique_size = 0, clique[10240], weight = 0;
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

		for (i = 0; i < clique_size; i++) {
			printf("%d ", clique[i]);
			weight += clique[i] % Weight_Mod + 1;
		}
		printf("\n");
		printf("  SIZE: %d\n", clique_size);
		printf("WEIGHT: %d\n", weight);

		for (i = 0; i < clique_size; i++) {
			for (j = i + 1; j < clique_size; j++) {
				if (is_adjacent(clique[i], clique[j]) == FALSE) {
					printf("find non-adjacent vertices: %d %d\n", clique[i], clique[j]);
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

static void allcoate_memory_for_adjacency_list(int nb_node, int nb_edge, int offset) {
	int i, block_size = 40960000, free_size = 0;
	Init_Adj_List = (int *) malloc((2 * nb_edge + nb_node) * sizeof(int));
	if (Init_Adj_List == NULL ) {
		for (i = 1; i <= NB_NODE; i++) {
			if (Node_Degree[i - offset] + 1 > free_size) {
				Node_Neibors[i] = (int *) malloc(block_size * sizeof(int));
				BLOCK_LIST[BLOCK_COUNT++] = Node_Neibors[i];
				free_size = block_size - (Node_Degree[i - offset] + 1);
			} else {
				Node_Neibors[i] = Node_Neibors[i - 1] + Node_Degree[i - 1 - offset] + 1;
				free_size = free_size - (Node_Degree[i - offset] + 1);
			}
		}
	} else {
		BLOCK_COUNT = 1;
		BLOCK_LIST[BLOCK_COUNT - 1] = Init_Adj_List;
		Node_Neibors[1] = Init_Adj_List;
		for (i = 2; i <= NB_NODE; i++) {
			Node_Neibors[i] = Node_Neibors[i - 1] + Node_Degree[i - 1 - offset] + 1;
		}
	}
}

static int read_graph_wclq_format(char *input_file) {
	int j, node = 1, l_node, r_node, nb_edge = 0, max_node = NONE, offset = 0;
	long long weight, max_weight = 0;
	char line[128], word[10];

	char rankfile[100];
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

    char filename[100];
    strcpy(filename,dataPath);
    strcat(filename,input_file);

	FILE* fp_in = fopen(filename, "r");
	if (fp_in == NULL ) {
		printf("R can not open file %s\n", filename);
		return FALSE;
	}

	printf("R reading wclq file  ...\n");

	memset(Node_Degree, 0, MAX_NODE * sizeof(long long));

	while (fgets(line, 127, fp_in) != NULL) {
		if (line[0] == 'v') {
			sscanf(line, "%s%d%lld", word, &node, &weight);
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
	assert(offset == 0);
	NB_NODE = max_node + offset;
	if (max_weight > INT_MAX)
		LARGE_WEIGHT = TRUE;
	else
		LARGE_WEIGHT = FALSE;

	if (NB_NODE > MAX_NODE) {
		printf("R the graph goes beyond the max size can be processed: %d\n", NB_NODE);
		exit(0);
	}

	Node_Neibors = (int **) malloc((NB_NODE + 1) * sizeof(int *));
	allcoate_memory_for_adjacency_list(NB_NODE, nb_edge, offset);
	memset(Node_Degree, 0, (NB_NODE + 1) * sizeof(long long));

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
					assert(LONG_MAX - Node_Weight[rankVar[l_node]] - Top_Weight[rankVar[r_node]] > 0);
					Node_Weight[rankVar[l_node]] += Top_Weight[rankVar[r_node]];
					assert(LONG_MAX - Node_Weight[rankVar[r_node]] - Top_Weight[rankVar[l_node]] > 0);
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
		if (Node_Weight[node] > max_weight)
			max_weight = Node_Weight[node];
	}
	if (max_weight > MAX_NODE) {
		LARGE_WEIGHT = TRUE;
//		printf("I reduce first level subgraphs is DISABLE\n");
	} else {
		LARGE_WEIGHT = FALSE;
//		printf("I reduce first level subgraphs is ENABLE\n");
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
	memset(Node_Degree, 0, MAX_NODE * sizeof(long long));
	while (fgets(line, 127, fp_in) != NULL ) {
		if ((format == 1 && line[0] == 'e') || (format == 2 && line[0] != '%')) {
			if (format == 1)
				sscanf(line, "%s%d%d", word, &l_node, &r_node);
			else
				sscanf(line, "%d%d", &l_node, &r_node);

			if (l_node + offset >= MAX_NODE || r_node + offset >= MAX_NODE) {
				printf("R the vertex index %d(%d) the limitation %d\n", l_node, r_node, MAX_NODE);
				exit(0);
			}

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

	//printf("R the graph size is %d\n", NB_NODE);

	for (node = 1; node <= NB_NODE; node++) {
		Top_Weight[node] = node % Weight_Mod + 1;
		//Top_Weight[node] = 1;
		Node_Weight[node] = Top_Weight[node];
	}

	Node_Neibors = (int **) malloc((NB_NODE + 1) * sizeof(int *));
	allcoate_memory_for_adjacency_list(NB_NODE, nb_edge, offset);
	memset(Node_Degree, 0, (NB_NODE + 1) * sizeof(long long));

	nb_edge = 0;
	fseek(fp_in, 0L, SEEK_SET);
	while (fgets(line, 127, fp_in) != NULL ) {
		if ((format == 1 && line[0] == 'e') || (format == 2 && line[0] != '%')) {
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
//	char * fileStyle = strrchr(input_file, '.') + 1;
//	if (strrchr(input_file, '.') == NULL ) {
//		read_graph_node_node(input_file, 1);
//	} else if (strcmp(fileStyle, "clq") == 0) {
//		read_graph_node_node(input_file, 1);
//	} else if (strcmp(fileStyle, "edges") == 0) {
//		read_graph_node_node(input_file, 2);
//	} else if (strcmp(fileStyle, "mtx") == 0) {
//		read_graph_node_node(input_file, 2);
//	} else if (strcmp(fileStyle, "wclq") == 0) {
//		read_graph_wclq_format(input_file);
//	} else if (FORMAT == 1) {
//		read_graph_node_node(input_file, 1);
//	} else if (FORMAT == 2) {
//		read_graph_node_node(input_file, 2);
//	} else {
//		read_graph_node_node(input_file, 1);
//	}
    read_graph_wclq_format(input_file);
	printf("R #node=%d #edge=%d #density=%9.8f\n", NB_NODE, NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
	NB_NODE_O = NB_NODE;
	NB_EDGE_O = NB_EDGE;
	N0_B = NB_NODE;
	D0_B = ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1));

	READ_TIME = get_utime();

	printf("R Reading Time: %4.2lf \n", READ_TIME);
	return TRUE;
}

static void sort_by_degree_degeneracy_ordering() {
	long long *degree_counter;
	long long *where;
	int p1, i, node = NONE, neibor, *neibors, t, j, h, k, Max_Weight;
	long long cur_degree = 0;
	INIT_CLQ_SIZE = 0;
//	printf("I computing vertex degeneracy ordering...\n");

//	printf("the number of node is %d\n", NB_NODE);

    Max_Degree = 0;
    Max_Weight = 0;
	for (int i = 1; i<= NB_NODE; i++){
	    if (Node_Degree[i] > Max_Degree){
	        Max_Degree = Node_Degree[i];
	    }
	    if (Top_Weight[i] > Max_Weight){
	        Max_Weight = Top_Weight[i];
	    }
    }
//    printf("the maximum degree is %d\n", Max_Degree);
    MaxCLQ_Stack = (int *) malloc((Max_Degree + 1) * sizeof(int));

    if (Max_Weight > MAX_NODE) {
		LARGE_WEIGHT = TRUE;
//		printf("I reduce first level subgraphs is DISABLE\n");
	} else {
		LARGE_WEIGHT = FALSE;
//		printf("I reduce first level subgraphs is ENABLE\n");
	}

	where = Candidate_Stack + NB_NODE + 1;
	degree_counter = Vertex_UB;
	memset(degree_counter, 0, (Max_Degree + 1) * sizeof(long long));

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
		if (p1 < NB_NODE - 1 && Node_Degree[node] == Node_Degree[Candidate_Stack[p1 + 1]]) {
			degree_counter[Node_Degree[node]] = p1 + 1;
		}

		if (Node_Degree[node] == NB_NODE - p1 - 1) {
			INIT_CLQ_SIZE = 0;
			INIT_CLQ_WEIGHT = 0;
			for (i = p1; i < NB_NODE; i++) {
				MaxCLQ_Stack[INIT_CLQ_SIZE++] = Candidate_Stack[i];
				INIT_CLQ_WEIGHT += Top_Weight[Candidate_Stack[i]];
			}
			printf("I initial clique weight: %lld\n", INIT_CLQ_WEIGHT);
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
				if (Node_Degree[neibor] != Node_Degree[Candidate_Stack[h - 1]]) {
					degree_counter[Node_Degree[neibor]] = h;
				}
			}
		}
		p1++;
	}
}

static void sort_by_score_ordering() {

//	INIT_CLQ_SIZE = 0;
//	INIT_CLQ_WEIGHT = 0;


	int Max_Weight, Max_Degree;
//	printf("I computing vertex degeneracy ordering...\n");
//
//	printf("the number of node is %d\n", NB_NODE);

    Max_Degree = 0;
    Max_Weight = 0;
	for (int i = 1; i<= NB_NODE; i++){
	    if (Node_Degree[i] > Max_Degree){
	        Max_Degree = Node_Degree[i];
	    }
	    if (Top_Weight[i] > Max_Weight){
	        Max_Weight = Top_Weight[i];
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

    if (Max_Weight > MAX_NODE) {
		LARGE_WEIGHT = TRUE;
//		printf("I reduce first level subgraphs is DISABLE\n");
	} else {
		LARGE_WEIGHT = FALSE;
//		printf("I reduce first level subgraphs is ENABLE\n");
	}

	for (int node = 0; node < NB_NODE; node++) {
		Candidate_Stack[node] = NB_NODE - node;
	}
	Candidate_Stack[NB_NODE] = DELIMITER;


//    for (int i = 0; i < ini_cli_size; i++){
//        MaxCLQ_Stack[i] = rankVar[ini_clique[i]+1];
//        INIT_CLQ_WEIGHT += Top_Weight[rankVar[ini_clique[i]+1]];
//    }
//
//    if (INIT_CLQ_WEIGHT != objVal){
//        printf("INIT_CLQ is wrong \n");
//        exit(0);
//    } else{
//        printf("I initial clique weight: %lld\n", INIT_CLQ_WEIGHT);
//    }
}

static int init_for_degeneracy(long long *segment_counter, long long *where) {
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
	int *neibors, neibor, new_weight, total_weight = 0;
	int p1, i, node = NONE, t, head, head_node;
	int cur_core = 0, pre_weight, cur_weight;
	INIT_CLQ_SIZE = 0;
	MAX_SUBGRAPH_SIZE = 0;
	printf("I computing weight cores and degeneracy ordering...\n");

	long long *where = Candidate_Stack + NB_NODE + 1;
	long long *segment_counter = Vertex_UB + NB_NODE + 1;
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

		if (p1 < NB_NODE - 1 && cur_weight == Node_Weight[Candidate_Stack[p1 + 1]]) {
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

			printf("I The initial clique weight is %lld, W_CORE_G is %d\n", INIT_CLQ_WEIGHT, K_CORE_G);
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

				if (head == p1 + 1 || new_weight > Node_Weight[Candidate_Stack[head - 1]]) {
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

static int addIntoIsetTomitaBis_adj(int node) {

	int j, iset_node;
	long long *current_set;

	for (j = 0; j < iSET_COUNT; j++) {
		if (Top_Weight[node] - iSET_Weight[j] + iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT) {
			current_set = iSET[j];
			for (iset_node = *current_set; iset_node != NONE; iset_node = *(++current_set)) {
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

static int re_number_adj(int node) {
	int i, k, neibor, one_neibor, count;
	long long *neibors, *saved_neibors, iset_weight, iset_second_weight, inc1 = 0, inc2 = 0;
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
					for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
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
						} else if (count == 1 && Top_Weight[one_neibor] == iset_weight) {
							if (Top_Weight[node] > iset_second_weight)
								inc1 = Top_Weight[node] - iset_weight;
							else
								inc1 = iset_second_weight - iset_weight;
						}

						if (Top_Weight[one_neibor] >= iSET_Weight[k]) {
							inc2 = Top_Weight[one_neibor] - iSET_Weight[k];
						}
						if (inc1 + inc2 + iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT) {

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

static long long absorb_by_inserting(int iset_idx, long long iset_weight, int insert_node, long long node_weight, int last_iset) {
	long long insert_weight, *iset_addr, *_addr;
	//assert(iset_weight == iSET_Weight[iset_idx]);
	//assert(iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT);
	//determine the weight can be inserted into
	if (node_weight <= iset_weight) {
		insert_weight = node_weight;
	} else if (last_iset == NONE) {
		assert(node_weight - iset_weight + iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT);
		insert_weight = node_weight;
	} else {
		insert_weight = iset_weight;
	}

	iset_addr = iSET[iset_idx];
	while (*iset_addr != NONE) {
		if (insert_weight > *(iset_addr + 1))
			break;
		iset_addr += 2;
	}
	if (*iset_addr == NONE) {
		*iset_addr = insert_node;
		*(iset_addr + 1) = insert_weight;
		*(iset_addr + 2) = NONE;
	} else {
		_addr = iSET[iset_idx] + iSET_Size[iset_idx] * 2;
		*(_addr + 2) = NONE;
		while (_addr != iset_addr) {
			*_addr = *(_addr - 2);
			*(_addr + 1) = *(_addr - 1);
			_addr = _addr - 2;
		}
		*_addr = insert_node;
		*(_addr + 1) = insert_weight;
	}
	iSET_Size[iset_idx]++;
	if (insert_weight > iset_weight) {
		iSET_Weight[iset_idx] = insert_weight;
		iSET_TOTAL_WEIGHT += insert_weight - iset_weight;
	}
	return insert_weight;
}

static long long absorb_by_splitting(int iset_idx, long long topk_weight, int insert_node, long long node_weight) {
	int k, iset_node;
	long long insert_weight, *iset_addr, new_weight;
	//determine the weight can be inserted into
	//assert(node_weight - topk_weight + iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT);

	if (node_weight > topk_weight) {
		insert_weight = node_weight;
		iSET_TOTAL_WEIGHT += node_weight - topk_weight;
	} else {
		insert_weight = node_weight;
		topk_weight = node_weight;
	}

	assert(iSET_COUNT < MAX_SUBGRAPH_SIZE);
	//insert_weight = topk_weight;

	k = 2;
	iSET_Size[iSET_COUNT] = 1;
	iSET[iSET_COUNT][0] = insert_node;
	iSET[iSET_COUNT][1] = insert_weight;
	iSET[iSET_COUNT][2] = NONE;
	iSET_Weight[iSET_COUNT] = insert_weight;

	iSET_Weight[iset_idx] -= topk_weight;
	new_weight = iSET_Weight[iset_idx];
	iset_addr = iSET[iset_idx];
	for (iset_node = *iset_addr; iset_node != NONE; iset_node = *(iset_addr += 2)) {
		if (*(iset_addr + 1) > new_weight) {
			iSET[iSET_COUNT][k++] = iset_node;
			iSET[iSET_COUNT][k++] = *(iset_addr + 1) - new_weight;
			*(iset_addr + 1) = new_weight;
			iSET_Size[iSET_COUNT]++;
		} else {
			break;
		}
	}
	iSET[iSET_COUNT][k] = NONE;
	iSET_COUNT++;
	return insert_weight;

}

static void do_weight_partition(int insert_node, long long node_weight) {
	int iset_idx, p = ptr(Candidate_Stack);
	long long abs_weight, iset_weight;
	for (iset_idx = Candidate_Stack[p]; iset_idx != NONE; iset_idx = Candidate_Stack[++p]) {
		iset_weight = iSET_Weight[iset_idx];
		abs_weight = Candidate_Stack[++p];
		//	assert(iset_weight == abs_weight);
		if (iset_weight == abs_weight) {
			node_weight -= absorb_by_inserting(iset_idx, abs_weight, insert_node, node_weight, Candidate_Stack[p + 1]);

		} else {
			//assert(iset_weight > abs_weight);
			assert(Candidate_Stack[p + 1] == NONE);
			node_weight -= absorb_by_splitting(iset_idx, abs_weight, insert_node, node_weight);

		}
		//assert(node_weight >= 0);
		if (node_weight <= 0)
			break;
	}
	if (node_weight > 0) {
		//assert(t == p);
		iSET_Size[iSET_COUNT] = 1;
		iSET[iSET_COUNT][0] = insert_node;
		iSET[iSET_COUNT][1] = node_weight;
		iSET[iSET_COUNT][2] = NONE;
		iSET_Weight[iSET_COUNT] = node_weight;
		iSET_TOTAL_WEIGHT += node_weight;
		iSET_COUNT++;
	}
//	assert(iSET_COUNT <= MAX_SUBGRAPH_SIZE);
//assert(node_weight == 0);
}

static int add_vertex_with_weight_partition(int insert_node) {
	int j, iset_node, iset_topk = NONE;
	long long iset_weight, max_topk = 0, node_weight = Node_Weight[insert_node], abs_weight = 0;
	unsigned char *adj_list = iMatrix(insert_node);
	int p = ptr(Candidate_Stack);
	long long *iset_addr;

	Candidate_Stack[p] = NONE;

	for (j = 0; j < iSET_COUNT; j++) {
		iset_addr = iSET[j];
		iset_weight = iSET_Weight[j];

		//test if the node can be inserted into
		for (iset_node = *iset_addr; iset_node != NONE; iset_node = *(iset_addr += 2)) {
			if (Matrix(adj_list,iset_node) > 0) {
				break;
			}
		}

		// can be inserted into
		if (iset_node == NONE) {
			abs_weight += iset_weight;
			Candidate_Stack[p++] = j;
			Candidate_Stack[p++] = iset_weight;
		} else if (iset_weight - *(iset_addr + 1) > max_topk) {
			max_topk = iset_weight - *(iset_addr + 1);
			iset_topk = j;
		}

//		if (abs_weight >= node_weight)
//			break;

		if (abs_weight + max_topk >= node_weight)
			break;
//		if (node_weight + iSET_TOTAL_WEIGHT - abs_weight - max_topk
//				<= MAX_ISET_WEIGHT)
//			break;

	}
	Candidate_Stack[p] = NONE;
	//max_topk=0;
	if (node_weight + iSET_TOTAL_WEIGHT - abs_weight - max_topk <= MAX_ISET_WEIGHT) {
		if (max_topk > 0) {
			Candidate_Stack[p++] = iset_topk;
			Candidate_Stack[p++] = max_topk;
			Candidate_Stack[p] = NONE;
		}
		do_weight_partition(insert_node, node_weight);

		return TRUE;
	} else {
		return FALSE;
	}
}

//static void build_structures();
//static void check_build_structures();

static int cut_by_iset_less_vertices() {
	int i = ptr(Candidate_Stack) - 2, j, node;
	iSET_COUNT = 0;
	iSET_TOTAL_WEIGHT = 0;
	MAX_ISET_WEIGHT = MAX_CLQ_WEIGHT - CUR_CLQ_WEIGHT - CUR_NODE_WEIGHT;
	if (MAX_ISET_WEIGHT <= 0)
		return FALSE;
	for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[--i]) {
		for (j = 0; i < iSET_COUNT; j++)
			iSET_Tested[j] = FALSE;
		if (addIntoIsetTomitaBis_adj(node) == FALSE && re_number_adj(node) == FALSE) {
			return FALSE;
		}
	}
	return TRUE;
}
static int NODE_IN_ISET;

static int cut_by_binary_maxsat_reasoning() {
	int i = ptr(Candidate_Stack) - 2, node;
	LAST_IN = INT_MAX;
	FIRST_INDEX = NONE;
	NODE_IN_ISET = 0;
	iSET_COUNT = 0;
	iSET_TOTAL_WEIGHT = 0;
	MAX_ISET_WEIGHT = MAX_CLQ_WEIGHT - CUR_CLQ_WEIGHT - CUR_NODE_WEIGHT;

	if (MAX_ISET_WEIGHT <= 0) {
		for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[--i]) {
			Candidate_Stack[i] = -node;
		}
		Branching_Point = ptr(Candidate_Stack) - 1;
		return FALSE;
	}

	for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[--i]) {
		if (add_vertex_with_weight_partition(node) == FALSE) {
			Candidate_Stack[i] = -node;
		} else {
			NODE_IN_ISET++;
			LAST_IN = i;
		}
	}

	i = ptr(Candidate_Stack) - 2;
	for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[--i]) {
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
		for (node = Candidate_Stack[i = FIRST_INDEX]; node != DELIMITER; node = Candidate_Stack[--i]) {
			if (i > LAST_IN) {
				if (node < 0) {
					Vertex_UB[i] = UPPER_WEIGHT_BOUND - CUR_CLQ_WEIGHT - CUR_NODE_WEIGHT;
				}
			} else {
				break;
			}
		}
#else
		if(iSET_COUNT<=5){
			for (node = Candidate_Stack[i = FIRST_INDEX]; node != DELIMITER; node = Candidate_Stack[--i]) {
				if (i > LAST_IN) {
					if (node < 0) {
						Vertex_UB[i] = UPPER_WEIGHT_BOUND - CUR_CLQ_WEIGHT - CUR_NODE_WEIGHT;
					}
				} else {
					break;
				}
			}
		}
#endif
		Branching_Point = FIRST_INDEX + 1;
		return FALSE;
		
	}
}

#define assign_node(node, value, reason) {\
	Node_Value[node] = value;\
	Node_Reason[node] = reason;\
	push(node, FIXED_NODE_STACK);\
}

inline static int add_new_iset_for_bnode(int b_node, long long b_weight) {
	assert(iSET_COUNT < MAX_ISET_COUNT);
	IS[iSET_COUNT].satisfied = FALSE;
	IS[iSET_COUNT].used = FALSE;
	IS[iSET_COUNT].involved = FALSE;
	IS[iSET_COUNT].active = TRUE;
	IS[iSET_COUNT].size = 1;
	IS[iSET_COUNT].weight = b_weight;
	IS[iSET_COUNT].topk = 1;
	IS[iSET_COUNT].nodes = iNode_TAIL;

	*(iNode_TAIL++) = b_node;
	*(iNode_TAIL++) = b_weight;
	//*(iNode_TAIL++) = NULL_REASON;
	*(iNode_TAIL++) = NONE;
	iNode_TAIL += RESERVED_LENGTH;

	iSET_COUNT++;
	iSET_TOTAL_WEIGHT += b_weight;

	//assert(iSET_TOTAL_WEIGHT > MAX_ISET_WEIGHT);
	return iSET_COUNT - 1;
}

static void init_for_maxsat_reasoning() {
	int i;
	ptr(UNIT_STACK) = 0;
	ptr(REASON_STACK) = 0;
	ptr(NEW_UNIT_STACK) = 0;
	//ptr(TOP_UNIT_STACK) = 0;
	ptr(FIXED_NODES_STACK) = 0;
	ptr(TOPK_REDUCED_STACK) = 0;
	ptr(SATISFIED_iSETS_STACK) = 0;

	for (i = iSET_COUNT - 1; i >= 0; i--) {
		IS[i].used = FALSE;
		IS[i].involved = FALSE;

		if (IS[i].active == TRUE) {
			if (IS[i].size == 0) {
				IS[i].satisfied = TRUE;
			} else {
				IS[i].satisfied = FALSE;
				if (IS[i].topk == 1)
					push(i, UNIT_STACK);
			}
		}
	}
}

//static int get_t_weight(int iset) {
//	int t_weight = 0, flag = TRUE;
//	int node, *nodes = IS[iset].nodes;
//	assert(iset < iSET_COUNT && iset >= 0);
//	for (node = *(nodes); node != NONE; node = *(nodes += 2)) {
//		//test
//		assert(node > 0);
//		if (Node_Value[node] == P_TRUE && flag == TRUE) {
//			assert(*(nodes + 1) == IS[iset].weight);
//			flag = FALSE;
//		}
//		//
//		if (Node_Value[node] != P_FALSE && *(nodes + 1) < IS[iset].weight) {
//			t_weight = *(nodes + 1);
//			break;
//		}
//	}
//	assert(t_weight < IS[iset].weight);
//	return t_weight;
//}

//static void release_conflicting_isets() {
//	int i, j = 0, iset, *nodes;
//	int delta = IS[REASON_STACK[0]].weight;
//	NEW_NODE_IDX++;
//	Node_Value[NEW_NODE_IDX] = UNASSIGNED;
//	for (i = 0; i < ptr(REASON_STACK); i++) {
//
//		iset = REASON_STACK[i];
//
//		if (IS[iset].weight < delta)
//			delta = IS[iset].weight;
//
//		nodes = IS[iset].nodes;
//		while (*nodes != NONE)
//			nodes++;
//		*(nodes) = NEW_NODE_IDX;
//		*(nodes + 1) = NONE;
//		IS[iset].size++;
//		IS[iset].involved = FALSE;
//		iSET[NEW_NODE_IDX][j++] = iset;
//	}
//	iSET[NEW_NODE_IDX][j] = NONE;
//	iSET_TOTAL_WEIGHT -= delta;
//}

//static int retrace_conflicting_isets2(int start_iset) {
//	int i, iset, reason, node;
//	int *nodes;
//	int delta = NONE, start, count = 0, t_weight;
//	start = ptr(REASON_STACK);
//	push(start_iset, REASON_STACK);
//	delta = IS[start_iset].weight;
//	IS[start_iset].involved = TRUE;
//
//	assert(IS[start_iset].size==0 && IS[start_iset].satisfied==FALSE);
//
//	for (i = 0; i < ptr(REASON_STACK); i++) {
//		iset = REASON_STACK[i];
//		nodes = IS[iset].nodes;
//		for (node = *nodes; node != NONE; node = *(++nodes)) {
////			assert(Node_Value[node]==P_FALSE);
//
//			reason = Node_Reason[node];
//			if (IS[reason].involved == FALSE) {
//				push(reason, REASON_STACK);
//				IS[reason].involved = TRUE;
//				if (IS[reason].weight < delta)
//					delta = IS[reason].weight;
//			}
//		}
//	}
//
//	assert(delta > 0);
//	return delta;
//}

static int retrace_conflicting_isets(int start_iset) {
	int i, iset, reason, node;
	long long *nodes;
	int start, count = 0;
	long long delta = NONE, t_weight;
	start = ptr(REASON_STACK);
	push(0, REASON_STACK);
	push(0, REASON_STACK);
	push(start_iset, REASON_STACK);
	IS[start_iset].involved = TRUE;

	assert(IS[start_iset].topk==0 && IS[start_iset].satisfied==FALSE);

//	assert(IS_WEIT(start_iset)>0);
	nodes = IS[start_iset].nodes;
	for (node = *(nodes); node != NONE; node = *(nodes += 2)) {
//		if (*(nodes + 1) == IS[start_iset].weight) {
//			if (Node_Value[node] != P_FALSE)
//				printf("Node_Value[node]=%d\n", Node_Value[node]);
//		}
		if (Node_Value[node] != P_FALSE) {
			assert(*(nodes + 1) < IS[start_iset].weight);
			break;
		}
	}

	if (node == NONE) {
		t_weight = 0;
	} else {
		t_weight = *(nodes + 1);
	}
	delta = IS[start_iset].weight - t_weight;

	assert(delta > 0);
	push(t_weight, REASON_STACK);

	nodes = IS[start_iset].nodes;
	for (node = *nodes; node != NONE; node = *(nodes += 2)) {
		if (*(nodes + 1) > t_weight) {
			assert(Node_Value[node]==P_FALSE);

			reason = Node_Reason[node];
			if (IS[reason].involved == FALSE) {
				push(reason, REASON_STACK);

				//assert(get_t_weight(reason) == 0);
				push(IS[reason].t_weight, REASON_STACK);
				IS[reason].involved = TRUE;
			}
		} else {
			break;
		}
	}

	for (i = start + 4; i < ptr(REASON_STACK); i += 2) {
		iset = REASON_STACK[i];
		t_weight = REASON_STACK[i + 1];
		nodes = IS[iset].nodes;
		for (node = *nodes; node != NONE; node = *(nodes += 2)) {
			if (*(nodes + 1) > t_weight) {
				if (Node_Value[node] == P_FALSE) {
					reason = Node_Reason[node];
					if (IS[reason].involved == FALSE) {
						push(reason, REASON_STACK);
						//assert(get_t_weight(reason) == 0);
						push(IS[reason].t_weight, REASON_STACK);
						IS[reason].involved = TRUE;
					}
				}
			} else {
				break;
			}
		}
	}
// determine delta
	count = 0;
	for (i = start + 2; i < ptr(REASON_STACK); i += 2) {
		count++;
		iset = REASON_STACK[i];
		t_weight = REASON_STACK[i + 1];
		IS[iset].involved = FALSE;
		if (IS[iset].weight - t_weight < delta)
			delta = IS[iset].weight - t_weight;
	}
	assert(count > 0);
	assert(delta > 0);
	REASON_STACK[start] = count;
	REASON_STACK[start + 1] = delta;

	return delta;
}

static int fix_node(int fix_node, int fix_iset) {
	int i, j, iset, node;
	long long *nodes = IS[fix_iset].nodes;
	//find the unit node
	if (fix_node == NONE) {
		for (fix_node = *(nodes); fix_node != NONE; fix_node = *(nodes += 2)) {
			if (Node_Value[fix_node] == UNASSIGNED) {
				break;
			}
		}
	}
	//determine the t_weight
	for (node = *(nodes += 2); node != NONE; node = *(nodes += 2)) {
		if (*(nodes + 1) < IS[fix_iset].weight && Node_Value[node] != P_FALSE) {
			break;
		}
	}
	if (node == NONE)
		IS[fix_iset].t_weight = 0;
	else
		IS[fix_iset].t_weight = *(nodes + 1);

	Node_Value[fix_node] = P_TRUE;
	Node_Reason[fix_node] = fix_iset;
	IS[fix_iset].satisfied = TRUE;
	push(fix_node, FIXED_NODES_STACK);
	push(fix_iset, SATISFIED_iSETS_STACK);
	//set fix_node=TRUE
	for (iset = iSET[fix_node][i = 0]; iset != NONE; iset = iSET[fix_node][i]) {
		if (IS[iset].satisfied == FALSE) {
			if (iSET[fix_node][i + 1] == IS[iset].weight) {
				IS[iset].satisfied = TRUE;
				push(iset, SATISFIED_iSETS_STACK);
			} else {
				//assert(iSET[fix_node][i + 1] < IS[iset].weight);
				nodes = IS[iset].nodes;
				for (node = *(nodes); node != fix_node; node = *(nodes += 2)) {
					if (Node_Value[node] == UNASSIGNED) {
						Node_Value[node] = P_FALSE;
						Node_Reason[node] = fix_iset;
						push(node, FIXED_NODES_STACK);
						if (*(nodes + 1) == IS[iset].weight) {
							IS[iset].topk--;
							push(iset, TOPK_REDUCED_STACK);
						}
					} else if (Node_Value[node] == P_TRUE) {
						break;
					}
				}
				return iset;
			}
		}
		i += 2;
	}

	unsigned char *adj_list = iMatrix(fix_node);
	//exclude non-neibors of fix_node in their isets
	i = ptr(Candidate_Stack) - 2;
	for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[--i]) {

		if (node > 0 && Node_Value[node] == UNASSIGNED && Matrix(adj_list,node) == FALSE) {
			Node_Value[node] = P_FALSE;
			Node_Reason[node] = fix_iset;
			push(node, FIXED_NODES_STACK);

			for (iset = iSET[node][j = 0]; iset != NONE; iset = iSET[node][j += 2]) {
				if (IS[iset].satisfied == FALSE && iSET[node][j + 1] == IS[iset].weight) {
					IS[iset].topk--;
					//IS[iset].size--;
					push(iset, TOPK_REDUCED_STACK);
					if (IS[iset].topk == 0) {
						return iset;
					} else if (IS[iset].topk == 1) {
						push(iset, NEW_UNIT_STACK);
					}

				}
			}
		}
	}
	return NONE;
}

static int reasoning_with_up() {
	int i, j, iset, empty_set;
	for (i = 0; i < ptr(UNIT_STACK); i++) {
		iset = UNIT_STACK[i];
		if (IS[iset].satisfied == FALSE) {

			//assert(IS[iset].topk == 1);

			ptr(NEW_UNIT_STACK) = 0;
			if ((empty_set = fix_node(NONE, iset)) != NONE) {
				retrace_conflicting_isets(empty_set);
				return TRUE;
			} else {
				for (j = 0; j < ptr(NEW_UNIT_STACK); j++) {
					iset = NEW_UNIT_STACK[j];
					if (IS[iset].satisfied == FALSE) {
						//assert(IS[iset].topk == 1);
						if ((empty_set = fix_node(NONE, iset)) != NONE) {
							retrace_conflicting_isets(empty_set);
							return TRUE;
						}
					}
				}
			}
		}
	}
	return FALSE;
}

static void reset_context() {
	int i;
	for (i = 0; i < ptr(FIXED_NODES_STACK); i++) {
		Node_Value[FIXED_NODES_STACK[i]] = UNASSIGNED;
	}
	ptr(FIXED_NODES_STACK) = 0;
	for (i = 0; i < ptr(SATISFIED_iSETS_STACK); i++) {
		IS[SATISFIED_iSETS_STACK[i]].satisfied = FALSE;
	}
	ptr(SATISFIED_iSETS_STACK) = 0;
	for (i = 0; i < ptr(TOPK_REDUCED_STACK); i++) {
		IS[TOPK_REDUCED_STACK[i]].topk++;
	}
	ptr(TOPK_REDUCED_STACK) = 0;
}

inline static void reduce_iset(int iset_idx, long long delta) {
	int size = 0, topk = 0;
	int node;
	long long *nodes;

	IS[iset_idx].weight -= delta;
	nodes = IS[iset_idx].nodes;

	for (node = *nodes; node != NONE; node = *(nodes += 2)) {
		if (*(nodes + 1) > delta) {
			size++;
			*(nodes + 1) = *(nodes + 1) - delta;
			if (*(nodes + 1) == IS[iset_idx].weight)
				topk++;

		} else {
			*(nodes) = NONE;
			break;
		}
	}
	IS[iset_idx].size = size;
	IS[iset_idx].topk = topk;
	if (IS[iset_idx].size == 0)
		IS[iset_idx].active = FALSE;
}

static void reduce_iset_topk_new(int iset_idx, long long delta, long long t_weight) {
	int topk = 0;
	int node;
	long long *nodes = IS[iset_idx].nodes;

	IS[iset_idx].weight -= delta;

	long long new_weight = IS[iset_idx].weight;

	for (node = *nodes; node != NONE; node = *(nodes += 2)) {
		if (*(nodes + 1) - delta >= t_weight) {
			//old
			*(nodes + 1) = *(nodes + 1) - delta;
			if (*(nodes + 1) == new_weight)
				topk++;

		} else if (*(nodes + 1) > t_weight) {
			//old
			*(nodes + 1) = t_weight;
			if (t_weight == new_weight)
				topk++;
		} else if (*(nodes + 1) == new_weight) {
			topk++;
		}
	}
	IS[iset_idx].topk = topk;
}

static void split_conflicting_isets() {
	int i, count = REASON_STACK[0], iset;
	long long delta = REASON_STACK[1], t_weight;
	//NEW_NODE_IDX++;

	//iSET_Size[NEW_NODE_IDX] = 0;
	//iSET[NEW_NODE_IDX][0] = NONE;
	//Node_Value[NEW_NODE_IDX] = UNASSIGNED;

	for (i = 1; i <= count; i++) {
		iset = REASON_STACK[i * 2];
		t_weight = REASON_STACK[i * 2 + 1];

		if (t_weight == 0) {
			reduce_iset(iset, delta);

		} else {
			reduce_iset_topk_new(iset, delta, t_weight);
		}
	}
	iSET_TOTAL_WEIGHT -= delta;
}

static int NB_TOPK;
static void build_iset_structures();
static void build_node_isets();

static long long insert_into_iset(int iset_idx, long long iset_weight, int insert_node, long long node_weight) {
	long long insert_weight, *iset_addr, *_addr;

	if (node_weight <= iset_weight) {
		insert_weight = node_weight;
	} else if (node_weight - iset_weight + iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT) {
		insert_weight = node_weight;
	} else {
		insert_weight = iset_weight;
	}

	iset_addr = IS[iset_idx].nodes;
	while (*iset_addr != NONE) {
		if (insert_weight > *(iset_addr + 1))
			break;
		iset_addr += 2;
	}
	if (*iset_addr == NONE) {
		*iset_addr = insert_node;
		*(iset_addr + 1) = insert_weight;
		*(iset_addr + 2) = NONE;
	} else {
		_addr = IS[iset_idx].nodes + IS[iset_idx].size * 2;
		assert(*_addr==NONE);
		*(_addr + 2) = NONE;
		while (_addr != iset_addr) {
			*_addr = *(_addr - 2);
			*(_addr + 1) = *(_addr - 1);
			_addr = _addr - 2;
		}
		*_addr = insert_node;
		*(_addr + 1) = insert_weight;
	}
	IS[iset_idx].size++;
	if (insert_weight > iset_weight) {
		IS[iset_idx].topk = 1;
		IS[iset_idx].weight = insert_weight;
		iSET_TOTAL_WEIGHT += insert_weight - iset_weight;

	} else if (insert_weight == iset_weight) {
		IS[iset_idx].topk++;
	}

	return insert_weight;
}

static long long split_and_insert(int iset_idx, long long t_weight, int insert_node, long long node_weight) {
	int node;
	long long insert_weight, *nodes, new_weight;
	//determine the weight can be inserted into
	assert(t_weight > 0);
	long long delta = IS[iset_idx].weight - t_weight;
	if (node_weight > delta) {
		if (node_weight - delta + iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT) {
			insert_weight = node_weight;
			iSET_TOTAL_WEIGHT += node_weight - delta;
		} else {
			insert_weight = delta;
		}
	} else {
		insert_weight = node_weight;
		delta = node_weight;
	}

	assert(delta > 0);
	assert(delta <= insert_weight);
	assert(iSET_COUNT < MAX_ISET_COUNT);

	IS[iSET_COUNT].satisfied = FALSE;
	IS[iSET_COUNT].used = FALSE;
	IS[iSET_COUNT].involved = FALSE;
	IS[iSET_COUNT].active = TRUE;
	IS[iSET_COUNT].size = 1;
	IS[iSET_COUNT].weight = insert_weight;
	IS[iSET_COUNT].topk = 1;
	IS[iSET_COUNT].nodes = iNode_TAIL;

	*(iNode_TAIL++) = insert_node;
	*(iNode_TAIL++) = insert_weight;
	//*(iNode_TAIL++) = NULL_REASON;

	assert(IS[iSET_COUNT].weight > 0);

	IS[iset_idx].weight -= delta;
	new_weight = IS[iset_idx].weight;
	IS[iset_idx].topk = 0;
	nodes = IS[iset_idx].nodes;
	for (node = *nodes; node != NONE; node = *(nodes += 2)) {
		if (*(nodes + 1) - delta >= t_weight) {
			*(iNode_TAIL++) = node;
			*(iNode_TAIL++) = delta;
			IS[iSET_COUNT].size++;
			if (delta == insert_weight)
				IS[iSET_COUNT].topk++;

			*(nodes + 1) -= delta;
			if (*(nodes + 1) == new_weight) {
				IS[iset_idx].topk++;
			}
		} else if (*(nodes + 1) > t_weight) {
			*(iNode_TAIL++) = node;
			*(iNode_TAIL++) = *(nodes + 1) - t_weight;
			IS[iSET_COUNT].size++;

			*(nodes + 1) = t_weight;
			if (t_weight == new_weight)
				IS[iset_idx].topk++;
		} else if (*(nodes + 1) == new_weight) {
			IS[iset_idx].topk++;
		}
	}
	*(iNode_TAIL++) = NONE;
	iNode_TAIL += RESERVED_LENGTH;

	iSET_COUNT++;
	return insert_weight;
}

static int insert_vertex_with_max3sat(int insert_node) {
	int iset_idx, node;
	long long *nodes, iset_weight, node_weight = Node_Weight[insert_node];
	unsigned char *adj_list = iMatrix(insert_node);

	int k = iSET_COUNT, i = ptr(Candidate_Stack) - 2;

	ptr(NEW_UNIT_STACK) = 0;
	Node_Value[insert_node] = UNASSIGNED;

	for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[--i]) {
		if (node > 0) {
			Node_Value[node] = UNASSIGNED;
		} else {
			Node_Value[-node] = UNASSIGNED;
		}
	}
	for (iset_idx = 0; iset_idx < k; iset_idx++) {
		if (IS[iset_idx].active == TRUE) {
			IS[iset_idx].involved = FALSE;
			assert(IS[iset_idx].weight > 0);
			nodes = IS[iset_idx].nodes;
			iset_weight = IS[iset_idx].weight;
			//test if the node can be inserted into the iset
			for (node = *nodes; node != NONE; node = *(nodes += 2)) {
				if (Matrix(adj_list,node) > 0) {
					break;
				} else {
					Node_Value[node] = P_FALSE;
				}
			}
			// can be inserted into iset i
			if (node == NONE) {
				node_weight -= insert_into_iset(iset_idx, iset_weight, insert_node, node_weight);
				assert(node_weight >= 0);
				assert(IS[iset_idx].size > 0);
				assert(IS[iset_idx].weight > 0);
				IS[iset_idx].involved = TRUE;
			} else {
				if (iset_weight > *(nodes + 1)) {
					node_weight -= split_and_insert(iset_idx, *(nodes + 1), insert_node, node_weight);
					assert(node_weight >= 0);
					assert(IS[iSET_COUNT - 1].weight > 0);
					assert(IS[iset_idx].size > 0);
					assert(IS[iset_idx].weight > 0);
					//IS[iset_idx].involved = TRUE;
				}
				if (IS[iset_idx].weight == *(nodes + 1)) {
					int unit_node = node;
					long long second_weight = NONE;
					for (node = *(nodes += 2); node != NONE; node = *(nodes += 2)) {
						if (Matrix(adj_list,node) > 0) {
							if (second_weight == NONE)
								second_weight = *(nodes + 1);
						} else {
							Node_Value[node] = P_FALSE;
						}
					}
					if (second_weight == NONE || IS[iset_idx].weight > second_weight) {
						push(unit_node, NEW_UNIT_STACK);
						push(iset_idx, NEW_UNIT_STACK);
						if (second_weight == NONE)
							IS[iset_idx].t_weight = 0;
						else
							IS[iset_idx].t_weight = second_weight;
					}
				}
			}
			if (iSET_TOTAL_WEIGHT + node_weight <= MAX_ISET_WEIGHT)
				break;
		}
	}
	if (iSET_TOTAL_WEIGHT + node_weight <= MAX_ISET_WEIGHT) {
		if (node_weight > 0)
			add_new_iset_for_bnode(insert_node, node_weight);
		return TRUE;
	} else {
		int j, fix_iset, fix_node;
		long long delta;
		for (j = 0; j < ptr(NEW_UNIT_STACK); j++) {
			fix_node = NEW_UNIT_STACK[j];
			fix_iset = NEW_UNIT_STACK[++j];
			if (IS[fix_iset].active == TRUE && IS[fix_iset].involved == FALSE) {
				adj_list = iMatrix(fix_node);
				for (iset_idx = 0; iset_idx < k; iset_idx++) {
					if (iset_idx == fix_iset || IS[iset_idx].active == FALSE || IS[fix_iset].involved == TRUE)
						continue;
					nodes = IS[iset_idx].nodes;
					iset_weight = IS[iset_idx].weight;
					assert(IS[iset_idx].weight > 0);
					for (node = *nodes; node != NONE; node = *(nodes += 2)) {
						if (node == fix_node || (Node_Value[node] == UNASSIGNED && Matrix(adj_list, node) > 0)) {
							break;
						}
					}
					if (node == NONE || iset_weight > *(nodes + 1)) {
						if (node == NONE)
							IS[iset_idx].t_weight = 0;
						else
							IS[iset_idx].t_weight = *(nodes + 1);

						delta = node_weight;
						assert(delta > 0);
						if (delta > IS[iset_idx].weight - IS[iset_idx].t_weight)
							delta = IS[iset_idx].weight - IS[iset_idx].t_weight;
						if (delta > IS[fix_iset].weight - IS[fix_iset].t_weight)
							delta = IS[fix_iset].weight - IS[fix_iset].t_weight;

						assert(delta > 0);

						if (IS[iset_idx].t_weight == 0) {
							reduce_iset(iset_idx, delta);
						} else {
							reduce_iset_topk_new(iset_idx, delta, IS[iset_idx].t_weight);
						}

						if (IS[fix_iset].t_weight == 0) {
							reduce_iset(fix_iset, delta);
						} else {
							reduce_iset_topk_new(fix_iset, delta, IS[fix_iset].t_weight);
						}

						node_weight -= delta;

						IS[iset_idx].involved = TRUE;
						if (IS[iset_idx].size == 0)
							IS[iset_idx].active = FALSE;
						IS[fix_iset].involved = TRUE;
						if (IS[fix_iset].size == 0)
							IS[fix_iset].active = FALSE;
						assert(node_weight >= 0);
						break;
					}
				}
			}
			if (iSET_TOTAL_WEIGHT + node_weight <= MAX_ISET_WEIGHT)
				break;
		}
		if (node_weight > 0)
			add_new_iset_for_bnode(insert_node, node_weight);
		if (iSET_TOTAL_WEIGHT <= MAX_ISET_WEIGHT) {
			return TRUE;
		} else {
			return FALSE;
		}
	}
}

static int cut_by_ordered_maxsat_reasoning() {
	int i, k, node;

	build_iset_structures();

	k = FIRST_INDEX;
	while ((node = Candidate_Stack[k]) != DELIMITER) {
		if (node < 0) {
			node = -node;
			Candidate_Stack[k] = node;
			//idx = insert_vertex_with_weight_partition(node);
			insert_vertex_with_max3sat(node);
			//reasoning
			while (iSET_TOTAL_WEIGHT > MAX_ISET_WEIGHT) {
				build_node_isets();
				init_for_maxsat_reasoning();
				reasoning_with_up();
				reset_context();
				if (ptr(REASON_STACK) > 0) {
					split_conflicting_isets();
				} else {
					break;
				}
			}
			if (iSET_TOTAL_WEIGHT > MAX_ISET_WEIGHT) {
				Candidate_Stack[k] = -node;
				break;
			} else {
				NB_TOPK++;
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

static int NB_TOPK = 0;

static void build_iset_structures() {
	int i, node, idx;
	long long *nodes;
	int iset_len = 0;

	RESERVED_LENGTH = 0;
	NEW_NODE_IDX = 0;

	i = ptr(Candidate_Stack) - 2;
	for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[--i]) {
		if (node < 0) {
			RESERVED_LENGTH++;
		}
		idx = abs(node);
		if (idx > NEW_NODE_IDX) {
			NEW_NODE_IDX = idx;
		}
	}

	MAX_OLD_NODE = NEW_NODE_IDX;
	RESERVED_LENGTH = RESERVED_LENGTH * 2;

	long long *addr = Node_Degree + MAX_OLD_NODE + 1;

	for (i = 0; i < iSET_COUNT; i++) {
		iset_len += iSET_Size[i];
		IS[i].satisfied = FALSE;
		IS[i].used = FALSE;
		IS[i].involved = FALSE;
		IS[i].active = TRUE;
		IS[i].size = iSET_Size[i];
		IS[i].weight = iSET_Weight[i];
		IS[i].topk = 0;
		IS[i].nodes = addr;
		for (node = *(nodes = iSET[i]); node != NONE; node = *(++nodes)) {
			*(addr++) = node; //node
			*(addr++) = *(++nodes); //weight
			if (*(nodes) == IS[i].weight)
				IS[i].topk++;
		}
		*(addr++) = NONE;
		addr += RESERVED_LENGTH;
		assert(IS[i].size > 0 && IS[i].weight > 0);
	}
	iNode_TAIL = addr;

	//FIXED_NODES_STACK = (int *) (Candidate_Stack + ptr(Candidate_Stack));
	//SATISFIED_iSETS_STACK = (int *) (Vertex_UB + ptr(Candidate_Stack));
    FIXED_NODES_STACK = (int *) (Candidate_Stack + ptr(Candidate_Stack)+1);
    SATISFIED_iSETS_STACK = (int *) (Vertex_UB + ptr(Candidate_Stack)+1);
}

static void build_node_isets() {
	int node, i = ptr(Candidate_Stack) - 2;
	long long *nodes;
	for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[--i]) {
		if (node > 0) {
			iSET_Size[node] = 0;
			iSET[node][0] = NONE;
			Node_Value[node] = UNASSIGNED;
		} else {
			iSET_Size[-node] = 0;
			iSET[-node][0] = NONE;
			Node_Value[-node] = UNASSIGNED;
		}
	}

	for (i = 0; i < iSET_COUNT; i++) {
		if (IS[i].size > 0 && IS[i].active == TRUE) {
			IS[i].topk = 0;
			nodes = IS[i].nodes;
			for (node = *(nodes); node != NONE; node = *(++nodes)) {
				//assert(node <= MAX_SUBGRAPH_SIZE);
				iSET[node][iSET_Size[node]] = i;
				iSET[node][iSET_Size[node] + 1] = *(++nodes);
				iSET[node][iSET_Size[node] + 2] = NONE;
				if (*nodes == IS[i].weight)
					IS[i].topk++;

				iSET_Size[node] += 2;
			}
		}
	}
}

static int MATRIX_REBUILDED = 0;

static void rebuild_matrix(int start) {
	int i = start, j = 1, node, neibor, *neibors;

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		Candidate_Stack[i] = j;
		Second_Name[j] = node;
		Node_Degree[node] = j++;
		Node_Value[node] = ACTIVE;
	}

	MATRIX_SIZE = j - 1;
	MATRIX_ROW_WIDTH = MATRIX_SIZE / 8 + 1;

	memset(Adj_Matrix, 0, (MATRIX_SIZE + 1) * (MATRIX_ROW_WIDTH) * sizeof(char));

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		neibors = Node_Neibors[Second_Name[node]];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (Node_Value[neibor] == ACTIVE) {
				SET_EDGE(node, Node_Degree[neibor]);
				SET_EDGE(Node_Degree[neibor], node);
			}
		}
	}
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		Node_Value[Second_Name[node]] = PASSIVE;
		Node_Weight[node] = Top_Weight[Second_Name[node]];
	}
	MATRIX_REBUILDED++;
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

	printf("C %8d |%12lld |%8d %10d %12d %12d|%10d %10.2lf \n", Cursor_Stack[0] + 1, MAX_CLQ_WEIGHT, cut_ver, cut_inc, cut_iset, cut_satz, BRANCHING_COUNT, get_utime() - READ_TIME - INIT_TIME);
	fflush(stdout);
	total_cut_ver += cut_ver;
	cut_ver = 0;
	total_cut_inc += cut_inc;
	cut_inc = 0;
	total_cut_iset += cut_iset;
	cut_iset = 0;
    total_cut_satz += cut_satz;
    cut_satz = 0;
	Last_Idx = CURSOR;
	if (MAX_CLQ_WEIGHT == UPPER_WEIGHT_BOUND) {
		ptr(Cursor_Stack) = 1;
		ptr(Clique_Stack) = 0;
		Rollback_Point = NB_NODE + 1;
		CUR_CLQ_WEIGHT = 0;
		Vertex_UB[CURSOR]=MAX_CLQ_WEIGHT;
	}
}
static long long compute_subgraphs_weight(int start) {
	int i = start, j = 0, node, neibor, *neibors;
	long long max_weight = 0;
	int nb_node = 0, nb_edge = 0;

//	/*<TEST>*/
//	for (node = 1; node <= NB_NODE; node++)
//		assert(Node_State[node] == PASSIVE);
//	/*</TEST>*/

	j = 0;
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		Node_Value[node] = ACTIVE;
		Node_Weight[node] = Top_Weight[node];
		//Node_Degree[node] = j;
		Clique_Stack[node] = j;
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

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (Node_Value[neibor] == ACTIVE) {
				nb_edge++;
				j = Clique_Stack[node];
				iSET[j][iSET_Size[j]++] = neibor;
				Node_Weight[node] += Top_Weight[neibor];

				j = Clique_Stack[neibor];
				iSET[j][iSET_Size[j]++] = node;
				Node_Weight[neibor] += Top_Weight[node];
			}
		}
	}
	max_weight = 0;
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		j = Clique_Stack[node];
		iSET[j][iSET_Size[j]] = NONE;
		Node_Value[node] = PASSIVE;
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

	printf("C %8d |%12lld |%8d %10d %12d %12d|%10d %10.2lf\n", Cursor_Stack[0] + 1, MAX_CLQ_WEIGHT, cut_ver, cut_inc, cut_iset, cut_satz, BRANCHING_COUNT, get_utime() - READ_TIME - INIT_TIME);
	total_cut_ver += cut_ver;
	cut_ver = 0;
	total_cut_inc += cut_inc;
	cut_inc = 0;
	total_cut_iset += cut_iset;
	cut_iset = 0;
	total_cut_satz += cut_satz; cut_satz = 0;
	Last_Idx = CURSOR;
	ptr(Clique_Stack) = 0;
	Rollback_Point = NB_NODE + 1;
	CUR_CLQ_WEIGHT = 0;
}

static long long init_for_me(int start, long long *segment_counter, long long *where) {
	long long i, j, k, t, node;
	long long max_weight = 0, total_weight = 0;

	max_weight = compute_subgraphs_weight(start);
	if (max_weight + ptr(Candidate_Stack) >= STACK_LENGTH)
		return NONE;
	memset(segment_counter, 0, (max_weight + 1) * sizeof(long long));

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
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

	for (node = Vertex_UB[i = start]; node != DELIMITER; node = Vertex_UB[++i]) {
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

static int compute_subgraph_degree(int start) {
	int i = start, j = 0, node, neibor, *neibors, max_degree = 0;
	int nb_node = 0, nb_edge = 0;

	j = 0;
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		Node_Weight[node] = Top_Weight[node];
		Node_Value[node] = ACTIVE;
		Node_Degree[node] = 0;
		iSET_Size[node] = j;
		j++;
	}
	nb_node = j;
	N1_B = nb_node;

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (Node_Value[neibor] == ACTIVE) {
				nb_edge++;
				iSET[iSET_Size[node]][Node_Degree[node]++] = neibor;
				iSET[iSET_Size[neibor]][Node_Degree[neibor]++] = node;
				Node_Weight[node] += Top_Weight[neibor];
				Node_Weight[neibor] += Top_Weight[node];
			}
		}
	}
	max_degree = 0;
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		iSET[iSET_Size[node]][Node_Degree[node]] = NONE;
		Node_Value[node] = PASSIVE;
		if (Node_Degree[node] > max_degree)
			max_degree = Node_Degree[node];

	}

	return max_degree;
}

static int reduce_first_level_subgraphs_by_degree(int start) {
	long long *degree_counter, *where, neibor, *neibors;
	int end, p1, i, node = NONE, t, j, h, k;
	long long weight = 0;
	//int max_degree = 0;
	//CUR_MAX_NODE = 0;
	Max_Degree = compute_subgraph_degree(start);

	where = Candidate_Stack + ptr(Candidate_Stack) + 1;
	degree_counter = Vertex_UB + ptr(Candidate_Stack) + 1;
	memset(degree_counter, 0, (Max_Degree + 1) * sizeof(long long));

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
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

	for (node = Vertex_UB[i = start]; node != DELIMITER; node = Vertex_UB[++i]) {
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

		if (p1 < end && Node_Degree[node] == Node_Degree[Candidate_Stack[p1 + 1]]) {
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

				for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
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
				if (Node_Degree[neibor] != Node_Degree[Candidate_Stack[h - 1]]) {
					degree_counter[Node_Degree[neibor]] = h;
				}
			}
		p1++;
	}

	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		Vertex_UB[i] = Node_Weight[node];
		Node_Weight[node] = Top_Weight[node];
	}
	return FALSE;
}

static int reduce_first_level_subgraphs_by_weight(int start) {
	long long *neibors, neibor;
	long long *segment_counter, new_weight, total_weight = 0;
	int p1, i, node = NONE, t, j, head, head_node;
	int max_core = 0, pre_weight, cur_weight;

	long long *where = Candidate_Stack + ptr(Candidate_Stack) + 1;
	segment_counter = Vertex_UB + ptr(Candidate_Stack) + 1;

	total_weight = init_for_me(start, segment_counter, where);
	if (total_weight == NONE)
		return FALSE;

	p1 = start;
	max_core = Node_Weight[Candidate_Stack[p1]];
	while ((node = Candidate_Stack[p1]) != DELIMITER) {

		cur_weight = Node_Weight[node];

		if (cur_weight > max_core) {
			max_core = cur_weight;
		}
		Vertex_UB[p1] = cur_weight;

		if (Candidate_Stack[p1 + 1] != DELIMITER && cur_weight == Node_Weight[Candidate_Stack[p1 + 1]]) {
			segment_counter[cur_weight] = p1 + 1;
		}

		if (cur_weight == total_weight) {
			if (total_weight == MAX_CLQ_WEIGHT) {
				ptr(Clique_Stack) = 0;
				push(Candidate_Stack[CURSOR], Clique_Stack);
				while ((node = Candidate_Stack[p1++]) != DELIMITER)
					push(node, Clique_Stack);
				store_maximal_weighted_clique2();

				for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
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

		neibors = iSET[Clique_Stack[node]];

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

				if (head == p1 + 1 || new_weight > Node_Weight[Candidate_Stack[head - 1]]) {
					segment_counter[new_weight] = head;
				}
			}
		}
		total_weight -= Top_Weight[node];
		p1++;
	}
	for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
		Node_Weight[node] = Top_Weight[node];
	}
	if (max_core + CUR_NODE_WEIGHT > MAX_CLQ_WEIGHT) {
		CUR_MAX_NODE = 0;
		for (node = Candidate_Stack[i = start]; node != DELIMITER; node = Candidate_Stack[++i]) {
			if (Vertex_UB[i] > MAX_CLQ_WEIGHT - CUR_NODE_WEIGHT)
				break;
		}
		j = start;
		for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[++i]) {
			Vertex_UB[j] = Vertex_UB[i];
			Candidate_Stack[j++] = node;
			if (node > CUR_MAX_NODE)
				CUR_MAX_NODE = node;
		}
		Candidate_Stack[j] = DELIMITER;
		ptr(Candidate_Stack) = j + 1;
		NB_CANDIDATE = j - start;

		return FALSE;
	} else {
		Vertex_UB[CURSOR]=max_core + CUR_NODE_WEIGHT;
		return TRUE;
	}
}

static int cut_by_inc_ub() {
	int i = CURSOR, neibor,*neibors;
	int node=Candidate_Stack[CURSOR];
	int start=ptr(Candidate_Stack);
	unsigned char * adj_list;
	NB_CANDIDATE=0;
	CUR_MAX_NODE=0;
	long long max_weight=CUR_NODE_WEIGHT,max = 0;
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
	if((max+CUR_NODE_WEIGHT+CUR_CLQ_WEIGHT<=MAX_CLQ_WEIGHT)||(CUR_CLQ_WEIGHT+max_weight<=MAX_CLQ_WEIGHT)) { //
				cut_inc++;
				return TRUE;
			}
			if(NB_CANDIDATE==0) {
				if(CUR_CLQ_WEIGHT+CUR_NODE_WEIGHT>MAX_CLQ_WEIGHT)
				store_maximal_weighted_clique();
				return TRUE;
			}
			if(CUR_CLQ_SIZE==0) {
				if(NB_CANDIDATE<10&&cut_by_iset_less_vertices()==TRUE) {
					cut_iset++;
					return TRUE;
				} else if(LARGE_WEIGHT==TRUE && reduce_first_level_subgraphs_by_degree(start)) {
					cut_inc++;
					return TRUE;
				} else if(LARGE_WEIGHT==FALSE && reduce_first_level_subgraphs_by_weight(start)) {
					cut_inc++;
					return TRUE;
				} else if(REBUILD_MATRIX==TRUE || CUR_MAX_NODE > MATRIX_SIZE) {
					rebuild_matrix(start);
					REBUILD_MATRIX=TRUE;
				}
			}
			return FALSE;
		}

static void init_for_search() {
	cut_ver = 0;
	cut_inc = 0;
	cut_iset = 0;
	cut_satz = 0;
	total_cut_ver = 0;
	total_cut_inc = 0;
	total_cut_iset = 0;
	total_cut_satz = 0;

	Last_Idx = NB_NODE;
	NB_BACK_CLIQUE = 0;

	MAX_CLQ_SIZE = 0;
	ptr(Clique_Stack) = 0;
	ptr(Cursor_Stack) = 0;
	Rollback_Point = 0;

	MAX_CLQ_WEIGHT = 0;
	CUR_CLQ_WEIGHT = 0;

	if (OPT_CLQ_WEIGHT > 0) {
		MAX_CLQ_SIZE = INIT_CLQ_SIZE;
		MAX_CLQ_WEIGHT = OPT_CLQ_WEIGHT;

	} else if (INIT_CLQ_SIZE > 0) {
		MAX_CLQ_SIZE = INIT_CLQ_SIZE;
		MAX_CLQ_WEIGHT = INIT_CLQ_WEIGHT;
	}
	push(NB_NODE, Cursor_Stack);
}

static void allocate_memory() {
	int i;
	int size = MAX_SUBGRAPH_SIZE + 1;
	
	Second_Name = (int *) calloc((NB_NODE + 1), sizeof(int));
	MAX_ISET_COUNT = size;
	//iSET = (int **) malloc(size * sizeof(int *));

	iSET = (long long **) calloc(MAX_ISET_COUNT, sizeof(long long *));
	iSET[0] = (long long *) calloc(MAX_ISET_COUNT * (size * 2), sizeof(long long));
	for (i = 1; i < MAX_ISET_COUNT; i++) {
		iSET[i] = iSET[i - 1] + size * 2;
	}
	iSET_Size = (int *) calloc((NB_NODE + 1) *2, sizeof(int));


	iSET_Weight = (long long *) calloc(MAX_ISET_COUNT , sizeof(long long));
	iSET_Tested = (char *) calloc(MAX_ISET_COUNT , sizeof(char));
	//MaxCLQ_Stack = (int *) malloc(size * sizeof(int));
	Clique_Stack = (int *) calloc((NB_NODE + 1), sizeof(int));
	

	/* data structures for maxsat reasoning*/
#ifdef MaxSAT
	//IS = (int **) malloc(size * sizeof(int *));
	IS=(struct iSET_State*)calloc(MAX_ISET_COUNT, sizeof(struct iSET_State));
	//IS_HEAD = Node_Degree;
	UNIT_STACK = (int *) calloc((MAX_ISET_COUNT), sizeof(int));
	//TOP_UNIT_STACK = (int *) malloc((size) * sizeof(int));
	NEW_UNIT_STACK = (int *) calloc((MAX_ISET_COUNT) * 2, sizeof(int));
	REASON_STACK = (long long *) calloc((MAX_ISET_COUNT) * 4, sizeof(long long));
	TOPK_REDUCED_STACK=(int *) calloc((MAX_ISET_COUNT) * 10, sizeof(int));
#endif
}

static void search_maxclique(double cutoff, int using_init_clique) {
	int node;

	BRANCHING_COUNT = 0;
	if (using_init_clique == TRUE) {
		printf("C  ------------------------------------------------------------------------------------------\n");
		printf("C    Index |      Weight |NB_Vertex  NB_IncUB    NB_Binary   NB_Ordered|  NB_Branch      time\n");
	}
	while (CURSOR > 0) {
	    SEARCH_TIME = get_utime() - READ_TIME - INIT_TIME;
	    if (SEARCH_TIME >= cutoff){
//	        printf("Not solving to optimality; user time limit\n");
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

				if(Rollback_Point+MAX_SUBGRAPH_SIZE>=STACK_LENGTH) {
					printf("ERROR: the depth of search tree exceeds the limit of %d\n", STACK_LENGTH);
					exit(0);
				}

				if(cut_by_inc_ub()==TRUE

				||cut_by_binary_maxsat_reasoning()==TRUE
#ifdef MaxSAT
			|| (iSET_COUNT>5 && cut_by_ordered_maxsat_reasoning()==TRUE)
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
		printf("C  ------------------------------------------------------------------------------------------\n");
		printf("C %8d |%12lld |%8d %10d %12d %12d|%10d %10.2lf \n", CURSOR+1,MAX_CLQ_WEIGHT,cut_ver,cut_inc, cut_iset, cut_satz,BRANCHING_COUNT,SEARCH_TIME);
		total_cut_ver += cut_ver;
		total_cut_inc += cut_inc;
		total_cut_iset += cut_iset;
		total_cut_satz += cut_satz;
		printf("C  ------------------------------------------------------------------------------------------\n");
		printf("C %8d |%12lld |%8d %10d %12d %12d|%10d %10.2lf\n", CURSOR+1,MAX_CLQ_WEIGHT,total_cut_ver,total_cut_inc, total_cut_iset, total_cut_satz,BRANCHING_COUNT,SEARCH_TIME);
	}
}

static void check_maxw_clique() {
	int i, j, node1, node2;
	long long weight = 0;
	if (INIT_CLQ_WEIGHT < MAX_CLQ_WEIGHT) {
		for (i = 0; i < MAX_CLQ_SIZE; i++) {
			weight += Top_Weight[MaxCLQ_Stack[i]];
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
}

static void printMaxClique(char* input_file) {
	printf("M ");
//	ifstream FIC;
	FILE *fp ;
	char outfilename[100];
	printf("%s\n", input_file);
    strcpy(outfilename,resPath);
    strcat(outfilename,input_file);
    strcat(outfilename,"_TSM.csv");
	fp = fopen(outfilename, "w");
	if (INIT_CLQ_WEIGHT < MAX_CLQ_WEIGHT) {
	    fprintf(fp, "%lld ", MAX_CLQ_WEIGHT);
		for (int i = 0; i < MAX_CLQ_SIZE; i++) {
			printf("%d ", Old_Name[MaxCLQ_Stack[i]]);
			fprintf(fp, "%d ",Old_Name[MaxCLQ_Stack[i]]);
//			fprintf(fp, "%d ",MaxCLQ_Stack[i]);
		}
	} else {
	    fprintf(fp, "%lld ", INIT_CLQ_WEIGHT);
		for (int i = 0; i < MAX_CLQ_SIZE; i++) {
			printf("%d ", MaxCLQ_Stack[i]);
			fprintf(fp, "%d ", MaxCLQ_Stack[i]);
		}
	}
	printf("\n");
	fprintf(fp, "\n");
    fclose(fp); // WYY
}
static int MATRIX_LIMITATION = 2048;
static void build_init_matrix() {
	int node, neibor, *neibors;

	MATRIX_SIZE = MAX_SUBGRAPH_SIZE;
	/*allocate memory for matrix of subgraphs*/
	MATRIX_ROW_WIDTH = MATRIX_SIZE / 8 + 1;
	Adj_Matrix = (unsigned char *) malloc((MATRIX_SIZE + 1) * MATRIX_ROW_WIDTH * sizeof(char));
	memset(Adj_Matrix, 0, (MATRIX_SIZE + 1) * MATRIX_ROW_WIDTH * sizeof(char));

	/*build initial matrix*/
	for (node = 1; node <= MATRIX_SIZE; node++) {
		Second_Name[node] = node;
		Node_Weight[node] = Top_Weight[node];
		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			SET_EDGE(node, neibor);
			SET_EDGE(neibor, node);
		}
	}
}

static void reduce_instance_for_weight() {
	int i, j, nb, node, *neibors, *neibors2, *addr;
	MAX_SUBGRAPH_SIZE = 0;
	i = 0;
	while (Vertex_UB[i] <= INIT_CLQ_WEIGHT) {
		Node_Value[Candidate_Stack[i]] = PASSIVE;
		i++;
	}
	j = 0;

	for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[++i]) {
		Vertex_UB[j] = Vertex_UB[i];
		Candidate_Stack[j++] = node;
		Node_Value[node] = ACTIVE;
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
			if (Node_Value[node] == ACTIVE && New_Name[node] < i) {
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
		Node_Value[i] = PASSIVE;
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

	printf("I the reduced graph #node %d #edge %d #density %9.8f \n", NB_NODE, NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
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
	for (node = Candidate_Stack[i]; node != DELIMITER; node = Candidate_Stack[++i]) {
		if (Node_Weight[node] <= INIT_CLQ_WEIGHT) {
			Node_Value[node] = PASSIVE;
		} else {
			Candidate_Stack[j++] = node;
			Node_Value[node] = ACTIVE;
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
			if (Node_Value[node] == ACTIVE && New_Name[node] < i) {
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
		Node_Value[i] = PASSIVE;
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

//	printf("I the reduced graph: #node %d #edge %d #density %9.8f \n", NB_NODE, NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
	N0_A = NB_NODE;
	D0_A = ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1));
//	printf("I the largest subgraph is %d\n", MAX_SUBGRAPH_SIZE);
	INIT_TIME = get_utime() - READ_TIME;
//	printf("I Initializing Time: %4.2lf \n", INIT_TIME);
}

void print_version1() {
	printf("c Hello! I am TSM-MWC, a solver for the maximum weight clique problem, build at %s %s.\n", __TIME__, __DATE__);
#ifdef MaxSAT
	printf("c compiled with Two-stage MaxSAT Reasoning.\n");
#endif
	return;
}

static void check_result(char *input_file, char *result_file) {
	char * fileStyle = strrchr(input_file, '.') + 1;
	if (strcmp(fileStyle, "clq") == 0) {
		read_graph_node_node(input_file, 1);
	} else if (strcmp(fileStyle, "edges") == 0 || strcmp(fileStyle, "mtx") == 0) {
		read_graph_node_node(input_file, 2);
	} else if (FORMAT == 1) {
		read_graph_node_node(input_file, 1);
	} else if (FORMAT == 2) {
		read_graph_node_node(input_file, 2);
	} else {
		read_graph_node_node(input_file, 1);
	}
	printf("R Instance Information: #node=%d #edge=%d density=%9.8f\n", NB_NODE, NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
	check_clique_in_result_file(result_file);
}
//void parse_parmerters(int argc, char *argv[]) {
//	int i;
//	OPT_CLQ_WEIGHT = 0;
//	if (argc > 3) {
//		for (i = 2; i < argc; i++) {
//			if (strcmp(argv[i], "-o") == 0)
//				sscanf(argv[++i], "%d", &INIT_ORDERING);
//			else if (strcmp(argv[i], "-opt") == 0) {
//				sscanf(argv[++i], "%lld", &OPT_CLQ_WEIGHT);
//			} else if (strcmp(argv[i], "-f") == 0)
//				sscanf(argv[++i], "%d", &FORMAT);
//			else if (strcmp(argv[i], "-check") == 0) {
//				check_result(argv[1], argv[i + 1]);
//				exit(0);
//			} else if (strcmp(argv[i], "-i") == 0) {
//				sscanf(argv[++i], "%d", &START_MAXSAT_THD);
//			} else if (strcmp(argv[i], "-w") == 0) {
//				sscanf(argv[++i], "%d", &Weight_Mod);
//			} else if (strcmp(argv[i], "-matrix-size") == 0) {
//				sscanf(argv[++i], "%d", &MATRIX_LIMITATION);
//			}
//		}
//	}
//	printf("# begin searching on %s ...\n", argv[1]);
//	//printf("I INIT_ORDERING=%d FORMAT=%d Weight_Mod=%d\n", INIT_ORDERING, FORMAT, Weight_Mod);
//}

void clear_structures(){
	memset(Vertex_UB,0,MAX_NODE*2*sizeof(long long));
}

int tsm(char* File_Name1, const char* resPath1, int NB_NODE1, int NB_EDGE1, double cutoff, int** AdjacentList, int* Node_Degree1, int* Node_Weight1, int* Node_Bound1){

    NB_NODE = NB_NODE1;
    NB_EDGE = NB_EDGE1;

    File_Name = File_Name1;
    resPath = resPath1;

    READ_TIME = get_utime();

    Node_Neibors = (int **) malloc((NB_NODE + 1) * sizeof(int *));
	allcoate_memory_for_adjacency_list(NB_NODE, NB_EDGE, 0);

    Node_Neibors = AdjacentList;

    for (int i = 1; i <= NB_NODE; i++){
        Node_Degree[i] = Node_Degree1[i];
        Node_Weight[i] = Node_Bound1[i];
        Top_Weight[i] = Node_Weight1[i];
    }
	int ret = 0;
	FORMAT = 1;
	INIT_ORDERING = 1;
//	print_version1();
//	parse_parmerters(argc, argv);
	clear_structures();

    sort_by_degree_degeneracy_ordering();
    reduce_instance_for_degree();

    allocate_memory();
    build_init_matrix();
    init_for_search();
    search_maxclique(cutoff, TRUE);

    printMaxClique(File_Name);
//    check_maxw_clique();

//	printf(">>%s |V| %d |E| %d D %0.8lf max_weight %lld branches %d read_time %4.2lf init_time %4.2lf search_time %4.2lf total_time %4.2lf \n", (strrchr(File_Name, '/') == NULL )? File_Name : strrchr(File_Name, '/') + 1,
//	NB_NODE_O, NB_EDGE_O,
//	((float) NB_EDGE_O * 2 / NB_NODE_O / (NB_NODE_O - 1)),
//	MAX_CLQ_WEIGHT, BRANCHING_COUNT, READ_TIME, INIT_TIME, SEARCH_TIME,
//	READ_TIME + INIT_TIME + SEARCH_TIME);

	return MAX_CLQ_WEIGHT;
}


