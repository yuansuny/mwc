// =====================================================================================
//
//       Filename:  fastwclq.cpp
//
//    Description:  This is a solver for weighted maximum clique problem, which interleaves
//					between construction and simplification.
//
//        Version:  1.0
//        Created:  2015.12
//       Revision:  none
//       Compiler:  g++ v4.7
//
//         Author:  Shaowei Cai, caisw@ios.ac.cn
//					& Jinkun Lin, jkunlin@gmail.com
//   Organization:  Key State Lab of Computer Science, Institute of Software, CAS;
//					School of EECS, Peking University
//
// =====================================================================================


#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <set>
#include <map>
#include <vector>
#include <algorithm>
#include <set>
#include <string.h>

using namespace std;

const float       MY_RAND_MAX_FLOAT = 10000000.0;
const int   	  MY_RAND_MAX_INT =   10000000;
const float 	  BASIC_SCALE = 0.0000001; //1.0f/MY_RAND_MAX_FLOAT;

vector<vector<long>> adjacency_list;
vector<long> vertex_neighbor_weight;
vector<long> vertex_weight;

//vector<long> neighbor_hash_sum;


//reduction
vector<long> hit_in_common_neighbor;
vector<long> vertex_to_removed;
vector<long> working_vertex;
vector<long> next_working_vertex;
vector<bool> is_pending;
vector<vector<long>::size_type> index_in_working_vertex;


//solutions
vector<long> solution;
vector<long> best_solution;
long best_solution_weight=0;
long solution_weight;

long tries;
double best_solution_time;
long best_solution_try;

//input parameter
long size_threshold;
int t;

struct Remaining_vertex {
	vector<long> vertex;
	vector<vector<long>::size_type> index;

	vector<long>::iterator begin() {
		return vertex.begin();
	}
	vector<long>::iterator end() {
		return vertex.end();
	}
	void init(vector<long>::size_type vertex_size) {
		vertex.reserve(vertex_size);
		index.resize(vertex_size);
		for (vector<long>::size_type i = 1; i < vertex_size; ++i) {
			vertex.push_back(i);
			index[i] = i - 1;
		}
	}
	void remove(long v) {
		index[*vertex.rbegin()] = index[v];
		vertex[index[v]] = *vertex.rbegin();
		vertex.pop_back();
	}

	vector<long>::size_type size() {
		return vertex.size();
	}

	bool empty() {
		return vertex.empty();
	}
};
Remaining_vertex remaining_vertex;


//build adjacency_list
void build(string file_name) {
	ifstream in_file(file_name);
	if (! in_file.is_open()) {
		cout << "in_file error" << endl;
		exit(1);
	}

	long vertex_count;

	//get vertex_count
	string line;
	istringstream is;
	string p, tmp;
	do {
		getline(in_file, line);
		is.clear();
		is.str(line);
		is >> p >> tmp >> vertex_count;
	} while (p != "p");
	
	//reading vertex weight
	vertex_weight.resize(vertex_count + 1);
	long v,w;
	for(vector<vector<long>>::size_type i=1; i<vertex_weight.size(); ++i){
	    in_file >> tmp >> v >> w;
		if(tmp!="v") break;
		vertex_weight[v]=w;
		
		//v=i;
		//vertex_weight[v]=v%200+1;
	}

	adjacency_list.resize(vertex_count + 1);
	vertex_neighbor_weight.resize(vertex_count + 1, 0);

	long v1, v2;
	while (in_file >> tmp >> v1 >> v2) {
		adjacency_list[v1].push_back(v2);
		adjacency_list[v2].push_back(v1);
		vertex_neighbor_weight[v1] += vertex_weight[v2];
		vertex_neighbor_weight[v2] += vertex_weight[v1];
	}
	in_file.close();
	

	solution.reserve(adjacency_list.size());
	best_solution.reserve(adjacency_list.size());
	
	hit_in_common_neighbor.resize(adjacency_list.size());
	working_vertex.reserve(adjacency_list.size());
	next_working_vertex.reserve(adjacency_list.size());
	is_pending.resize(adjacency_list.size());
	index_in_working_vertex.resize(adjacency_list.size());

	remaining_vertex.init(adjacency_list.size());

}

void print_vec(vector<long> & container) {
	cout << '{';
	for (auto i : container) {
		cout << i << ' ';
	}
	cout << '}';
	cout << '\t' << "size = " << container.size();
	cout << endl;
}

long upper_bound(long v) {
	if (adjacency_list[v].empty()) {
		return vertex_weight[v];
	}
	long largest_weight_neighbor;
	long largest_weight = 0;
	for (auto u : adjacency_list[v]) {
		if (vertex_weight[u] > largest_weight) {
			largest_weight = vertex_weight[u];
			largest_weight_neighbor = u;
		}
	}

	long v1, v2;
	if (adjacency_list[v].size() < adjacency_list[largest_weight_neighbor].size()) {
		v1 = v;
		v2 = largest_weight_neighbor;
	}
	else {
		v1 = largest_weight_neighbor;
		v2 = v;
	}
	
	for (auto i : adjacency_list[v1]) {
		hit_in_common_neighbor[i] = false;
	}
	for (auto i : adjacency_list[v2]) {
		hit_in_common_neighbor[i] = true;
	}
	
	long common_neigbor_sum_weight = 0;
	for (auto i : adjacency_list[v1]) {
		if (hit_in_common_neighbor[i]) {
			common_neigbor_sum_weight += vertex_weight[i];
		}
	}

	long value_with_largest = vertex_weight[v] + vertex_weight[largest_weight_neighbor] + common_neigbor_sum_weight;
	long value_without_largest = vertex_weight[v] + vertex_neighbor_weight[v] - vertex_weight[largest_weight_neighbor];
	
	return value_with_largest > value_without_largest ? value_with_largest : value_without_largest;
}

void simplify_iterative() {
	long threshold_weight_degree = best_solution_weight;
	working_vertex.clear();
	next_working_vertex.clear();

	for (auto v : remaining_vertex) {
		working_vertex.push_back(v);
		is_pending[v] = true; //true if v in working_vertex or next_working_vertex
	}

	while (!working_vertex.empty()) {
		for (vector<long>::size_type i = 0; i < working_vertex.size(); ++i) {
			auto v = working_vertex[i];
			if (vertex_weight[v] + vertex_neighbor_weight[v] <= threshold_weight_degree ||
					upper_bound(v) <= threshold_weight_degree) {
				for (auto u : adjacency_list[v]) {
					vector<long>::size_type j = 0;
					for (; j < adjacency_list[u].size(); ++j) {
						if (adjacency_list[u][j] == v) {
							break;
						}
					}
					adjacency_list[u][j] = *adjacency_list[u].rbegin();
					adjacency_list[u].pop_back();
					vertex_neighbor_weight[u] -= vertex_weight[v];
					//if u is not in working_vertex and next_working_vertex, add it to next_working_vertex
					if (!is_pending[u]) {
						next_working_vertex.push_back(u);
						is_pending[u] = true;
					}
				}
				adjacency_list[v].clear();
				remaining_vertex.remove(v);
			}
			is_pending[v] = false;
		}
		working_vertex.swap(next_working_vertex);
		next_working_vertex.clear();
	}
}

//adjacency_list, vertex_weight, vertex_neighbor_weight
void simplify() {
	//simplify by degree
	long threshold_weight_degree = best_solution_weight;
	
	for (auto v : remaining_vertex) {
		if (vertex_weight[v] + vertex_neighbor_weight[v] <= threshold_weight_degree) {
			vertex_to_removed.push_back(v);
		}
	}

	while (!vertex_to_removed.empty()) {
		long i = *vertex_to_removed.rbegin();
		vertex_to_removed.pop_back();
		//remove i from N(v), for each v in N(i)
		for (auto v : adjacency_list[i]) {
			vector<long>::size_type j = 0;
			for (; j < adjacency_list[v].size(); ++j) {
				if (adjacency_list[v][j] == i) {
					break;
				}
			}
			adjacency_list[v][j] = *adjacency_list[v].rbegin();
			adjacency_list[v].pop_back();
			vertex_neighbor_weight[v] -= vertex_weight[i];
			if (vertex_weight[v] + vertex_neighbor_weight[v] + vertex_weight[i] > threshold_weight_degree &&
					vertex_weight[v] + vertex_neighbor_weight[v] <= threshold_weight_degree) {
				vertex_to_removed.push_back(v);
			}
		}
		//remove i
		adjacency_list[i].clear();
		remaining_vertex.remove(i);
	}
}


template<typename T>
bool is_neighbor(T v1, T v2) {//check v1 in adj list of v2
	//if(neighbor_hash_sum[v1+v2]==0) return false; 

	if (adjacency_list[v1].size()<adjacency_list[v2].size()){
		for (auto n : adjacency_list[v1]) {
			if (v2 == n) {
				return true;
			}
		}
		return false;

	}
	else{
		for (auto n : adjacency_list[v2]) {
			if (v1 == n) {
				return true;
			}
		}
		return false;
	}
}

void output_graph_size() {
	long edge_count = 0;
	for (auto v : remaining_vertex) {
		edge_count += adjacency_list[v].size();
	}
	edge_count /= 2;
	cout << "p edge " << remaining_vertex.size() << ' ' << edge_count << endl;
}

void output_best_solution() {

	cout << "the best found clique has weight " << best_solution_weight  << endl;
	std::sort(best_solution.begin(), best_solution.end());
	
	for (auto v : best_solution) {
		cout << v << ' ';
	}
	cout << endl;
	
}

void update_best_solution() {
	best_solution.clear();
	for (auto v : solution) {
		best_solution.push_back(v);
	}
}

bool compare_vertex (long v1, long v2) {
	return vertex_neighbor_weight[v1]/t + vertex_weight[v1] > vertex_neighbor_weight[v2]/t + vertex_weight[v2];
}


vector<long> start_vertices;
long untest_pointer;

vector<vector<long>> adjacency_cand_neighbor_weight;
vector<bool> is_computed; 

vector<long> candidates;
vector<long> cand_neighbor_weight;
vector<bool> is_in_candidates;

vector<bool> is_addv_neighbor; // indicates whether a candidate vertex is adjacent to the add_v

//vector<long> remove_cand_vertices;//in each step
//vector<bool> is_removed;

long start_bms_count=1;
long min_bms_count;
long max_bms_count;
long real_bms_count;


bool is_new_graph = true;

void init()
{
	cand_neighbor_weight.resize(adjacency_list.size(),0);
	is_in_candidates.resize(adjacency_list.size(),0);
	is_computed.resize(adjacency_list.size(),0);
	is_addv_neighbor.resize(adjacency_list.size(),0);
	adjacency_cand_neighbor_weight.resize(adjacency_list.size());
	for (vector<long>::size_type v = 1; v < adjacency_list.size(); ++v){
		adjacency_cand_neighbor_weight[v].resize(adjacency_list[v].size());
	}
	
	real_bms_count = min_bms_count;	
}

int construct()
{
	solution.clear();
	candidates.clear();
	solution_weight=0;

	long startv;
	vector<long>::size_type index, tmp_index;
	
	if (is_new_graph)
	{
		start_vertices = remaining_vertex.vertex;
		untest_pointer = 0;
		
		for (vector<long>::size_type v = 1; v < adjacency_list.size(); ++v)
			is_computed[v]=0;
	}
	
	
	if(static_cast<std::vector<int>::size_type>(untest_pointer) == start_vertices.size())
	{
		untest_pointer = 0;
		
		real_bms_count = real_bms_count*2;
		if(real_bms_count > max_bms_count) real_bms_count = min_bms_count;
	}

	long best_score;
	long tmp_score;
			
	//pick the starting vertex
	index = untest_pointer+rand()%(start_vertices.size()-untest_pointer);
	startv = start_vertices[index];
	best_score = vertex_weight[startv]+vertex_neighbor_weight[startv]/t;
	for (long i=1; i<=start_bms_count; ++i){
		tmp_index = untest_pointer+rand()%(start_vertices.size()-untest_pointer);
		tmp_score = vertex_weight[start_vertices[tmp_index]]+vertex_neighbor_weight[start_vertices[tmp_index]]/t;
		if (tmp_score > best_score){
			best_score = tmp_score;
			index = tmp_index;
		}
	}
	startv = start_vertices[index];
	std::swap(start_vertices[index], start_vertices[untest_pointer++]);

	solution.push_back(startv);
	solution_weight+=vertex_weight[startv];
	
	//initialize the set of candidate vertices S = N(startv)
	for (auto u : adjacency_list[startv]) {
			candidates.push_back(u);
			is_in_candidates[u]=1;
	}
	
	//initialize the cand_neighbor_weight value of vertices in candidate set S
	long i=0;
	if (is_computed[startv]==0) {
		for (auto v : candidates) {
			for (auto n : adjacency_list[v]){
				if (is_in_candidates[n]==1)
					cand_neighbor_weight[v] += vertex_weight[n];
			}
			//record the beginning cand_neighbor_weight value of vertices in the beginning candidate set S
			adjacency_cand_neighbor_weight[startv][i++] = cand_neighbor_weight[v];
		}
		
		is_computed[startv]=1;
	}
	else {
		i=0;
		for (auto v : adjacency_list[startv]){
				cand_neighbor_weight[v] = adjacency_cand_neighbor_weight[startv][i++];
		}
	}
	

	long add_v;
	long max_score;
	
	while (!candidates.empty()) {

		//pick add_v
		if (candidates.size() < static_cast<std::vector<int>::size_type>(real_bms_count))
		{
			max_score = 0;
			index = 0;
			for (vector<long>::size_type i = 0; i < candidates.size(); ++i) {
				tmp_score = cand_neighbor_weight[candidates[i]]/t + vertex_weight[candidates[i]];
				if (tmp_score > max_score) {
					max_score = tmp_score;
					index = i;
				}
			}
		
		}
		else
		{
			index = rand()%candidates.size();
			max_score = cand_neighbor_weight[candidates[index]]/t + vertex_weight[candidates[index]];
	
			for (long i=1; i<real_bms_count; ++i){
				tmp_index = rand()%candidates.size();
				tmp_score = cand_neighbor_weight[candidates[tmp_index]]/t + vertex_weight[candidates[tmp_index]];
				if (tmp_score > max_score) {
					max_score = tmp_score;
					index = tmp_index;
				}
			}
		}
		add_v = candidates[index];
		
		//upper bound prune
		if (solution_weight+cand_neighbor_weight[add_v] + vertex_weight[add_v]<=best_solution_weight) {
		
			for (auto v : candidates)
				is_in_candidates[v]=0;

			for (auto u : adjacency_list[startv]) {
				cand_neighbor_weight[u]=0;
			}
			
			return -1;
		}
		
		solution.push_back(add_v);
		solution_weight+=vertex_weight[add_v];
		

		//remove add_v and update its neighbors information
		for (auto u : adjacency_list[add_v]) {
			if (is_in_candidates[u]==1)
				cand_neighbor_weight[u] -= vertex_weight[add_v];
		}
		is_in_candidates[add_v]=0;
		candidates[index]=*(candidates.end() - 1);
		candidates.pop_back();

		for (auto v : adjacency_list[add_v]) {
			if (is_in_candidates[v]==1)
				is_addv_neighbor[v] = 1;
		}

		
		for (vector<long>::size_type i = 0; i < candidates.size(); ) {
			//remove the vertice doesn't belong to the neighborhood of add_v
			
			long cur_v = candidates[i];

			if (is_addv_neighbor[cur_v]==0){
				//update
				for (auto u : adjacency_list[cur_v]) {
					if (is_in_candidates[u]==1)
						cand_neighbor_weight[u] -= vertex_weight[cur_v];
				}
				is_in_candidates[cur_v]=0;
				candidates[i]=*(candidates.end() - 1);
				candidates.pop_back();
			}
			else {
				is_addv_neighbor[cur_v]=0; // erase the value here, making this array clean after the step.
				++i;
			}
		}

	}
	
	for (auto u : adjacency_list[startv]) {
		cand_neighbor_weight[u]=0;
	}
	
	return 0;
	
}



vector<long>::size_type binary_search(const vector<long> &array, long value) {
	vector<long>::size_type left = 0, right = array.size();
	while (left != right) {
		vector<long>::size_type middle = (right + left) / 2;
		if (array[middle] == value) {
			return middle;
		}
		else if (array[middle] < value) {
			left = middle + 1;
		}
		else {
			right = middle;
		}
	}
	return array.size();
}

bool verify_simple(string file_name) {
	cout << "verifying..." << endl;
	ifstream in_file(file_name);
	if (! in_file.is_open()) {
		cout << "in_file error" << endl;
		exit(1);
	}

	long vertex_count;

	//get vertex_count
	string line;
	istringstream is;
	string p, tmp;
	do {
		getline(in_file, line);
		is.clear();
		is.str(line);
		is >> p >> tmp >> vertex_count;
	} while (p != "p");
	
	//reading vertex weight
	vector<long> vw;
	vw.resize(vertex_count + 1);
	long v,w;
	for(vector<vector<long>>::size_type i=1; i<vw.size(); ++i){
	    in_file >> tmp >> v >> w;
		vw[v]=w;
	}

	// check solution weight
	long sw = 0;
	for (auto v : best_solution) {
		sw += vw[v];
	}
	if (sw != best_solution_weight) {
		cout << "wrong weight!" << endl;
		return false;
	}

	// adjacency list
	vector<vector<long>> adj_list;
	adj_list.resize(vertex_count + 1);
	long v1, v2;
	while (in_file >> tmp >> v1 >> v2) {
		adj_list[v1].push_back(v2);
		adj_list[v2].push_back(v1);
	}
	in_file.close();

	//check clique
	for (vector<long>::size_type i = 0; i < best_solution.size(); ++i) {
		long v1 = best_solution[i];
		for (vector<long>::size_type j = i + 1; j < best_solution.size(); ++j) {
			long v2 = best_solution[j];
			vector<long>::size_type k = 0;
			for (; k < adj_list[v1].size(); ++k) {
				if (v2 == adj_list[v1][k]) {
					break;
				}
			}
			if (k >= adj_list[v1].size()) {
				cerr << "wrong anser: " << v1 << " is not neighbor of " << v2 << "!" << endl;
				return false;
			}
		}
	}
	cout << "solution verified." << endl;
	return true;
}

bool verify (string file_name) 
{
	cout << "verifying..." << endl;
	
	//verify clique
	std::sort(best_solution.begin(), best_solution.end());
	
	vector<vector<long>> solution_matrix(best_solution.size());
	for (vector<long> & neighbor_list : solution_matrix) {
		neighbor_list.resize(best_solution.size(), 0);
	}
	
	ifstream in_file(file_name);
	if (! in_file.is_open()) {
		cout << "in_file error" << endl;
		exit(1);
	}
	
	string line;
	istringstream is;
	string c, tmp;
	long v1, v2;
	
	do {
		getline(in_file, line);
		is.clear();
		is.str(line);
		is >> c >> v1 >> v2;
	} while (c != "e"); //read the first edge
	
	
	do {
		auto v1_index = binary_search(best_solution, v1);
		if (v1_index == best_solution.size()) {
			continue;
		}
		auto v2_index = binary_search(best_solution, v2);
		if (v2_index == best_solution.size()) {
			continue;
		}
		solution_matrix[v1_index][v2_index] = 1;
		solution_matrix[v2_index][v1_index] = 1;
	} while (in_file >> tmp >> v1 >> v2);
	
	
	for (vector<vector<long>>::size_type i = 0; i < solution_matrix.size(); ++i) {
		for (vector<long>::size_type j = i + 1; j < solution_matrix.size(); ++j) {
			if (solution_matrix[i][j] != 1) {
				cerr << "wrong answer: violate clique property" << endl;
				cerr << "vertcies " << best_solution[i] << " and " << best_solution[j]<< " are not adjacent." << endl;
				return false;
			}
		}
	}
	
	//verify clique weight
	long verify_best_solution_weight = 0;
	for (auto v : best_solution) {
		verify_best_solution_weight += vertex_weight[v];
	}
	
	if (verify_best_solution_weight != best_solution_weight) {
		cerr << "wrong answer: weight." << endl;
		cerr << "verified weight of best solution is " << verify_best_solution_weight <<endl;
		cerr << "but claimed weight of best solution is " << best_solution_weight <<endl;
		return false;
	}
	
	cout << "solution verified." << endl;
	return true;

}

long simp_count=0;

bool better_since_simp=true;

//int main(int argc, char const *argv[]) {

int fastwclq(int vertex_count, int nb_edge, double cutoff_time, int** AdjacentList, int* Node_Degree, int* Node_Weight, int* Node_Bound){


    int seed = rand()%1000;

	long maxtries=2000000000;
	bool exact=false;

	min_bms_count = 4;
	max_bms_count = 64;
	t=2;
	size_threshold = 100000;
	
//	build(filename);


	//reading vertex weight
	vertex_weight.resize(vertex_count + 1);
	for(int i = 0; i < vertex_count; i++){
		vertex_weight[i+1] = Node_Weight[i];
	}

	adjacency_list.resize(vertex_count + 1);
	vertex_neighbor_weight.resize(vertex_count + 1, 0);

	for (int i = 0; i < vertex_count; i++){
	    for (int j = 0; j < Node_Degree[i]; j++){
	        adjacency_list[i+1].push_back(AdjacentList[i][j]+1);
	    }
	    vertex_neighbor_weight[i+1] = Node_Bound[i] - Node_Weight[i];
	}

	solution.reserve(adjacency_list.size());
	best_solution.reserve(adjacency_list.size());

	hit_in_common_neighbor.resize(adjacency_list.size());
	working_vertex.reserve(adjacency_list.size());
	next_working_vertex.reserve(adjacency_list.size());
	is_pending.resize(adjacency_list.size());
	index_in_working_vertex.resize(adjacency_list.size());

	remaining_vertex.init(adjacency_list.size());

	
	clock_t start = clock();
	
	init();

	for(tries=1; tries<=maxtries; tries++) {
	
		if (tries%1000000==0) srand(seed++); 

		if ((double) ( clock() - start) / CLOCKS_PER_SEC > cutoff_time) break;

		construct();
		
		is_new_graph=false;

		if (solution_weight > best_solution_weight) {
			
			update_best_solution();
			best_solution_weight=solution_weight;
			best_solution_time = (double) ( clock() - start) / CLOCKS_PER_SEC;
			best_solution_try = tries;
			
			better_since_simp=true;
		}
		
		if(better_since_simp)
		{
			if (remaining_vertex.size() > static_cast<std::vector<int>::size_type>(size_threshold)) {
				simplify();
			}
			else {
				simplify_iterative();
			}

			better_since_simp=false;
			is_new_graph=true;
			simp_count++;
			
			if (remaining_vertex.empty()) {
				exact=true;
				break;
			}
		} 
	}
	
	/*
	cout << best_solution_weight<<' '<< best_solution_time<<' '<<best_solution_try;
	if (exact) cout<<" exact";
	else cout << " heuristic";
	
	cout<< endl <<tries<<" total tries "<<simp_count<<" simps";
	cout << endl;
	output_best_solution();*/
	
	cout << best_solution_weight<<' '<< best_solution_time<<' '<<best_solution_try;
	if (exact) cout<<" x";
	else cout<<" h";

	cout<<" "<<tries<<" "<<simp_count;
	cout << endl;

//	verify(argv[1]);
//	verify_simple(argv[1]);
//	verify_simple(filename);


//	output_best_solution();
//	output_graph_size();
	return best_solution_weight;
}
