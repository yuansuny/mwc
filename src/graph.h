#ifndef GRAPH_H
#define GRAPH_H
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <sstream>
#include <cmath>
#include <random>
#include <iterator>

namespace MWC {
  class Graph {
    const std::string file_name;
    const std::string input_dir;
    std::uint32_t n_nodes;
    std::uint32_t n_edges;
    double density;
    std::vector<std::vector<std::uint32_t>> adj_list;
    std::vector<std::uint32_t> degree;
    std::vector<double> weight;
    std::vector<double> bound;
    double max_weight = 0, max_bound = 0;
    std::uint32_t max_degree = 0;
    std::vector<bool> optimal_solution;
    void read_graph();
    void read_optimal_solution();
    
  public:
    explicit Graph(std::string file_name, std::string input_dir);

    // Size of the graph (i.e. number of nodes).
    std::uint32_t size() const { return n_nodes; }

    std::uint32_t get_num_edges() const { return n_edges; }

    std::vector<std::vector<std::uint32_t>> get_adj_list() const {return adj_list; }

    std::uint32_t get_degree(std::uint32_t i) const { return degree[i]; }

    double get_weight(std::uint32_t i) const { return weight[i]; }

    double get_bound(std::uint32_t i) const { return bound[i]; }

    std::uint32_t get_max_degree() const { return max_degree; }

    double get_max_weight() const { return max_weight; }

    double get_max_bound() const { return max_bound; }

    double get_density() const{ return density; }

    // Optimal solution of node x[i]
    bool get_optimal_value(std::uint32_t i) const { return optimal_solution[i]; }

    std::string get_file_name() const { return file_name; }

  };
}

#endif
