#include "graph.h"
#include <cmath>
#include <random>
#include <iterator>
#include <algorithm>

namespace MWC {
    Graph::Graph(std::string file_name, std::string input_dir) :  file_name{file_name}, input_dir{input_dir} {
        std::cout << file_name << "\n";
        read_graph();
        read_optimal_solution();
    }

    void Graph::read_optimal_solution(){
        std::string opt_file_name = input_dir + file_name + ".sol";
        std::ifstream opt_file(opt_file_name);
        if (!opt_file){
            std::cout << "optimal solution is not provided \n";
//             exit(1);
            return;
        }
        std::string line;
        bool READ_Point = 0;
        std::uint32_t node;
        std::vector<std::uint32_t> opt_sol;
        while(!opt_file.eof()) {
            getline(opt_file, line);
            if (line[0] == 'E' || line[0] == '-') {
                break;
            }
            if (READ_Point){
                std::stringstream stream(line);
                while (stream >> node) {
                    opt_sol.push_back(node - 1);
                }
            }
            if (line[0] == 'O'){
                READ_Point = 1;
            }
        }
        double opt_obj = 0;
        optimal_solution = std::vector<bool>(n_nodes, 0);
        for (auto i = 0u; i < opt_sol.size(); ++i){
            opt_obj += weight[opt_sol[i]];
            optimal_solution[opt_sol[i]] = 1;
        }
        std::cout << "optimal objective value is " << opt_obj << "\n";
    }

    void Graph::read_graph(){
        //It only supports .wclq input graph, indexed from 1.
        std::string input_file = input_dir  + file_name + ".wclq";
        std::ifstream file(input_file);
        std::string line, s1, s2;
        std::uint32_t v1, v2, ne = 0u;
        std::uint32_t idx;
        double w;

        while(!file.eof()) {
            getline(file, line);
            if (line[0] == 'p') {
                std::stringstream stream(line);
                stream >> s1 >> s2 >> n_nodes >> n_edges;
                adj_list.resize(n_nodes);
                weight = std::vector<double>(n_nodes, 0);
                degree = std::vector<std::uint32_t>(n_nodes, 0);
                bound = std::vector<double>(n_nodes, 0);
                std::cout << "number of nodes is " << n_nodes << "; number of edges is " << n_edges << std::endl;
            }
            if (line[0] == 'v'){
                std::stringstream stream(line);
                // if it is unweighted graph, assign weight to vertices according to w = v % 200 + 1.
                // stream >> s1 >> v1;
                // w = v1 % 200 + 1;
                // else reading vertex and weight
                stream >> s1 >> v1 >> w;

                weight[v1-1] = w;
                bound[v1-1] = w;
            }
            if (line[0] == 'e'){
                std::stringstream stream(line);
                stream >> s1 >> v1 >> v2;
                for (idx = 0u; idx < adj_list[v1-1].size(); ++idx){
                    if (adj_list[v1-1][idx] == v2 - 1){
                        break;
                    }
                }
                if (idx == adj_list[v1-1].size()){
                    adj_list[v1-1].push_back(v2-1);
                    adj_list[v2-1].push_back(v1-1);
                    degree[v1-1] += 1;
                    degree[v2-1] += 1;
                    bound[v1-1] += weight[v2-1];
                    bound[v2-1] += weight[v1-1];
                    ne++;
                }
            }
        }
        n_edges = ne;
        density = 2.0*n_edges/n_nodes/(n_nodes-1);
        std::cout << "number of undirected edges is " << n_edges << std::endl;

        for (auto i = 0u; i < n_nodes; ++i){
            if (weight[i] > max_weight){
                max_weight = weight[i];
            }
            if (degree[i] > max_degree){
                max_degree = degree[i];
            }
            if (bound[i] > max_bound){
                max_bound = bound[i];
            }
        }
    }
}
