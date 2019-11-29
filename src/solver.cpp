#include "solver.h"
#include <cmath>
#include <limits>

namespace MWC {
    //compute the reduced graph by removing vertices that are predicted to be 0
    void Solver::compute_reduced_graph(){
        nb_nodes = r.get_reduced_problem_size();
        AdjacentList = (int **) malloc((nb_nodes) * sizeof(int *));
        Node_Degree = (int *) malloc((nb_nodes) * sizeof(int));
        Node_Weight = (int *) malloc((nb_nodes) * sizeof(int));
        Node_Bound = (int *) malloc((nb_nodes) * sizeof(int));
        nodes_list = std::vector<std::uint32_t>(nb_nodes);
        std::vector<std::vector<std::uint32_t>> adj_list = g.get_adj_list();

        if (nb_nodes == g.size()){
            //directly copy the original graph
            nb_edge = g.get_num_edges();
            for (auto i = 0u; i < g.size(); ++i){
                nodes_list[i] = i;
                Node_Degree[i] = g.get_degree(i);
                Node_Weight[i] = g.get_weight(i);
                Node_Bound[i] = g.get_bound(i);
                AdjacentList[i] = (int *) malloc(Node_Degree[i] * sizeof(int));
                for (auto j = 0u; j < g.get_degree(i); ++j){
                    AdjacentList[i][j] = adj_list[i][j];
                }
            }
        } else{
            // compute the reduce graph
            std::uint32_t count = 0u;
            for (auto i = 0u; i < g.size(); ++i){
                if (r.get_predicted_value(i) == 1){
                    nodes_list[count++] = i;
                }
            }
            nb_edge = 0u;
            std::uint32_t idx, k1, k2, k3;
            std::vector<std::uint32_t> list(nb_nodes);
            for(auto i = 0u; i < nb_nodes; ++i){
                idx = nodes_list[i];
                Node_Weight[i] = g.get_weight(idx);
                Node_Bound[i] = g.get_weight(idx);
                std::sort(adj_list[idx].begin(), adj_list[idx].end());
                k1 = 0u, k2 = 0u, k3 = 0u;
                while (k1 < nb_nodes && k2 < g.get_degree(idx)){
                    if(nodes_list[k1] > adj_list[idx][k2]){
                        k2++;
                    } else if (nodes_list[k1] < adj_list[idx][k2]){
                        k1++;
                    } else {
                        list[k3] = k1;
                        Node_Bound[i] += g.get_weight(nodes_list[k1]);
                        k1++, k2++, k3++;
                    }
                }
                Node_Degree[i] = k3;
                AdjacentList[i] = (int *) malloc((k3) * sizeof(int));
                for (auto j = 0u; j < k3; ++j){
                    AdjacentList[i][j] = list[j];
                }
                nb_edge += k3;
            }
        }
    }

    void Solver::solve_mwc_tsm(){
        std::cout << "Using the exact solver TSM to solve the MWC problem" << std::endl;
        compute_reduced_graph();
        char File_Name[g.get_file_name().size()+1];
        strcpy(File_Name, g.get_file_name().c_str());
        char resPath[res_path.size()+1];
        strcpy(resPath, res_path.c_str());

        // solve the reduced graph using TSM
        objVal = tsm(File_Name, resPath, nb_nodes, nb_edge, cutoff, AdjacentList, Node_Degree, Node_Weight, Node_Bound);

        // read the best solution found by TSM
        std::string best_file_name = res_path + g.get_file_name() + "_TSM.csv";
        std::ifstream best_file(best_file_name);
        std::uint32_t v;
        best_file >> objVal;
        while(best_file >> v) {
            best_sol.push_back(nodes_list[v-1]);
        }
        best_file.close();
        remove(best_file_name.c_str());
    }

    // solve the reduced graph using WLMC
    void Solver::solve_mwc_wlmc(){
        std::cout << "Using the exact solver WLMC to solve the MWC problem" << std::endl;
        compute_reduced_graph();
        objVal = wlmc(nb_nodes, nb_edge, cutoff, AdjacentList, Node_Degree, Node_Weight, Node_Bound);
    }

    // solve the reduced graph using LSCC
    void Solver::solve_mwc_lscc(){
        std::cout << "Using the heuristic method LSCC to solve the MWC problem" << std::endl;
        compute_reduced_graph();
        objVal = lscc(nb_nodes, nb_edge, cutoff, AdjacentList, Node_Degree, Node_Weight);
    }

    // solve the reduced graph using fastWCLQ
    void Solver::solve_mwc_fastwclq(){
        std::cout << "Using the heuristic method FastWCLQ to solve the MWC problem" << std::endl;
        compute_reduced_graph();
        objVal = fastwclq(nb_nodes, nb_edge, cutoff, AdjacentList, Node_Degree, Node_Weight, Node_Bound);
    }
}
