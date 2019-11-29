#include "solver.h"
#include <cmath>
#include <limits>

namespace MWC {
    void Solver::solve_mwc_tsm(){
        //re-construct the graph by removing vertices predicted to be 0
        std::uint32_t nb_nodes = r.get_reduced_problem_size();
        std::vector<std::uint32_t> nodes_list(nb_nodes);
        int** AdjacentList = (int **) malloc((nb_nodes + 1) * sizeof(int *)); //indexed from 1;
        int* Node_Degree = (int *) malloc((nb_nodes + 1) * sizeof(int));   //indexed from 1;
        int* Node_Weight = (int *) malloc((nb_nodes + 1) * sizeof(int));   //indexed from 1;
        int* Node_Bound = (int *) malloc((nb_nodes  + 1) * sizeof(int));    //indexed from 1;
        std::uint32_t count = 0u;
        for (auto i = 0u; i < g.size(); ++i){
            if (r.get_predicted_value(i) == 1){
                nodes_list[count++] = i;
            }
        }
        std::uint32_t nb_edge = 0u;
        std::uint32_t idx, k1, k2, k3;
        std::vector<std::vector<std::uint32_t>> adj_list = g.get_adj_list();
        std::vector<std::uint32_t> list(nb_nodes);
        for(auto i = 0u; i < nb_nodes; ++i){
            idx = nodes_list[i];
            Node_Weight[i+1] = g.get_weight(idx);
            Node_Bound[i+1] = g.get_weight(idx);
            std::sort(adj_list[idx].begin(), adj_list[idx].end());
            k1 = 0u, k2 = 0u, k3 = 0u;
            while (k1 < nb_nodes && k2 < g.get_degree(idx)){
                if(nodes_list[k1] > adj_list[idx][k2]){
                    k2++;
                } else if (nodes_list[k1] < adj_list[idx][k2]){
                    k1++;
                } else {
                    list[k3] = k1+1;
                    Node_Bound[i+1] += g.get_weight(nodes_list[k1]);
                    k1++, k2++, k3++;
                }
            }
            Node_Degree[i+1] = k3;
            AdjacentList[i+1] = (int *) malloc((k3+1) * sizeof(int));
            for (auto j = 0u; j < k3; ++j){
                AdjacentList[i+1][j] = list[j];
            }
            AdjacentList[i+1][k3] = -1;
            nb_edge += k3;
        }

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
}
