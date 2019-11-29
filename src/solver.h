#ifndef SOLVER_H
#define SOLVER_H

#include "graph.h"
#include "reduce.h"
#include <iostream>
#include <vector>
#include <algorithm>

#include "lscc.h"
#include "fastwclq.h"

extern "C" {
#include "tsm.h"
#include "wlmc.h"
}

namespace MWC {
  class Solver {
    const Graph& g;
    const Reduce& r;
    const double cutoff;
    double objVal;
    std::vector<std::uint32_t> best_sol;
    std::string res_path = "../results/";
    // compute reduced graph
    void compute_reduced_graph();
    std::uint32_t nb_nodes;
    std::uint32_t nb_edge;
    std::vector<std::uint32_t> nodes_list;
    int** AdjacentList;
    int* Node_Degree;
    int* Node_Weight;
    int* Node_Bound;

  public:
    
    // Builds a solver for graph g.
    explicit Solver(const Graph& g, const Reduce& r, const float cutoff) : g{g}, r{r}, cutoff{cutoff} {}

    void solve_mwc_tsm();
    void solve_mwc_wlmc();
    void solve_mwc_lscc();
    void solve_mwc_fastwclq();

    double get_objective_value() const { return objVal; }

    std::vector<std::uint32_t> get_best_solution() const { return best_sol; }

  };
}

#endif
