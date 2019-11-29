#ifndef SOLVER_H
#define SOLVER_H

#include "graph.h"
#include "reduce.h"
#include <iostream>
#include <vector>
#include <algorithm>

extern "C" {
#include "tsm.h"
}

namespace MWC {
  class Solver {
    const Graph& g;
    const Reduce& r;
    const double cutoff;
    double objVal;
    std::vector<std::uint32_t> best_sol;
    std::string res_path = "../results/";
    
  public:
    
    // Builds a solver for graph g.
    explicit Solver(const Graph& g, const Reduce& r, const float cutoff) : g{g}, r{r}, cutoff{cutoff} {}

    void solve_mwc_tsm();

    double get_objective_value() const { return objVal; }

    std::vector<std::uint32_t> get_best_solution() const { return best_sol; }

  };
}

#endif
