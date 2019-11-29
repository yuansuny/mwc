#ifndef REDUCE_H
#define REDUCE_H
#include "graph.h"

extern "C" {
#include "svm_predict_model.h"
#include "linear_svm_predict_model.h"
}

#include <random>
#include <algorithm>
#include <iterator>
#include <iostream>
#include <numeric>      // std::iota
#include <vector>
#include <cstring>
#include <string>
#include <time.h>
#include <sys/time.h>
#include <iomanip>

namespace MWC {
    class Reduce{
        const Graph& g;
        double threshold_c;
        double threshold_r;
        const std::string training_data_dir = "../train_data/";
        const std::string svm_training_model_name = "svm_train_model";
        const std::string linear_svm_training_model_name = "linear_svm_train_model";
        const std::string test_data_name = "_test_data";
        const std::string output_file_name = "_predicted_value";
        const std::uint32_t sample_factor = 10;
        std::uint32_t sample_size;
        int probability = 0;
        std::vector<std::vector<std::uint32_t>> samples;
        std::vector<double> objs;
        double best_obj_sampling;
        std::vector<std::uint32_t> best_sol_sampling;
        std::vector<std::vector<std::uint32_t>> adj_list;
        std::vector<bool> is_neighbor_sorted;
        float max_cbm, max_rbm;
        std::vector<bool> predicted_value;
        std::vector<float> ranking_scores;
        std::vector<float> corr_xy;

        std::uint32_t num_variable_left;
        void constructing_test_data();
        void loading_output_data();
        void random_sampling(std::uint32_t idx);


        public:
            // Reduce the size of graph g.
            explicit  Reduce(const Graph& g, double threshold_c, double threshold_r);
            void single_thread_sampling();
            void removing_variables_rbm();
            void removing_variables_cbm();
            void removing_variables_svm();
            void removing_variables_svm_linear();
            void removing_variables_none();
            double get_objective_value_sampling() const { return best_obj_sampling; }
            bool get_predicted_value(std::uint32_t i) const { return predicted_value[i]; }
            float get_cbm_value(std::uint32_t i) const { return corr_xy[i]; }
            float get_rbm_value(std::uint32_t i) const { return ranking_scores[i]; }
            float get_max_cbm() const { return max_cbm; }
            float get_max_rbm() const { return max_rbm; }
            void compute_reduced_problem_size();
            void compute_correlation_based_measure();
            void compute_ranking_based_measure();
            std::uint32_t get_reduced_problem_size() const { return num_variable_left; }
            std::vector<std::uint32_t> get_best_sol_sampling() const { return best_sol_sampling; }
    };
}

#endif
