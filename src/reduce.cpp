#include "reduce.h"
#include <cmath>
#include <limits>

namespace MWC {
    Reduce::Reduce(const Graph& g, double threshold_c, double threshold_r) : g{g}, threshold_c{threshold_c}, threshold_r{threshold_r} {}

    void Reduce::random_sampling(std::uint32_t idx) {
        std::uint32_t nb_candidates = g.size();
        std::vector<std::uint32_t> candidate_sorted_idx(nb_candidates);
        std::iota(candidate_sorted_idx.begin(), candidate_sorted_idx.end(), 0u);
        std::uint32_t k1, k2, k3, sel_idx;
        while (nb_candidates > 0u){
            sel_idx = candidate_sorted_idx[rand() % nb_candidates];
            samples[idx].push_back(sel_idx);
            objs[idx] += g.get_weight(sel_idx);
            if (is_neighbor_sorted[sel_idx] == 0){
                std::sort(adj_list[sel_idx].begin(), adj_list[sel_idx].end());
                is_neighbor_sorted[sel_idx] = 1;
            }

            if (samples[idx].size() == 1){
                for (std::uint32_t i = 0u; i < g.get_degree(sel_idx); ++i){
                    candidate_sorted_idx[i] = adj_list[sel_idx][i];
                }
                nb_candidates = g.get_degree(sel_idx);
            } else {
                k1 = 0u, k2 = 0u, k3 = 0u;
                while (k1 < nb_candidates && k2 < g.get_degree(sel_idx)){
                    if(candidate_sorted_idx[k1] > adj_list[sel_idx][k2]){
                        k2++;
                    } else if (candidate_sorted_idx[k1] < adj_list[sel_idx][k2]){
                        k1++;
                    } else {
                        candidate_sorted_idx[k3] = adj_list[sel_idx][k2];
                        k1++, k2++, k3++;
                    }
                }
                nb_candidates = k3;
            }
        }
    }

    void Reduce::single_thread_sampling() {
        const auto n = g.size();
        sample_size = sample_factor * sqrt(g.get_num_edges());
        std::cout << "sample size is " << sample_size << "\n";
        samples.resize(sample_size);
        objs = std::vector<double>(sample_size, 0.0);
        adj_list = g.get_adj_list();
        is_neighbor_sorted = std::vector<bool>(n, 0);
        srand (time(NULL));
        for(std::uint32_t i = 0u; i < sample_size; ++i) {
            random_sampling(i);
        }
        std::uint32_t idx = -1;
        best_obj_sampling = 0;
        for (std::uint32_t i = 0u; i < sample_size; ++i){
            if (objs[i] > best_obj_sampling){
                best_obj_sampling = objs[i];
                idx = i;
            }
        }
        std::cout << "best obj in sampling is " << best_obj_sampling << "\n";
        best_sol_sampling = samples[idx];
    }

    void Reduce::removing_variables_none() {
        std::cout << "no problem reduction, solving the original problem" << std::endl;
        const auto n = g.size();
        predicted_value = std::vector<bool>(n, 1);
        compute_reduced_problem_size();
    }

    void Reduce::removing_variables_rbm() {
        std::cout << "problem reduction using ranking-based measure with threshold " << threshold_r << std::endl;
        single_thread_sampling();
        compute_ranking_based_measure();
        const auto n = g.size();
        predicted_value = std::vector<bool>(n, 0);
        for (auto i = 0u; i < n; ++i){
            if (ranking_scores[i] < threshold_r){
                predicted_value[i] = 0;
            } else{
                predicted_value[i] = 1;
            }
        }
        compute_reduced_problem_size();
    }

    void Reduce::compute_ranking_based_measure() {
        std::cout << "computing ranking based measure " << std::endl;
        const auto n = g.size();
        std::vector<std::uint32_t> sort_idx(sample_size);
        std::iota(sort_idx.begin(), sort_idx.end(), 0);
        std::vector<double> objs_copy(objs);
        std::sort(sort_idx.begin(), sort_idx.end(), [&objs_copy](std::uint32_t i1, std::uint32_t i2) {return objs_copy[i1] > objs_copy[i2];});
        std::vector<std::uint32_t> rank = std::vector<std::uint32_t>(sample_size);
        for (auto i = 0u; i < sample_size; i++){
            rank[sort_idx[i]] = i;
        }
        ranking_scores = std::vector<float>(n, 0.0);
        for (auto i = 0u; i < sample_size; ++i){
            for (auto j = 0u; j < samples[i].size(); ++j){
                ranking_scores[samples[i][j]] += 1.0/(rank[i]+1);
            }
        }
        max_rbm = 0;
        for (auto i = 0u; i < n; ++i){
            if (ranking_scores[i] > max_rbm){
                max_rbm = ranking_scores[i];
            }
        }
    }

    void Reduce::removing_variables_cbm(){
        std::cout << "problem reduction using correlation-based measure with threshold " << threshold_c << std::endl;
        single_thread_sampling();
        compute_correlation_based_measure();
        const auto n = g.size();
        predicted_value = std::vector<bool>(n, 0);
        for (auto i = 0u; i < n; ++i){
            if (corr_xy[i] > threshold_c){
                predicted_value[i] = 1;
            } else{
                predicted_value[i] = 0;
            }
        }
        compute_reduced_problem_size();
    }

    void Reduce::compute_correlation_based_measure(){
        std::cout << "computing correlation based measure " << std::endl;
        const auto n = g.size();
        double mean_y = 0.0;
        for (auto i = 0u; i < sample_size; ++i){
            mean_y += objs[i];
        }
        mean_y = mean_y/sample_size;
        std::vector<double> diff_y = std::vector<double>(sample_size);
        double variance_y = 0.0, sum_diff_y = 0.0;
        for (auto i = 0u; i < sample_size; ++i){
            diff_y[i] = objs[i] - mean_y;
            variance_y += diff_y[i]*diff_y[i];
            sum_diff_y += diff_y[i];
        }

        std::vector<double> mean_x(n, 0.0);
        std::vector<double> S1(n, 0.0);
        for (auto i = 0u; i < sample_size; ++i){
            for (auto j = 0u; j < samples[i].size(); ++j){
                mean_x[samples[i][j]] += 1.0/sample_size;
                S1[samples[i][j]] += diff_y[i];
            }
        }

        std::vector<double> variance_x(n, 0.0);
        std::vector<double> variance_xy(n, 0.0);
        corr_xy = std::vector<float>(n, 0.0);
        max_cbm = -1.0;
        for (auto i = 0u; i < n; ++i){
            variance_x[i] = mean_x[i]*(1-mean_x[i])*sample_size;
            variance_xy[i] = (1-mean_x[i])*S1[i] - mean_x[i]*(sum_diff_y - S1[i]);
            if (variance_x[i] > 0){
                corr_xy[i] = variance_xy[i]/sqrt(variance_x[i]*variance_y);
            }else if (mean_x[i] == 1.0){
                corr_xy[i] = 1.0;
            }else {
                corr_xy[i] = -1.0; // mean_x[i] == 0
            }
            if (corr_xy[i] > max_cbm){
                max_cbm = corr_xy[i];
            }
        }
    }

    void Reduce::constructing_test_data(){
        single_thread_sampling();
        compute_correlation_based_measure();
        compute_ranking_based_measure();
        std::string test_s = g.get_file_name() + test_data_name + ".csv";
        char test_data[test_s.size()+1];
        strcpy(test_data, test_s.c_str());
        std::ofstream test_file(test_data, std::ios::trunc);
        if (! test_file.is_open()){
            std::cout << "Cannot open the output file " <<  test_data << "\n";
        }

        for (auto i = 0u; i < g.size(); ++i){
            test_file << 0 << " ";
            test_file << "1:" << std::fixed << std::setprecision(6) << g.get_density() <<  " ";
            test_file << "2:" << std::fixed << std::setprecision(6) << g.get_weight(i) / g.get_max_weight() <<  " ";
            test_file << "3:" << std::fixed << std::setprecision(6) << static_cast<double>(g.get_degree(i)) / g.get_max_degree() <<  " ";
            test_file << "4:" << std::fixed << std::setprecision(6) << g.get_bound(i) / g.get_max_bound() <<  " ";
            test_file << "5:" << std::fixed << std::setprecision(6) << ranking_scores[i] / max_rbm << " ";
            test_file << "6:" << std::fixed << std::setprecision(6) << corr_xy[i] / max_cbm << " " << "\n";
        }
        test_file.close();
    }

    void Reduce::loading_output_data(){
        int n = g.size();
        predicted_value = std::vector<bool>(n, 0);
        std::string output_s = g.get_file_name() + output_file_name +  ".csv";
        char output_file[output_s.size()+1];
        strcpy(output_file, output_s.c_str());
        std::ifstream predicted_file(output_file);
        if (! predicted_file){
            std::cout << "fail to read the predicted file \n";
        }
        bool value;
        for (int i = 0; i < n; ++i){
            predicted_file >> value;
            predicted_value[i] = value;
        }
        predicted_file.close();
        remove(output_file);
    }

    // Removing variables using SVM
    void Reduce::removing_variables_svm(){
        std::cout << "problem reduction using SVM" << std::endl;
        constructing_test_data();
        std::string test_s = g.get_file_name() + test_data_name  + ".csv";
        std::string output_s = g.get_file_name() + output_file_name  + ".csv";
        std::string model_s = training_data_dir + svm_training_model_name;
        char test_data[test_s.size()+1];
        char output_file[output_s.size()+1];
        char model_file[model_s.size()+1];
        strcpy(test_data, test_s.c_str());
        strcpy(output_file, output_s.c_str());
        strcpy(model_file, model_s.c_str());

        svm_predict_model(test_data, model_file, output_file, probability);
        remove(test_data);

        loading_output_data();
        compute_reduced_problem_size();
        std::cout << "problem reduction using SVM done" << std::endl;
    }


    // Removing variables using Linear SVM (fast)
    void Reduce::removing_variables_svm_linear(){
        std::cout << "problem reduction using linear SVM" << std::endl;
        constructing_test_data();
        std::string test_s = g.get_file_name() + test_data_name  + ".csv";
        std::string output_s = g.get_file_name() + output_file_name  + ".csv";
        std::string model_s = training_data_dir + linear_svm_training_model_name;
        char test_data[test_s.size()+1];
        char output_file[output_s.size()+1];
        char model_file[model_s.size()+1];
        strcpy(test_data, test_s.c_str());
        strcpy(output_file, output_s.c_str());
        strcpy(model_file, model_s.c_str());

        linear_svm_predict_model(test_data, model_file, output_file, probability);
        remove(test_data);

        loading_output_data();
        compute_reduced_problem_size();
        std::cout << "Linear SVM prediction done" << std::endl;
    }

    void Reduce::compute_reduced_problem_size(){
        const auto n = g.size();
        std::uint32_t count = 0u;
        for (auto i = 0u; i < n; ++i){
            if(predicted_value[i] == 1){
                count++;
            }
        }
        num_variable_left = count;
        std::cout << "proportion of remaining problem size is " << static_cast<double>(count) / n  << std::endl;
    }

}
