#include "training.h"

namespace MWC {
    Training::Training(std::vector<std::string> training_files, std::string input_dir, double alpha, int kernel_type) :
        training_files{training_files}, input_dir{input_dir}, alpha{alpha}, kernel_type{kernel_type} {
        std::cout << "number of training graphs is: " << training_files.size() << "\n";
        construct_training_set();
    }

    void Training::construct_training_set(){
        std::string train_s = train_data_dir  + train_file_name;
        char train_data[train_s.size()+1];
        strcpy(train_data, train_s.c_str());

        std::ofstream train_file(train_data, std::ios::trunc);
        if (! train_file.is_open()){
            std::cout << "Cannot open the output file " <<  train_data << "\n";
            return;
        }
        train_file.close();

        std::uint64_t num0 = 0;
        std::uint64_t num1 = 0;
        for (auto d = 0u; d < training_files.size(); ++d){
            const auto graph = Graph(training_files[d], input_dir);
            auto reduce = Reduce(graph, 0.0, 0.01); //thresholds for ranking and correlation based measures will not be used.
            reduce.single_thread_sampling();
            reduce.compute_correlation_based_measure();
            reduce.compute_ranking_based_measure();
            train_file.open(train_data, std::ios::app);
            for (auto i = 0u; i < graph.size(); ++i){
                if (graph.get_optimal_value(i) == 1)
                    num1++;
                else
                    num0++;
                train_file << graph.get_optimal_value(i) << " ";
                train_file << "1:" << std::fixed << std::setprecision(6) << graph.get_density() <<  " ";
                train_file << "2:" << std::fixed << std::setprecision(6) << graph.get_weight(i) / graph.get_max_weight() <<  " ";
                train_file << "3:" << std::fixed << std::setprecision(6) << static_cast<double>(graph.get_degree(i)) / graph.get_max_degree() <<  " ";
                train_file << "4:" << std::fixed << std::setprecision(6) << graph.get_bound(i) / graph.get_max_bound() <<  " ";
                train_file << "5:" << std::fixed << std::setprecision(6) << reduce.get_rbm_value(i) / reduce.get_max_rbm() << " ";
                train_file << "6:" << std::fixed << std::setprecision(6) << reduce.get_cbm_value(i) / reduce.get_max_cbm() << " " << "\n";
            }
            train_file.close();
        }
        std::cout << "num0 is " << num0 << "; " << "num1 is " << num1 <<  std::endl;
        weight = alpha * num0/num1;
    }

    void Training::generate_training_model_svm(){
        std::string train_s = train_data_dir  + train_file_name;
        std::string model_s = train_data_dir + svm_train_model_name;
        char train_data[train_s.size()+1];
        char model_file[model_s.size()+1];
        strcpy(train_data, train_s.c_str());
        strcpy(model_file, model_s.c_str());
        std::cout << "weight of class 1 is " << weight << std::endl;
        std::cout << "kernel type is " << kernel_type << std::endl;
        std::cout << "output probability is " << prob << std::endl;
        svm_train_model(train_data, model_file, weight, kernel_type, prob);

        const int rem_result = remove(train_data);
        if(rem_result == 0){
            std::cout << "Successfully remove training data file" << std::endl;
        } else {
            std::cout << "No such training data file " << std::endl;
        }
    }

    void Training::generate_training_model_svm_linear(){
        std::string train_s = train_data_dir  + train_file_name;
        std::string model_s = train_data_dir + linear_svm_train_model_name;
        char train_data[train_s.size()+1];
        char model_file[model_s.size()+1];
        strcpy(train_data, train_s.c_str());
        strcpy(model_file, model_s.c_str());
        std::cout << "weight of class 1 is " << weight << std::endl;
        std::cout << "output probability is " << prob << std::endl;
        linear_svm_train_model(train_data, model_file, weight);

        const int rem_result = remove(train_data);
        if(rem_result == 0){
            std::cout << "Successfully remove training data file" << std::endl;
        } else {
            std::cout << "No such training data file " << std::endl;
        }
    }
}
