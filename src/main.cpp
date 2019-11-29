#include "graph.h"
#include "solver.h"
#include "reduce.h"
#include "training.h"
#include <iostream>
#include <time.h>
#include <sys/time.h>

double get_wall_time(){
    struct timeval time;
    if (gettimeofday(&time,NULL)){
        return 0;
    }
    return (double)time.tv_sec + (double)time.tv_usec * .000001;
}

void exit_and_help(){
	std::cout << "Usage: ./MWC [options] datafile" << std::endl;
	std::cout << "options: " << std::endl;
	std::cout << "-m : set problem reduction method (default 3)" << std::endl;
	std::cout << "0 -- no problem reduction" << std::endl;
	std::cout << "1 -- correlation-based measure" << std::endl;
	std::cout << "2 -- ranking-based measure" << std::endl;
	std::cout << "3 -- kernel SVM, dual (training and testing are slow)" << std::endl;
	std::cout << "4 -- linear SVM, primal (training and testing are fast)" << std::endl;
	std::cout << "-n : if training is needed (default 0)" << std::endl;
	std::cout << "0 -- training is not required; using ML model already trained" << std::endl;
	std::cout << "1 -- training is required; train a ML model to use" << std::endl;
	std::cout << "-k kernel_type : set type of kernel function for kernel SVM (default 2)" << std::endl;
	std::cout << "0 -- linear: u'*v" << std::endl;
	std::cout << "1 -- polynomial: (gamma*u'*v + coef0)^degree" << std::endl;
	std::cout << "2 -- radial basis function: exp(-gamma*|u-v|^2)" << std::endl;
	std::cout << "3 -- sigmoid: tanh(gamma*u'*v + coef0)" << std::endl;
	std::cout << "-t : set the cutoff time in seconds (default 1000)" << std::endl;
	std::cout << "-c : set the threshold for correlation-based measure (default 0.0)" << std::endl;
	std::cout << "-r : set the threshold for ranking-based measure (default 0.01)" << std::endl;
	std::cout << "-a : set the penalty for miss-classifying positive data for SVM em*num0/num1 (default 10)" << std::endl;
	exit(1);
}

int main(int argc, char* argv[]) {
    using namespace MWC;

    int    param_redu_method = 3; //problem reduction methods: 0 (none); 1 (correlation-based measure); 2 (ranking-based measure); 3 (kernel SVM, dual); 4 (linear SVM, primal).
    int    param_training    = 0;  //if training is required: 0 (not required), 1 (required).
    double param_cutoff      = 1000; //cutoff time in seconds.
    double param_threshold_r = 0.01; //threshold for ranking-based measure.
    double param_threshold_c = 0.0;  //threshold for correlation-based measure.
    double param_threshold_a = 10;   //penalty for miss-classifying positive data: param_thre_m*num0/num1.
    int    param_kernel_type = 2;    //kernel SVM type: 0 (linear); 1 (polynomial); 2 (RBF); 3 (sigmoid)

    // parse options (parameters)
	for(int i = 1; i < argc; ++i){
		if(argv[i][0] != '-'){
		    break;
		}
		if(++i >= argc){
		    exit_and_help();
		}
		switch(argv[i-1][1]){
			case 'm':
				param_redu_method = std::atoi(argv[i]);
				break;
			case 'n':
				param_training = std::atoi(argv[i]);
				break;
            case 't':
                param_cutoff = std::stod(argv[i]);
                break;
            case 'c':
                param_threshold_c = std::stod(argv[i]);
                break;
            case 'r':
                param_threshold_r = std::stod(argv[i]);
                break;
            case 'a':
                param_threshold_a = std::stod(argv[i]);
                break;
            case 'k':
				param_kernel_type = std::atoi(argv[i]);
				break;
			default:
				std::cout << "Unknown option: " << argv[i-1][1] << std::endl;
				exit_and_help();
		}
	}
	std::string input_file_name = argv[argc-1];

    // specify training graphs; optimal solutions for the training graphs must be provided.
    std::vector<std::string> training_file_name{"brock200_2", "brock200_4", "brock400_2",  "brock400_4", "DSJC500.5",
    "gen400_p0.9_75", "C125.9", "C250.9","gen200_p0.9_55", "gen200_p0.9_44", "MANN_a27", "p_hat700-3","p_hat700-2",
    "p_hat700-1", "p_hat300-3", "p_hat300-2", "p_hat300-1", "keller4", "p_hat1000-1", "p_hat1000-2", "p_hat1000-3",
    "p_hat1500-1",  "p_hat1500-2", "DSJC1000.5", "hamming10-2", "san1000"};
    const std::string input_dir = "../datasets/";
    const std::string output_dir = "../results/";
    std::uint32_t runs = 1u;

    if (param_training == 1){
        auto training = Training(training_file_name, input_dir, param_threshold_a, param_kernel_type);
        if (param_redu_method == 3){
            training.generate_training_model_svm();
        } else if (param_redu_method == 4){
            training.generate_training_model_svm_linear();
        }
    }


    std::string output_obj_filename, output_time_filename;
    output_obj_filename = output_dir + input_file_name + "_res_obj.csv";
    output_time_filename = output_dir + input_file_name + "_res_time.csv";
    std::ofstream output_file_obj (output_obj_filename, std::ios::trunc);
    std::ofstream output_file_time (output_time_filename, std::ios::trunc);

    if (output_file_obj.is_open()){
        output_file_obj << "|V|, " << "Y_s, " << "|V_s|, " << "Y" << std::endl;
    } else{
        std::cout << "Cannot open the output file " + output_obj_filename << std::endl;
        return 0;
    }
    output_file_obj.close();

    if (output_file_time.is_open()){
        output_file_time << "t_read, " << "t_reduce, " << "t_total" << std::endl;
    } else{
        std::cout << "Cannot open the output file " + output_time_filename << std::endl;
        return 0;
    }
    output_file_time.close();

    for (auto i = 0u; i < runs; ++i){
        double w0 = get_wall_time();
        const auto graph = Graph(input_file_name, input_dir);
        std::cout << "Original number of nodes is " << graph.size() << std::endl;
        output_file_obj.open(output_obj_filename, std::ios::app);
        output_file_obj << graph.size() <<", ";

        double w1 = get_wall_time();
        std::cout << "Reading time is " << w1 - w0 << "s" << std::endl;
        output_file_time.open(output_time_filename, std::ios::app);
        output_file_time << w1 - w0 <<", ";

        auto reduce = Reduce(graph, param_threshold_c, param_threshold_r);

        if (param_redu_method == 0){
            reduce.removing_variables_none();
        } else if (param_redu_method == 1){
            reduce.removing_variables_cbm();
        } else if (param_redu_method == 2){
            reduce.removing_variables_rbm();
        } else if (param_redu_method == 3){
            reduce.removing_variables_svm();
        } else if (param_redu_method == 4){
            reduce.removing_variables_svm_linear();
        } else {
            std::cout << "The problem reduction method is not supported" << std::endl;
            exit_and_help();
        }

        output_file_obj << reduce.get_objective_value_sampling() <<", ";
        std::cout << "Best objective value found from sampling is  " << reduce.get_objective_value_sampling() << std::endl;

        output_file_obj << reduce.get_reduced_problem_size() <<", ";
        std::cout << "Number of nodes left is " << reduce.get_reduced_problem_size()  << std::endl;

        double w2 = get_wall_time();
        std::cout << "Reduction time is  " << w2 - w1 << "s" << std::endl;
        output_file_time << w2 - w1 <<", ";

        auto solver = Solver(graph, reduce, param_cutoff-(w2-w0));
        solver.solve_mwc_tsm();

        if (solver.get_objective_value() > reduce.get_objective_value_sampling()){
            output_file_obj << solver.get_objective_value() << std::endl;
            std::cout << "Best objective value found is  " << solver.get_objective_value() << std::endl;
        } else {
            output_file_obj << reduce.get_objective_value_sampling() << std::endl;
            std::cout << "Best objective value found is  " << reduce.get_objective_value_sampling() << std::endl;
        }
        output_file_obj.close();

        auto w3 = get_wall_time();
        std::cout << "Total time is  " << w3 - w1 << "s" << std::endl;
        output_file_time << w3 - w1 << std::endl;
        output_file_time.close();

        if (i == 0u){
            auto best_sol = solver.get_best_solution();
            std::string output_sol_filename;
            output_sol_filename = output_dir + input_file_name + ".sol";
            std::ofstream output_file_sol (output_sol_filename, std::ios::trunc);
            output_file_sol << "CLIQUE_SECTION" << std::endl;
            for (auto j = 0u; j < best_sol.size(); ++j){
                output_file_sol << best_sol[j]+1 << std::endl;
            }
            output_file_sol << "EOF" << std::endl;
            output_file_sol.close();
        }
    }
    return 0;
}
