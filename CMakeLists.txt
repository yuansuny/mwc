cmake_minimum_required(VERSION 2.8.4)

project(MWC)

set(CMAKE_CXX_FLAGS                 "${CMAKE_CXX_FLAGS} -std=c++14 -O3 -flto -Wall -fPIC")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY  "${CMAKE_CURRENT_SOURCE_DIR}/build")

FILE(GLOB SOURCE_FILES src/*.cpp src/*/*.c src/*/*.cpp src/*/*/*.c)

add_executable( MWC ${SOURCE_FILES})

target_include_directories(MWC PRIVATE 
						"${CMAKE_CURRENT_SOURCE_DIR}/src/svm"
						"${CMAKE_CURRENT_SOURCE_DIR}/src/linear_svm"
						"${CMAKE_CURRENT_SOURCE_DIR}/src/linear_svm/blas"
						"${CMAKE_CURRENT_SOURCE_DIR}/src/solvers"
						)
