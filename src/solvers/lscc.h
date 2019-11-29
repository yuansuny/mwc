#ifndef LSCC_H
#define LSCC_H

#include<limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <sstream>
#include <fstream>
#include <string.h>
#include<sys/times.h>
#include<unistd.h>
#include <time.h>
#include <ctime>
#include <vector>
#include <string>
#include<math.h>
#include<assert.h>

int lscc(int nb_vtx, int nb_edge, double cutoff, int** AdjacentList, int* Node_Degree, int* Node_Weight);

#endif