// =====================================================================================
//
//       Filename:  LSCC+BMS.cpp
//
//    Description:  This is a solver for weighted maximum clique problem based on SCC and BMS
//
//        Version:  1.0
//        Created:  2016.01
//       Revision:  none
//       Compiler:  g++
//
//         Author:  Yiyuan Wang          yiyuanwangjlu@126.com
//                  Shaowei Cai          caisw@ios.ac.cn
//                  Minghao Yin          ymh@nenu.edu.cn

//         For example：./LSCC+BMS web-google 1000 1 
// =====================================================================================


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
#include<random>
#define	MAXV	1000000
#define MAXE	200000000

#include "lscc.h"


using namespace std;

int BMS=100;

tms start, finish;
double time_limit;
double real;
int lbest;
int M_iter = 0;
struct Edge1{
	int v1;
	int v2;
};

Edge1 edge[MAXE];
int v_degree_tmp[MAXV];

int adjaclen[MAXV];

double real_solve1=-1;
double real_solve2=-1;
int **neighbor;
int neighbor_len[MAXV];
int conf_change[MAXV];

int time_stamp[MAXV];




int temp_array[MAXV];

char * File_Name;
const char *resPath = "results/";
const char *dataPath;

int vectex[MAXV];
int funch[MAXV];
int address[MAXV];
int tabuin[MAXV];
int Max_Vtx,  Max_Iter;
int f;
int fbest;

int cruset[MAXV];
int len;
int tm1;
int tm2;
int C0[MAXV]; // the candidates node for ADD operation?
int C1[MAXV]; // the Candidate nodes for SWAP operation?
int We[MAXV]; // Weights of nodes?
int BC[MAXV]; //
int len0; // the length of C0
int len1; // the length of C1
int TC1[MAXV]; // Temporal candidate nodes?
int Iter; // the number of iterations taken
int TABUL = 7;
int Wf;
int Wbest;
int FC1[MAXV];
int Tbest[MAXV];
int TTbest[MAXV];
int Waim;
int Titer;

int len_best = 0;
int len_W;
int Iteration[ 100 ];
double time_used[ 100 ];
int len_used[ 100 ];
int W_used[ 100 ];
char outfilename[100];
char filename[100];
int len_improve;
int len_time;
int Wmode;





//int TABUL0 = 5;

/************************************************************************/
/*   WYY: Variables for Configuration Checking                    */
/************************************************************************/
/* neighbor[i][j] = n means that i and n are connceted, and n is the jth 
 *  neighbor of n.
 */

/* time_stamp[m]=j means the conf_change value of node m recently 
 * changes at jth iteration.
 */

//struct  timeval start;
//struct  timeval end;

void dump_neighborhood();
#define DEBUG 0
///////////////////////////
int edge_is(int m, int n)
{
  int i;
  int index;
  for(i=0;i<neighbor_len[m];i++){
    index=neighbor[m][i];
    if(index==n)return 0;
  }
  return 1;
}

// section 0, initiaze
void Initializing()
{
     ifstream FIC;
//     FIC.open(File_Name);

     FIC.open(filename);

     if ( FIC.fail() )
     {
           cout << "### Erreur open, File_Name " << File_Name << endl;
           getchar();
           exit(0);
     }
     //Max_Vclique=300;
    // FIC >> StrReading;
     if ( FIC.eof() )
     {
           cout << "### Error open, File_Name " << File_Name << endl;
           exit(0);
     }
     int nb_edg=-1, max_edg=0;
     int x1, x2;
	 
	 
	 string p, tmp;
	 FIC >>p>>tmp>>Max_Vtx >> nb_edg;

	 //FIC >> tt >> Max_Vtx >> nb_edg;
	 neighbor=(int **)malloc(nb_edg*2*sizeof(int));//neighbor set
	 for( int x = 0 ; x < Max_Vtx ; x++ ) 
	 {
		 conf_change[x] = 1; // initialize
         time_stamp[x] = 0;
		 adjaclen[x]=0;
         neighbor_len[x]=0;
         vectex[x]  = x;
         address[x] = x;
	}
	int ii;

     for( int x = 0; x < Max_Vtx; x++ )
     {
        FIC >>tmp>> x1 >> x2;
        x1--;
        We[ x1 ] =x2;       
     }

	for(ii=0;ii<nb_edg;ii++)
	{
		FIC >>tmp>> x1 >> x2;
		if ( x1<1 || x2<1 || x1>Max_Vtx || x2 >Max_Vtx){
            cout << "### Error of node : x1="
                 << x1 << ", x2=" << x2 << endl;
            exit(0);
        }
		if (x1 != x2) {
		    x1--; x2--;
            max_edg++;
            neighbor_len[x1]++;
            neighbor_len[x2]++;
            edge[ii].v1 = x2;
            edge[ii].v2 = x1;
		}
    }
    int v;
    for (v=0; v<Max_Vtx; v++) adjaclen[v]=Max_Vtx-1-neighbor_len[v];

	for (v=0; v<Max_Vtx; v++) neighbor[v]=(int *)malloc( neighbor_len[v]*sizeof(int));

    for(v=0; v<Max_Vtx; v++) v_degree_tmp[v]=0; 
	int e,v1,v2;  
	for (e=0; e<nb_edg; e++)
	{
		v1=edge[e].v1;
		v2=edge[e].v2;
		neighbor[v1][v_degree_tmp[v1]] = v2;
		neighbor[v2][v_degree_tmp[v2]] = v1;
		v_degree_tmp[v1]++;
		v_degree_tmp[v2]++;
	}

     if ( 0 && max_edg != nb_edg )
     {
           cout << "### Error de lecture du graphe, nbre aretes : annonce="
                 << nb_edg << ", lu=" << max_edg  << endl;
           exit(0);
     }
     
     

     for( int x = 0; x < Max_Vtx; x++ )
     {
//        We[ x ] = (x+1)%Wmode + 1;
        BC[ x ] = 0;
        //We[ x ] = 1;
        //We[ x ] = ( rand() % 10 ) + 1;
     }
    
     FIC.close();

}



// WYY
void dump_conf_change() {
	printf("\nconf_change:\n");
	for(int i = 0; i < Max_Vtx; i++) {
		printf("%4d(%d) ", i, conf_change[i]);
	}
	printf("\n");
}

// WYY
inline void neighbor_add(int node) {
	int node2;
	int num_neighbor = neighbor_len[node];
	
	conf_change[node] = 0; // keep this node from being removed immediately
	time_stamp[node] = Iter;
	for(int i = 0; i < num_neighbor; i++) {
		node2 = neighbor[node][i];
		if(conf_change[node2] == 0){
			conf_change[node2] = 1;
			time_stamp[node2] = Iter;
		}
	}
}
// WYY
inline void neighbor_drop(int node) {
	conf_change[node] = 0;
	time_stamp[node] = Iter;
}

// WYY
inline bool is_forbiden_cc(int node) {
	return (conf_change[node] == 0 ? true : false);
}


// WYY
void dump_neighborhood() {
	printf("Neighborhood:\n");
	for(int i = 0; i < Max_Vtx; i++) {
		printf(": ");
		for(int j = 0; j < neighbor_len[i]; j++)
			printf("%d ", neighbor[i][j]);
		printf("\n");	
	}
	return;
}

// WYY
void dump_cur_clique() {
	int n;
	printf("\ncurrent clique includes %d nodes:", len);
	for(int i = 0; i < len; i++) {
		n = cruset[i];
		printf("%d(%d) ", n, Tbest[n]);
	}
	printf("\n");
	return;
}

void Output(int r)
{
    int i;
    FILE *fp ;

    if (r == 0){
        fp = fopen(outfilename, "w");
        fprintf(fp, "f ");
        fprintf(fp, "x");
        fprintf(fp, "%d \n", Max_Vtx);
    }else{
        fp = fopen(outfilename, "a+");
    }
    fprintf(fp, "%d ", lbest);
    for( i = 0; i < Max_Vtx; i++)
    {
        fprintf(fp, "%d ",TTbest[i]);
    }
    fprintf(fp, "\n");
    fclose(fp); // WYY

    return;

//    fprintf(fp, "\n\n the total information: \n");
//    int wavg, iteravg, lenbb, success;
//    wavg = iteravg = lenbb = success = 0;
//    int best_v = 0;
//    double timeavg = 0;
//    for( i = 0; i < 100; i++ )
//		if( W_used[ i ] > best_v )
//		{
//			best_v = W_used[ i ];
//			lenbb = len_used[ i ];
//		}
//
//        int count = 0;
//        fprintf(fp, "\n The best weight value for the maximum weighted problem is %6d \n", best_v);
//        for( i = 0; i < 100; i++ )
//        {
//         wavg = wavg + W_used[ i ];
//        }
//        double twavg = (double (wavg)) / 100 ;
//        for( i = 0; i < 100; i++ )
//            if( W_used[ i ] == best_v )
//            {
//                count++;
//                iteravg = iteravg + Iteration[ i ];
//                timeavg = timeavg + time_used[ i ];
//            }
//
//        iteravg =  int ( (double (iteravg)) / count );
//         timeavg = timeavg / (count*1000);
//        fprintf(fp, "avg_sum = %10lf, succes = %6d, len = %5d, avg_iter = %6d,  time = %8lf \n",
//    			twavg, count, lenbb,  iteravg, timeavg );
//    fclose(fp) ;
//    return ;
}

int randomInt( int n )
{
    return rand() % n;
}

void clearGamma()
{
    int i;
    memset( vectex, 0, tm1 );
    memset(  funch, 0, tm1 );
    memset(address, 0, tm1 );
    memset( tabuin, 0, tm1 );
    for( i = 0; i < Max_Vtx; i++ )
    {
       C0[ i ] = i;
       address[ i ] = i;
    }
    len0 = Max_Vtx;
    len1 = 0;
    len = 0;
    Wf = 0;
    Wbest = 0;
}

// WYY: C0 is the set of nodes that can be added? and C1 is the set nodes that can be swapped with?
int selectC0( ) 
{
    int i, k, l;
    l = 0;
    
    if( len0 > 30 )
    {
       k = randomInt( len0 );
       return k;
    }
    
    // WYY: TC1 records the set of nodes which are not being forbidden
    for( i = 0; i < len0; i++ )
    {
       k = C0[ i ];
       if( !is_forbiden_cc(k) ) // Added by: WYY
       {
         TC1[ l++ ] = i;
       }
    }
    
    if( l == 0 )
      return -1;
    else
    {
        k = randomInt( l );
        k = TC1[ k ];
        return k;
    }
}
// WYY: Select from C0, a node, which is not in tabu and has the max weight, 
// or satisfy the aspiration rule though in tabu.
int WselectC0( )
{
    int i, k, l1, l2, w1, w2;
    l1 = 0;
    l2 = 0;
    w1 = 0;
    w2 = 0;
    
    for( i = 0; i < len0; i++ )
    {
       k = C0[ i ];
       
       // WYY:store nodes that are not in tabu list and with the maximum weight, in FC1
       if( !is_forbiden_cc(k) ) // Added by WYY
       {
           if( We[ k ] > w1 )
           {
              l1 = 0;
              w1 = We[ k ];
              FC1[ l1++ ] = i;
           }
           else if ( We[ k ] >= w1 )
           {
              FC1[ l1++ ] = i;
           }
       }
       else
       {  // WYY: stores nodes that are being in tabu but with the maximum weight, in TC1
           if( We[ k ] > w2 )
           {
              l2 = 0;
              w2 = We[ k ];
              TC1[ l2++ ] = i;
           }
           else if ( We[ k ] >= w2 )
           {
              TC1[ l2++ ] = i;
           }
       }
    }
    
    // WYY: to check first if the aspiration rule is applicable.
    // If not, select a nodes which have the highest weithgts; break ties randomly.
    if( (l2 > 0) && ( w2 > w1 ) && ((w2+Wf)>Wbest) ) 
    {
        /*
        k = randomInt( l2 );
        k = TC1[ k ];
        */
        
        // WYY: Select the node with the oldest age
        k = TC1[0];
        int oldest_time = time_stamp[ C0[k] ];
        int index;
        int node;
       	int time;
		for(int j = 1; j < l2; j++) {
			index = TC1[j];
			node = C0[index];
			time = time_stamp[ node ];
			if(time < oldest_time) {
				oldest_time = time;
				k = index;
			}
		}
		      
        //cout << "yes in aspiration w2+Wf = " << w2+Wf << endl;
        //getchar();
        return k;
    }  
    else if( l1 > 0 )
    {
    	/*
        k = randomInt( l1 );
        k = FC1[ k ];
        */
        
        // WYY
        k = FC1[0];
        int oldest_time = time_stamp[ C0[k] ];
        int index;
        int node;
       	int time;
		for(int j = 1; j < l1; j++) {
			index = FC1[j];
			node = C0[index];
			time = time_stamp[ node ];
			if(time < oldest_time) {
				oldest_time = time;
				k = index;
				//cout << "elder one found" << endl;
				//getchar();
			}
		}
        return k;
    }
    else
    {
        return -1;
    }
}

// SelN: the index of the node selected from C0
int expand(int SelN)
{
    int i, k1, m, n, n1;
    
    m = C0[ SelN ]; // the node is m
    cruset[ len++ ] = m; // add m into the current set
    vectex[ m ] = 1; // set the flag?
    Wf = Wf + We[ m ]; // Wf is the weight of the current clique, i,e, weight found. update it.

	 /* WYY: set the nodes in cruset as neighbors of m, and vice versa */
	if(DEBUG) {
		printf("\nin expand");
		printf("\nadd node %d", m);
	}
	//neighbor_add(m);
	    
    len0--;
    n1 = C0[ len0 ];
    k1 = address[ m ];
    C0[ k1 ] = n1;
    address[ n1 ] = k1;
    
    
    
    int node2;	
    for(i=0;i<Max_Vtx;i++)
      temp_array[i]=0;
    
    conf_change[m] = 0; // keep this node from being removed immediately
	time_stamp[m] = Iter;
    for(i=0;i<neighbor_len[m];i++){
        node2 = neighbor[m][i];
        if(conf_change[node2] == 0){
		    conf_change[node2] = 1;
		    time_stamp[node2] = Iter;
	    }
         n=neighbor[m][i];
         temp_array[n]=1;
    }

    for(i=0;i<Max_Vtx;i++){
       if(i==m)continue;
       if(temp_array[i]==1)continue;
       n=i;
       funch[ n ]++; // WYY: funch[n] traces the number of nodes that are in the current clique
       
       if( funch[ n ] == 1 ){   // WYY: remove n from C0
           k1 = address[ n ];
           len0--;
           n1 = C0[ len0 ];
           C0[ k1 ] = n1;
           address[ n1 ] = k1;
           
           // put it into C1
           C1[ len1 ] = n;
           address[ n ] = len1;
           len1++;
           
           BC[ n ] = m; // WYY: BC[n] = m denotes that n is Being Connected by m.
       }
       else if( funch[ n ] == 2 ){
           // remove n it from C1
           len1--;
           n1 = C1[ len1 ];
           k1 = address[ n ];
           C1[ k1 ] = n1;
           address[ n1 ] = k1;
       }
    }
    
    if( Wf > Wbest ){
        times(&finish);
        real_solve2 = double(finish.tms_utime - start.tms_utime + finish.tms_stime - start.tms_stime)/sysconf(_SC_CLK_TCK);
        real_solve2 = round(real_solve2 * 100)/100.0; 
        Wbest = Wf;
        len_best = len;
        for( i = 0; i < Max_Vtx; i++ )
        {
            Tbest[ i ] = vectex[ i ];
        }
     }
    
    return 1;   
}

int selectC1( )
{
    int i, k, l;
    l = 0;
    for( i = 0; i < len1; i++ )
    {
       k = C1[ i ];
       if( !is_forbiden_cc(k) ) // WYY
       {
         TC1[ l++ ] = i;
       }
    }
    if( l == 0 )
      return -1;
    else
    {
        k = randomInt( l );
        k = TC1[ k ];
        return k;
    }
}

int kkk;
int WselectC1( )
{
     int i, j, k, l, l1, l2, wmn, w1, w2, m, n;
     l1 = 0;
     l2 = 0;
     w1 = -1000000;
     w2 = -1000000;
     l = 0;
     for( i = 0; i < len1; i++ )
     {
         m = C1[ i ];
         n = BC[ m ];
         if( (vectex[ n ] == 1) && (edge_is( m, n)==1) )
           l++;
         else
         {
             for( j = 0; j < len; j++ )
             {
                k = cruset[ j ];
                if( edge_is(m, k)== 1 )
                  break;
             }
             BC[ m ] = k;
         }
     }
  //wyy-20150601
     int count;
     kkk=BMS;
	 if(len1<=BMS) kkk=len1;
	 
	 if(len1==0)return -1;
     //---add end
     for( count = 0; count < kkk; count++ )
     {
		 if(len1>BMS) i=rand()%len1;
		 else i=count;
		 
         m = C1[ i ];
         n = BC[ m ];
         wmn = We[ m ] - We[ n ];
		 if( !is_forbiden_cc(m) ) // WYY
         { // find the nodes that lead highest weight-increase for the current clique.
             if( wmn > w1 )
             {
                l1 = 0;
                w1 = wmn;
                FC1[ l1++ ] = i;
             }
             else if ( wmn >= w1 )
             {
                FC1[ l1++ ] = i;
             }
         }
         else
         {
             if( wmn > w2 )
             {
                l2 = 0;
                w2 = wmn;
                TC1[ l2++ ] = i;
             }
             else if ( wmn >= w2 )
             {
                TC1[ l2++ ] = i;
             }
         }
     }
     
     if( (l2 > 0) && ( w2 > w1 ) && ((w2+Wf)>Wbest) )
     {
        /* 
        k = randomInt( l2 );
        k = TC1[ k ];
        */
        
        // WYY: Select the oldest node
        k = TC1[0];
        int oldest_time = time_stamp[ C1[k] ];
        int index;
        int node;
       	int time;
		for(int j = 1; j < l2; j++) {
			index = TC1[j];
			node = C1[index];
			time = time_stamp[ node ];
			if(time < oldest_time) {
				oldest_time = time;
				k = index;
			}
		}
        return k;
     }  
     else if( l1 > 0 )
     {
     /*
        k = randomInt( l1 );
        k = FC1[ k ];
       */  
        
        // WYY: Select the oldest node
        k = FC1[0];
        int oldest_time = time_stamp[ C1[k] ];
        int index;
        int node;
       	int time;
		for(int j = 1; j < l1; j++) {
			index = FC1[j];
			node = C1[index];
			time = time_stamp[ node ];
			if(time < oldest_time) {
				oldest_time = time;
				k = index;
				//cout << "elder nodes found " << endl;
				//getchar();
			}
		}
       	
       	return k;
     }
     else
     {
         return -1;
     }
}

int plateau( int SelN )
{
     int i, k1, m, m1, n, n1, ti;
     
     m = C1[ SelN  ];
     // WYY: swap(m1, m), where m is to be added, and m1 to be removed. m and m1 have no edge.
     for(ti = 0; ti < len; ti++)
     {
         m1 = cruset[ ti ];
         if( edge_is(m1, m)== 1 )
            break;
     }
     
     Wf = Wf + We[ m ] - We[ m1 ];
     
     //the expand process, put m into the current independent set
     vectex[ m ] = 1;
     cruset[ len++ ] = m;

	 /* WYY: set the nodes in cruset as neighbors of m, and vice versa */
	 if(DEBUG) {
	 	printf("\nin plateau: add node %d", m);
	 	dump_cur_clique();
	 }
	 //neighbor_add(m); // Attention: here, we don't change conf_change values for m's neighbors
	 
     //delete m from C1
     k1 = address[ m ];
     len1--;
     n1 = C1[ len1 ];
     C1[ k1 ] = n1;
     address[ n1 ] = k1;
     
     
    for(i=0;i<Max_Vtx;i++)
      temp_array[i]=0;
    for(i=0;i<neighbor_len[m];i++){
     
      n=neighbor[m][i];
      temp_array[n]=1;
    }

    for(i=0;i<Max_Vtx;i++)
    {
       if(i==m)continue;
       if(temp_array[i]==1)continue;
       n=i;
        funch[ n ]++;
        if( (funch[ n ] == 1) && ( vectex[ n ] == 0 ) )
        {
             //cout << "tt k1 = " << k1 << "len0 = " << len0 << "n = " << n << "m = " << m << " m1 = " << m1 << endl;
             k1 = address[ n ];
             len0--;
             n1 = C0[ len0 ];
             C0[ k1 ] = n1;
             address[ n1 ] = k1;
             
             C1[ len1 ] = n;
             address[ n ] = len1;
             len1++;
             BC[ n ] = m;
           
             //getchar();
        }
        if( funch[ n ] == 2 )
        {
            len1--;
            n1 = C1[ len1 ];
            k1 = address[ n ];
            C1[ k1 ] = n1;
            address[ n1 ] = k1;
        }        
     } 
     
     //the backtrack process, delete m1 from the current independent set
     vectex[ m1 ] = 0;

	 len--;
     cruset[ ti ] = cruset[ len ];
     C1[ len1 ] = m1;
     address[ m1 ] = len1;
     len1++;
     
     /* WYY: neighborhood updating */
	 if(DEBUG) {
	 	printf("\nin plateau: remove node %d", m1);
	 	dump_neighborhood();
	 }
	 neighbor_drop(m1);
	 
    for(i=0;i<Max_Vtx;i++)
      temp_array[i]=0;
    for(i=0;i<neighbor_len[m1];i++){
     
      n=neighbor[m1][i];
      temp_array[n]=1;
    }

    for(i=0;i<Max_Vtx;i++)
    {
       if(i==m1)continue;
       if(temp_array[i]==1)continue;
       n=i;
	 
        funch[ n ]--;
        if( (funch[ n ] == 0) && (vectex[ n ] == 0) )
        {
           k1 = address[ n ];           
           len1--;
           n1 = C1[ len1 ];
           C1[ k1 ] = n1;
           address[ n1 ] = k1;
           
           C0[ len0 ] = n;
           address[ n ] = len0;
           len0++;
        }
        else if( funch[ n ] == 1 )
        {
           C1[ len1 ] = n;
           address[ n ] = len1;
           len1++;
        }
     }
     
     if( Wf > Wbest )
     {
        times(&finish);
        real_solve2 = double(finish.tms_utime - start.tms_utime + finish.tms_stime - start.tms_stime)/sysconf(_SC_CLK_TCK);
        real_solve2 = round(real_solve2 * 100)/100.0; 
        Wbest = Wf;
        len_best = len;
        for( i = 0; i < Max_Vtx; i++ )
        {
            Tbest[ i ] = vectex[ i ];
        }
     }
     
     
     return 1;   
}

// WYY: find nodes with minimum weight in the current clique to remove
int Mumi_Weigt()
{
    int i, k, l1;
    int w1 = 5000000;
    l1 = 0;
    // WYY: find in cruset the nodes with lowest weights, chose one of it randomly
    for( i = 0; i < len; i++ )
    {
       k = cruset[ i ];
       if( We[ k ] < w1 )
       {
          l1 = 0;
          w1 = We[ k ];
          FC1[ l1++ ] = i;
       }
       else if ( We[ k ] <= w1 )
       {
          FC1[ l1++ ] = i;
       }
    }
    
    if( l1 == 0 )
      return -1;
    /*
    k = randomInt( l1 );
    k = FC1[ k ];
    */
    
    // WYY: remove an oldest node
    k = FC1[0];
    int oldest_time = time_stamp[ cruset[k] ];
    int cur_index;
    int cur_node;
    int cur_time;
    for(int i = 1; i < l1; i++) {
    	cur_index = FC1[i];
    	cur_node = cruset[cur_index ];
    	cur_time = time_stamp[cur_node];
    	if(cur_time < oldest_time) {
    		oldest_time = cur_time;
    		k = cur_index;
    		//cout << "elder node found " << endl;
    		//getchar();
    	}
    }
    return k;
}

int backtract(){
    int i, m1, n, ti, k1, n1;
    ti = Mumi_Weigt();
    if( ti == -1 ){
    return -1;
    }

    if(DEBUG) printf("in backtrack");

    m1 = cruset[ ti ];
    Wf = Wf - We[ m1 ];
    vectex[ m1 ] = 0;

    len--;
    cruset[ ti ] = cruset[ len ];

    /* WYY: functions of neighborhood updating */
    neighbor_drop(m1);
    if(DEBUG) {
    printf("\nremove node %d", m1);
    dump_cur_clique();
    }
    //dump_conf_change();
    //getchar();

    C0[ len0 ] = m1;
    address[ m1 ] = len0;
    len0++;
     
    for(i=0;i<Max_Vtx;i++){
        temp_array[i]=0;
    }
    for(i=0;i<neighbor_len[m1];i++){
        n=neighbor[m1][i];
        temp_array[n]=1;
    }

    for(i=0; i<Max_Vtx; i++){
        if(i==m1) continue;
        if(temp_array[i]==1)continue;
        n = i;
        funch[ n ]--;
        if( (funch[ n ] == 0) && (vectex[ n ] == 0) ){
            k1 = address[ n ];
            len1--;
            n1 = C1[ len1 ];
            C1[ k1 ] = n1;
            address[ n1 ] = k1;

            C0[ len0 ] = n;
            address[ n ] = len0;
            len0++;
        } else if( funch[ n ] == 1 ) {
            C1[ len1 ] = n;
            address[ n ] = len1;
            len1++;
        }
    }
    return 1;
}

int tabu( int Max_Iter ){
     int i, k, am, am1, ww, ww1, ww2, ti, m1;
     Iter = 0;
     clearGamma(); 
     while( Iter < Max_Iter ){
        am = selectC0();
        if( am != -1 )
        {
            expand( am );
            Iter++;
            if( Wbest == Waim )
               return Wbest;
        }
        else 
            break;
     }
     times(&finish);
     double finish_time = double(finish.tms_utime - start.tms_utime + finish.tms_stime - start.tms_stime)/sysconf(_SC_CLK_TCK);
     finish_time = round(finish_time * 100)/100.0;
     if(Wbest>lbest){
        lbest=Wbest;
        real_solve1=real_solve2;
        printf("c	%.2f	%d\n", real_solve1,lbest);
        for( i = 0; i < Max_Vtx; i++ ){
            TTbest[ i ] = Tbest[i];
        }
     }
     if(finish_time>time_limit){
       M_iter+=Iter;
//       if(Wbest>lbest){
//       lbest=Wbest;
//       real_solve1=real_solve2;
//       }
//       printf("o	%.2f	%d\n", real_solve1,lbest);
       return Wbest;

//       dump_cur_clique();
//       Output();
//       exit(0);
     }
     
      
     while( Iter < Max_Iter )
     {
        am = WselectC0();
        am1 = WselectC1();
        if( (am != -1) && (am1 != -1) )
        {
            ww = We[ C0[ am ] ];
            ww1 = We[ C1[ am1 ] ] - We[ BC[ C1[ am1 ] ] ];
        
            if( ww > ww1 )
            {
                expand( am );
                
                Iter++;
                if( Wbest == Waim )
                   return Wbest;
            }
            else
            {
                plateau( am1 );
                if( Wbest == Waim )
                    return Wbest; 
                Iter++;
            }
        }
        else if( (am != -1) && (am1 == -1) )
        {
             expand( am );
             if( Wbest == Waim )
               return Wbest;
                
             Iter++;
        }
        else if( (am == -1) && (am1 != -1) )
        {
             ti = Mumi_Weigt();
             m1 = cruset[ ti ];
             ww1 = We[ C1[ am1 ] ] - We[ BC[ C1[ am1 ] ] ];
             ww2 = - We[ m1 ];
             if( ww1 > ww2 )
             {
                plateau( am1 );
                if( Wbest == Waim )
                    return Wbest; 
                Iter++;
             }
             else
             {
                 k = backtract();
                 if( k == -1 )
                     return Wbest;
                 Iter++;
             }
        }
        else if( (am == -1) && (am1 == -1) )
        {
             k = backtract();
             if( k == -1 )
                return Wbest;
             Iter++;
        }
        times(&finish);
        double finish_time = double(finish.tms_utime - start.tms_utime + finish.tms_stime - start.tms_stime)/sysconf(_SC_CLK_TCK);
        finish_time = round(finish_time * 100)/100.0;
        if(Wbest>lbest){
            lbest=Wbest;
            real_solve1=real_solve2;
            for( i = 0; i < Max_Vtx; i++ ){
                TTbest[ i ] = Tbest[i];
            }
            printf("c	%.2f	%d\n", real_solve1,lbest);
            }
        if(finish_time>time_limit){
          M_iter+=Iter;
//          if(Wbest>lbest){lbest=Wbest;real_solve1=real_solve2;}
//          printf("o	%.2f	%d\n", real_solve1,lbest);
          return Wbest;
//          dump_cur_clique();
//          Output();
//          exit(0);
       }
     }

     return Wbest;
}

void verify()
{
     int i, j;
     for( i = 0; i < Max_Vtx; i++ )
     {
          if( TTbest[ i ] == 1 )
          {
              for( j = i+1; j < Max_Vtx; j++ )
              if( (TTbest[ j ] == 1) && ( edge_is(i, j)== 1 ) )
                  cout << "hello there is something wrong" << endl;
          }
     }
     cout << "verified" << endl;
}

// WYY: Validate that the cruset is indeed a clique
void validate() {
	int i, j;
     for( i = 0; i < Max_Vtx; i++ )
     {
          if( vectex[ i ] == 1 )
          {
              for( j = i + 1; j < Max_Vtx; j++ )
              if( (vectex[ j ] == 1) && ( edge_is(i, j)== 1 ) ) {
                  cout << "hello there is something wrong" << endl;
              	getchar();
              }
          }
     }
}

int Max_Tabu()
{
     int i, l;
     lbest = 0;
     Titer = 0;
	 times(&start);
	 while(1)
     {
         l = tabu(len_improve);
         M_iter = M_iter + Iter; 
         if( l > lbest )
         {
			 real_solve1=real_solve2;
			 lbest = l; 
			 Titer = M_iter; 
			 len_W = len_best;

			 for( i = 0; i < Max_Vtx; i++ ){
                  TTbest[ i ] = Tbest[i];
             }

         }
         
         if( l >= Waim )
           return lbest;
         //cout << " l = " << l << " i = " << i << endl;
		 
		 // wyy: clear configuration Information for the next restart
		 for(int j = 0; j < Max_Vtx; j++) {
          	conf_change[j] = 1;
          	time_stamp[j] = 0;
         }
         times(&finish);
	    double finish_time = double(finish.tms_utime - start.tms_utime + finish.tms_stime - start.tms_stime)/sysconf(_SC_CLK_TCK);
	    finish_time = round(finish_time * 100)/100.0;
	    if(finish_time>time_limit){
	        printf("o	%.2f	%d\n", real_solve1,lbest);
	        return lbest;
//	        dump_cur_clique();
//	        Output();
//	        exit(0);

	    }
     
     }
     return lbest;
}

int lscc(int nb_vtx, int nb_edge, double cutoff, int** AdjacentList, int* Node_Degree, int* Node_Weight){

    Max_Vtx = nb_vtx;
    neighbor=(int **)malloc(nb_edge*2*sizeof(int));//neighbor set
	for( int x = 0 ; x < Max_Vtx ; x++ ){
	     BC[ x ] = 0;
		 conf_change[x] = 1; // initialize
         time_stamp[x] = 0;
		 adjaclen[x]=0;
         neighbor_len[x]=0;
         vectex[x]  = x;
         address[x] = x;
	}

	//node weight
	for(int x = 0; x < Max_Vtx; x++){
        We[x] = Node_Weight[x];
        neighbor_len[x] = Node_Degree[x];
    }

    for (int v = 0; v < Max_Vtx; v++){
        adjaclen[v] = Max_Vtx - 1 - neighbor_len[v];
        neighbor[v] = (int *)malloc(neighbor_len[v]*sizeof(int));
    }

	for (int i = 0; i < Max_Vtx; i++){
	    for (int j = 0; j < neighbor_len[i]; j++){
	        neighbor[i][j] = AdjacentList[i][j];
	    }
	}

     std::uniform_int_distribution<> rand_int(1,10000);
     std::mt19937 gen;

	 time_limit = cutoff;

	 len_improve=4000;
	 Waim=INT_MAX;
	 Wmode=200;

//     Initializing();
	 tm1 = Max_Vtx*sizeof( int );
     //  cout << "finish reading data" << endl;
     len_time = (int (100000000 / len_improve) ) + 1;
     //   cout << "len_time = " << len_time << endl;

//    seed = rand_int(gen);
//    srand(seed);

    Max_Tabu();
//  dump_cur_clique();
//	Output(i);

     return lbest;
}
