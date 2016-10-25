/*
 * minisat.cc
 *
 *  Created on: 2011/8/29
 *      Author: Yu-Fang Chen
 */


#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Solver.h"
#include "minisat_stub.h"

using namespace Minisat;
extern "C" void sat_result_free(sat_result_t* r){
	if(r->is_sat==1)
		free(r->counterexample);
	free(r);
}

extern "C" sat_result_t* solve(int** clauses, int num_of_clauses){
	Solver S;
    S.verbosity = 0;

    for (int i=0;i<num_of_clauses;i++){
        vec<Lit> lits;
    	int* clause=*(clauses+i);
//		fprintf(stderr,"\nclauses: ");
    	for(int j=0;;j++){
    		int lit=*(clause+j);
    		if(lit==0)
    			break;
    		int var = abs(lit)-1;
    		while (var >= S.nVars()) S.newVar();
//    		fprintf(stderr,"%d ", lit);
    		lits.push( (lit > 0) ? mkLit(var) : ~mkLit(var) );
    	}
//		fprintf(stderr,"\n");
        S.addClause_(lits);
    }
    sat_result_t* res=(sat_result_t*)malloc(sizeof(sat_result_t));
    if (!S.simplify()){
    	res->is_sat=0;
         return res;
     }

     if(S.solve()){
    	 res->is_sat=1;
    	 res->cesize=S.nVars();
    	 res->counterexample=(int*)malloc(sizeof(int)*res->cesize);
    	 for(int i=0;i<S.nVars();i++){
    		 lbool l=S.model[i];
			 res->counterexample[i]=(l==l_False)?0:1;
    	 }
     }else
    	 res->is_sat=0;


	return res;
}

