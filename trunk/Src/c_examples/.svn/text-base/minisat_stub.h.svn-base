/*
 * minisat.h
 *
 *  Created on: 2011/8/29
 *      Author: Yu-Fang Chen
 */

#ifndef MINISAT_H_
#define MINISAT_H_

typedef struct {
  int is_sat;// 0: UNSAT, 1:SAT
  int *counterexample;//the numbers of postive
  int cesize;
} sat_result_t;



#ifdef __cplusplus
extern "C"
#endif
void sat_result_free(sat_result_t*);
#ifdef __cplusplus
extern "C"
#endif
sat_result_t* solve(int** clauses, int num_of_clauses);
#endif /* MINISAT_H_ */
