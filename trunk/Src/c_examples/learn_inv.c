/*
 *  Created on: 2011/8/26
 *  Author: Yu-Fang Chen
  * Copyright reserved
 */
//#define DEBUG

#include <stdlib.h>
#include <stdio.h>

#include <errno.h>
#include <assert.h>

#include <type.h>
#include <bitvector.h>
#include <vector.h>

#include <stdlib.h>
#include <signal.h>
#include <zlib.h>
#include <minisat_stub.h>
#include <boolformula.h>
#include <cdnfformula.h>
#include <query.h>
#include <cdnf.h>
#include "learn_inv.h"

boolformula_t* myformula;
int memQ=0, equQ=0;

membership_result_t mymembershipquery (void *info, bitvector *v){
	membership_result_t res;
	memQ++;
	int i;
#ifdef DEBUG
	fprintf(stderr,"\n Mem. Query#%d:", memQ);
	for(i=1;i<v->length;i++){
		if(bitvector_get(v, i))
			fprintf(stderr,"%d ", i);
		else
			fprintf(stderr,"%d ", -i);
	}
	fprintf(stderr,"\n");
#endif
//if (x!=y/\v) is satisfiable, return true
	boolformula_t* mem=boolformula_conjunction_new(3);//mem=true
	boolformula_t* temp=boolformula_disjunction_new(2);//temp=false
        boolformula_t* temp2=boolformula_literal_new(-1); //temp2=~x
	boolformula_set(temp,0,temp2);//temp=~x
	boolformula_free(temp2);
	temp2=boolformula_literal_new(-2);//temp2=~y
	boolformula_set(temp,1,temp2);//temp=~x\/~y
	boolformula_free(temp2);
	boolformula_set(mem,0,temp);//mem=(~x\/~y)
	boolformula_free(temp);
        	
	temp=boolformula_disjunction_new(2);//temp=false
        temp2=boolformula_literal_new(1); //temp2=x
	boolformula_set(temp,0,temp2);//temp=x
	boolformula_free(temp2);
	temp2=boolformula_literal_new(2);//temp2=y
	boolformula_set(temp,1,temp2);//temp=x\/y
	boolformula_free(temp2);
	boolformula_set(mem,1,temp);//mem=(x\/y)/\(~x\/~y)
	boolformula_free(temp);


	temp=boolformula_conjunction_new(v->length-1);//temp=true
	for(i=1;i<v->length;i++){
		if(bitvector_get(v, i)){
        		temp2=boolformula_literal_new(i);
			boolformula_set(temp,i-1,temp2);
			boolformula_free(temp2);
		}else{
        		temp2=boolformula_literal_new(-i);
			boolformula_set(temp,i-1,temp2);
			boolformula_free(temp2);
		}
	}//temp=v

	boolformula_set(mem,2,temp);//mem=(x\/y)/\(~x\/~y)/\v
	boolformula_free(temp);
    	sat_result_t* r=satisfible(mem);
    	boolformula_free(mem);
	if(r->is_sat==1){//is SAT
		res=true;
		return res;
	}
//if (x\/(~x/\y))/\v, which equals (x\/y)/\v, is unsatisfiable, return false
	mem=boolformula_conjunction_new(2);//mem=true
	temp=boolformula_disjunction_new(2);//temp=false
        temp2=boolformula_literal_new(1); //temp2=x
	boolformula_set(temp,0,temp2);//temp=x
	boolformula_free(temp2);
	temp2=boolformula_literal_new(2);//temp2=y
	boolformula_set(temp,1,temp2);//temp=x\/y
	boolformula_free(temp2);
	boolformula_set(mem,0,temp);//mem=(x\/y)
	boolformula_free(temp);
        	
	temp=boolformula_conjunction_new(v->length-1);//temp=true
	for(i=1;i<v->length;i++){
		if(bitvector_get(v, i)){
        		temp2=boolformula_literal_new(i);
			boolformula_set(temp,i-1,temp2);
			boolformula_free(temp2);
		}else{
        		temp2=boolformula_literal_new(-i);
			boolformula_set(temp,i-1,temp2);
			boolformula_free(temp2);
		}
	}//temp=v

	boolformula_set(mem,1,temp);//mem=(x\/y)/\v
	boolformula_free(temp);
    	r=satisfible(mem);
    	boolformula_free(mem);
	if(r->is_sat==0){//is UNSAT
		res=false;
		return res;
	}
//randomly answer	
    	if(rand()%2==1){
    		res=true;
    	}else{
    		res=false;
    	}
	return res;
    	
    	if(rand()%2==1){
    		res=true;
    	}else{
    		res=false;
    	}
	return res;
        /*	
    	sat_result_t* r=satisfible(mem);
    	boolformula_free(mem);
	membership_result_t res;
    	if(r->is_sat==1){
    		res=true;
    	}else{
    		res=false;
    	}
    sat_result_free(r);
	return res;
*/
}

bitvector* getce(sat_result_t* r, uscalar_t num_vars){
#ifdef DEBUG
	fprintf(stderr,"CE: ");
#endif

	bitvector *bv = bitvector_new(num_vars+1);
	int i;
	for(i=0;i<r->cesize;i++){
		int c=*(r->counterexample+i);
		if(c==1){
			if(i<num_vars){
				bitvector_set(bv, i+1, true);
#ifdef DEBUG
			fprintf(stderr,"%d ",i+1);
#endif
			}else{
#ifdef DEBUG
			fprintf(stderr,"(%d)",i+1);
#endif
			}
		}else{
			if(i<num_vars){
				bitvector_set(bv, i+1, false);
#ifdef DEBUG
			fprintf(stderr,"%d ",-i-1);
#endif
			}else{
#ifdef DEBUG
			fprintf(stderr,"(%d)",-i-1);
#endif
			}
		}
	}
#ifdef DEBUG
	fprintf(stderr,"\n");
#endif
	return bv;
}

inline boolformula_t *boolformula_swap_xy(boolformula_t * f){
	boolformula_t* ret=NULL, *temp;
	int i;
	switch(f->t){
	case conjunct:
		ret=boolformula_conjunction_new(f->d.v->length);
		for(i=0;i<f->d.v->length;i++){
			temp=boolformula_swap_xy(vector_get(f->d.v,i));
			boolformula_set(ret,i, temp);
			boolformula_free(temp);
		}
		break;
	case disjunct:
		ret=boolformula_disjunction_new(f->d.v->length);
		for(i=0;i<f->d.v->length;i++){
			temp=boolformula_swap_xy(vector_get(f->d.v,i));
			boolformula_set(ret,i, temp);
			boolformula_free(temp);
		}
		break;
	case literal:
		if(f->d.l > 0)
			ret=boolformula_literal_new(3-f->d.l);
		else
			ret=boolformula_literal_new(-3-f->d.l);
		break;
	}
	assert(f->t==ret->t);

	return ret;
}
equivalence_result_t* myequivalencequery (void *info, uscalar_t num_vars, boolformula_t * I){
	equQ++;

#ifdef DEBUG
	fprintf(stderr,"\n Equ. Query#%d:", equQ);
	boolformula_print(I);
	fprintf(stderr,"\n");
#endif
//check if~(x!=y->I), which equals((~x\/~y)/\(x\/y)/\~I), is satisfiable
	boolformula_t* equ=boolformula_conjunction_new(3);//equ=true
	boolformula_t* temp=boolformula_disjunction_new(2);//temp=false
        boolformula_t* temp2=boolformula_literal_new(-1); //temp2=~x
	boolformula_set(temp,0,temp2);//temp=~x
	boolformula_free(temp2);
	temp2=boolformula_literal_new(-2);//temp2=~y
	boolformula_set(temp,1,temp2);//temp=~x\/~y
	boolformula_free(temp2);
	boolformula_set(equ,0,temp);//equ=(~x\/~y)
	boolformula_free(temp);
        	
	temp=boolformula_disjunction_new(2);//temp=false
        temp2=boolformula_literal_new(1); //temp2=x
	boolformula_set(temp,0,temp2);//temp=x
	boolformula_free(temp2);
	temp2=boolformula_literal_new(2);//temp2=y
	boolformula_set(temp,1,temp2);//temp=x\/y
	boolformula_free(temp2);
	boolformula_set(equ,1,temp);//equ=(x\/y)/\(~x\/~y)
	boolformula_free(temp);


	temp=boolformula_neg(boolformula_copy(I));//temp=~I
	boolformula_set(equ,2,temp);//equ=(x\/y)/\(~x\/~y)/\~I
	boolformula_free(temp);
    	sat_result_t* r=satisfible(equ);
    	boolformula_free(equ);
	equivalence_result_t* res = malloc(sizeof(equivalence_result_t));
	if(r->is_sat==1){//is SAT
		res->is_equal=false;
#ifdef DEBUG
		fprintf(stderr,"\n +");
#endif
		res->counterexample=getce(r,num_vars);
		sat_result_free(r);
		return res;
	}
	sat_result_free(r);
//check if ~(~x /\ I -> ~x/\y), which equals (~x/\I/\(x \/ ~y)),is satisfiable
	equ=boolformula_conjunction_new(3);//equ=true
	temp=boolformula_literal_new(-1);//temp=~x
	boolformula_set(equ,0,temp);//equ=~x
	boolformula_free(temp);


	temp=boolformula_copy(I);//temp=I
	boolformula_set(equ,1,temp);//equ=~x/\I
	boolformula_free(temp);
    	
	temp=boolformula_disjunction_new(2);//temp=false
	temp2=boolformula_literal_new(1); //temp2=x
	boolformula_set(temp,0,temp2);//temp=x
	boolformula_free(temp2);
	temp2=boolformula_literal_new(-2);//temp2=~y
	boolformula_set(temp,1,temp2);//temp=x\/~y
	boolformula_free(temp2);
	boolformula_set(equ,2,temp);//equ=~x/\I/\(~x\/y)
	boolformula_free(temp);
        	
    	r=satisfible(equ);
    	boolformula_free(equ);
	if(r->is_sat==1){//is SAT
		res->is_equal=false;
#ifdef DEBUG
		fprintf(stderr,"\n +");
#endif
		res->counterexample=getce(r,num_vars);
		sat_result_free(r);
		return res;
	}
	sat_result_free(r);

//check if~(x/\I->I[y<-t][x<-y][t<-x]), which equals x/\I/\~I[x,y<-y,x], is satisfiable
	equ=boolformula_conjunction_new(3);//equ=true
	temp=boolformula_literal_new(1);//temp=x
	boolformula_set(equ,0,temp);//equ=x
	boolformula_free(temp);


	temp=boolformula_copy(I);//temp=I
	boolformula_set(equ,1,temp);//equ=x/\I
	boolformula_free(temp);

	temp=boolformula_neg(boolformula_swap_xy(I));//temp=~I[x,y<-y,x]
	boolformula_set(equ,2,temp);//equ=x/\I/\~I[x,y<-y,x]
    	r=satisfible(equ);
    	boolformula_free(equ);
	if(r->is_sat==1){//is SAT
		res->is_equal=false;
#ifdef DEBUG
		fprintf(stderr,"\n +");
#endif
		res->counterexample=getce(r,num_vars);
		sat_result_free(r);
		return res;
	}else{
		res->is_equal=true;
#ifdef DEBUG
		fprintf(stderr,"\n +");
#endif
		sat_result_free(r);
		return res;
	}
}

int main(int argc, char *argv[]){
	int mode = CDNF_Plus3;
	boolformula_t* c=NULL;
	while(c==NULL){
		c=learn (NULL, 2, mymembershipquery,NULL, myequivalencequery, mode);
	}
	fprintf(stderr,"\nFinished! Number of Mem. Q. =%d, Equ. Q. = %d\nResult:", memQ, equQ);
	boolformula_print(c);
	boolformula_free(c);
	fprintf(stderr,"\n");
	return 0;
}

inline sat_result_t* satisfible(boolformula_t * f){
	int tgtSize=0;
#ifdef DEBUG
	fprintf(stderr,"\n Ori:");
	boolformula_print(f);
#endif
	boolformula_t* temp=boolformula_to_cnf(f,boolformula_num_of_var(f));
#ifdef DEBUG
	fprintf(stderr,"\n CNF from Ori:");
	boolformula_print(temp);
#endif
	boolformula_t* temp2;
	int** tgt;
	uscalar_t i,j,num_clauses=0;
	switch(temp->t){
	case literal:
		tgt=malloc(sizeof(int*)*1);
		tgtSize=1;
		*(tgt)=malloc(sizeof(int)*2);
		*(*(tgt))=temp->d.l;
		*(*(tgt)+1)=0;
		num_clauses++;
		break;
	case conjunct:
		tgt=malloc(sizeof(int*)*temp->d.v->length);
		tgtSize=temp->d.v->length;

		for(i=0;i<temp->d.v->length;i++){
			num_clauses++;
			temp2=(boolformula_t*)vector_get(temp->d.v, i);
			if((temp2->t)==disjunct){
				*(tgt+i)=malloc(sizeof(int)*(temp2->d.v->length+1));
				for(j=0;j<temp2->d.v->length;j++){
					*(*(tgt+i)+j)= ((boolformula_t*)vector_get(temp2->d.v, j))->d.l;
				}
				*(*(tgt+i)+temp2->d.v->length)=0;
			}else{
				*(tgt+i)=malloc(sizeof(int)*2);
				*(*(tgt+i))= temp2->d.l;
				*(*(tgt+i)+1)= 0;
			}
		}

		break;
	default:
		printf("Something wrong\n");
		exit(14);
		break;
	}
	boolformula_free(temp);
	sat_result_t* ret=solve(tgt, num_clauses);
	for(i=0;i<tgtSize;i++){
		free(*(tgt+i));
		*(tgt+i)=NULL;
	}
	free(tgt);
	tgt=NULL;
#ifdef DEBUG
	if(ret->is_sat==1){
		fprintf(stderr,"\n SAT\n");

	}else{
		fprintf(stderr,"\n UNSAT\n");
	}
#endif
	return ret;
}
