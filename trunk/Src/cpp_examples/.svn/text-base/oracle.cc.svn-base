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

extern "C"{
#include <type.h>
#include <bitvector.h>
#include <vector.h>
}

#include <signal.h>
#include <zlib.h>
#include <minisat_stub.h>
extern "C"{
#include <boolformula.h>
#include <cdnfformula.h>
#include <query.h>
#include <cdnf.h>
}
#include "oracle.h"

boolformula_t* myformula;
int cmemQ=0, memQ=0, equQ=0;

membership_result_t mycomembershipquery (void *info, bitvector *bv){
	cmemQ++;
	unsigned i;
#ifdef DEBUG
	fprintf(stderr,"\n Co-Mem. Query#%d:", cmemQ);
	for(i=1;i<bv->length;i++){
		if(bitvector_get(bv, i))
			fprintf(stderr,"%d ", i);
		else
			fprintf(stderr,"%d ", -i);
	}
	fprintf(stderr,"\n");
#endif

	boolformula_t* mem=boolformula_conjunction_new(bv->length);
	boolformula_t* temp=boolformula_neg(boolformula_copy(myformula));
	boolformula_set(mem,0,temp);
	boolformula_free(temp);
	for(i=1;i<bv->length;i++){
		if(bitvector_get(bv, i)){
			temp=boolformula_literal_new(i);
			boolformula_set(mem,i,temp);
			boolformula_free(temp);
		}else{
			temp=boolformula_literal_new(-i);
			boolformula_set(mem,i,temp);
			boolformula_free(temp);
		}
	}
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

}


membership_result_t mymembershipquery (void *info, bitvector *bv){
	memQ++;
	unsigned i;
#ifdef DEBUG
	fprintf(stderr,"\n Mem. Query#%d:", memQ);
	for(i=1;i<bv->length;i++){
		if(bitvector_get(bv, i))
			fprintf(stderr,"%d ", i);
		else
			fprintf(stderr,"%d ", -i);
	}
	fprintf(stderr,"\n");
#endif

	boolformula_t* mem=boolformula_conjunction_new(bv->length);
	boolformula_t* temp=boolformula_copy(myformula);
	boolformula_set(mem,0,temp);
	boolformula_free(temp);

	for(i=1;i<bv->length;i++){
		if(bitvector_get(bv, i)){
			temp=boolformula_literal_new(i);
			boolformula_set(mem,i,temp);
			boolformula_free(temp);
		}else{
			temp=boolformula_literal_new(-i);
			boolformula_set(mem,i,temp);
			boolformula_free(temp);
		}
	}
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

}

bitvector* getce(sat_result_t* r, uscalar_t num_vars){
#ifdef DEBUG
	fprintf(stderr,"CE: ");
#endif

	bitvector *bv = bitvector_new(num_vars+1);
	unsigned i;
	for(i=0;i<(unsigned)r->cesize;i++){
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

equivalence_result_t* myequivalencequery (void *info, uscalar_t num_vars, boolformula_t * b){
	equQ++;

#ifdef DEBUG
	fprintf(stderr,"\n Equ. Query#%d:", equQ);
	boolformula_t* temp=cdnf_to_boolformula(f);
	_boolformula_print(temp);
	boolformula_free(temp);
	fprintf(stderr,"\n");
#endif
	equivalence_result_t* res = (equivalence_result_t*)malloc(sizeof(equivalence_result_t));
	boolformula_t* equ=boolformula_disjunction_new(2);
	boolformula_t* temp1=boolformula_neg(boolformula_copy(myformula));
	boolformula_t* temp2=boolformula_copy(b);

	boolformula_set(equ,0,temp1);
	boolformula_set(equ,1,temp2);
	boolformula_neg(equ);
	sat_result_t* r=satisfible(equ);
	boolformula_free(equ);
	boolformula_free(temp1);
	boolformula_free(temp2);

	if(r->is_sat==1){//not equivalent
		res->is_equal=false;
#ifdef DEBUG
		fprintf(stderr,"\n +");
#endif
		res->counterexample=getce(r,num_vars);
		sat_result_free(r);
	}else{
		sat_result_free(r);
		equ=boolformula_disjunction_new(2);
		temp1=boolformula_copy(myformula);
		temp2=boolformula_neg(b);
		boolformula_set(equ,0,temp1);
		boolformula_set(equ,1,temp2);
		boolformula_neg(equ);
		r=satisfible(equ);
		boolformula_free(equ);
		boolformula_free(temp1);

		if(r->is_sat==1){//not equivalent
			res->is_equal=false;
#ifdef DEBUG
			fprintf(stderr,"\n -");
#endif
			res->counterexample=getce(r,num_vars);
			sat_result_free(r);
		}else{
			sat_result_free(r);
			res->is_equal=true;
		}
	}
        boolformula_free (b);
	return res;
}

char skipline(){
	char c;
	c = getchar();
	while (c != EOF) {
		if(c=='\n')
			break;
		c = getchar();
	}
	return c;
}

boolformula_t* read_DIMACS(){
	int num_var, num_clauses, lit;
	boolformula_t* ret=boolformula_conjunction_unit(), *temp;
	char c;
	c = getchar();
	while (c != EOF) {
	    if(c=='c'){
	    	skipline();
	    	c = getchar();
	    }else if(c=='p'){
	    	c = getchar();
	    	assert(c==' ');
	    	c = getchar();
	    	assert(c=='c');
	    	c = getchar();
	    	assert(c=='n');
	    	c = getchar();
	    	assert(c=='f');
	    	scanf("%d",&num_var);
	    	scanf("%d",&num_clauses);
	    	skipline();
	    }else{
	    	boolformula_t* clause=boolformula_disjunction_unit();
	    	bool canAdd=false;
	    	do{
				scanf("%d",&lit);
				if(lit!=0){
		    			canAdd=true;
		    			temp=boolformula_literal_new(lit);
					boolformula_add(clause, temp);
					boolformula_free(temp);
				}
	    	}while(lit!=0);
	    	if(canAdd)
	    		boolformula_add(ret,clause);
		boolformula_free(clause);
	    	c=skipline();
	    }
	}

	return ret;
}

void print_help(){
        printf("Usage: learn mode < input\n");
        printf(" mode = 0, using CDNF algorithm\n");
        printf(" mode = 1, using CDNF+ algorithm\n");
        printf(" mode = 2, using CDNF++ algorithm\n");
        printf(" input should contain a CNF formula in DIMACS format\n");
        exit(-1);
}


int main(int argc, char *argv[]){
	double startNum=1;
	int mode=CDNF;

	if(argc==2){
		mode =  atoi( argv[1] );
		if(mode != CDNF && mode != CDNF_Plus && mode != CDNF_PlusPlus)
			print_help();
                myformula=read_DIMACS();
                if(mode ==CDNF){
                        startNum=boolformula_num_of_var(myformula);
                }

	}else{
		print_help();
	}
        boolformula_t* c=learn (NULL, startNum, mymembershipquery,mycomembershipquery, myequivalencequery, mode);
	fprintf(stderr,"\nFinished! Number of Mem. Q. =%d, co-Mem. Q= %d, Equ. Q. = %d\nResult:", memQ, cmemQ, equQ);
	boolformula_print(c);
	boolformula_free(c);
	fprintf(stderr,"\n");
	return 0;
}


inline sat_result_t* satisfible(boolformula_t * f){
	uscalar_t tgtSize=0;
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
		tgt=(int**)malloc(sizeof(int*)*1);
		tgtSize=1;
		*(tgt)=(int*)malloc(sizeof(int)*2);
		*(*(tgt))=temp->d.l;
		*(*(tgt)+1)=0;
		num_clauses++;
		break;
	case conjunct:
		tgt=(int**)malloc(sizeof(int*)*temp->d.v->length);
		tgtSize=temp->d.v->length;

		for(i=0;i<temp->d.v->length;i++){
			num_clauses++;
			temp2=(boolformula_t*)vector_get(temp->d.v, i);
			if((temp2->t)==disjunct){
				*(tgt+i)=(int*)malloc(sizeof(int)*(temp2->d.v->length+1));
				for(j=0;j<temp2->d.v->length;j++){
					*(*(tgt+i)+j)= ((boolformula_t*)vector_get(temp2->d.v, j))->d.l;
				}
				*(*(tgt+i)+temp2->d.v->length)=0;
			}else{
				*(tgt+i)=(int*)malloc(sizeof(int)*2);
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
