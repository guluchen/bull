/*****************************************************************************
 *
 * 
 * Author: Yu-Fang Chen
 * Copyright reserved
 *****************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <type.h>
#include <vector.h>
#include "bitvector.h"
#include "boolformula.h"
#include "query.h"
#include "cdnf.h"
#include <jni.h>

#include <stdlib.h>
#include <errno.h>

#include <signal.h>
#include <zlib.h>
#include "Cdnfp.h"
JNIEnv* env;
jobject boolformula_c2java(boolformula_t* f){
	if(f==NULL)
		return NULL;
	jclass cls= (*env) ->FindClass(env,"BooleanFormula");
	if(cls == 0){
		printf("Cannot Find the Class BooleanFormula\n");
		exit(0);
	}
	
	jmethodID mid =(*env)->GetMethodID(env, cls, "<init>", "(I)V");
	if(mid == 0){
		printf("Cannot Find MethodID for the Constructor of BooleanFormula\n");
		exit(0);
	}
	if(boolformula_get_type(f)==literal){
		jobject java_f=(*env)->NewObject(env,cls, mid, 2);

		if(java_f == 0){
			printf("Cannot Find MethodID for the Constructor of BooleanFormula\n");
			exit(0);
		}
		jmethodID mid2=(*env)->GetMethodID(env, cls, "setLit", "(I)V");
		if(mid2 == 0){
			printf("Cannot Find MethodID for setLit\n");
			exit(0);
		}

		jint r=boolformula_get_value(f);
		(*env)->CallVoidMethod(env,java_f, mid2, r);
		(*env)->DeleteLocalRef( env, cls ); 
		return java_f;
	}else if (boolformula_get_type(f)==conjunct){
		jobject java_f=(*env)->NewObject(env,cls, mid, 0);
		int i;
		for(i=0;i<boolformula_get_length(f);i++){
			boolformula_t* subf=boolformula_get_subformula(f,i);
			jobject java_subf=boolformula_c2java(subf);
			jmethodID mid2=(*env)->GetMethodID(env, cls, "add", "(LBooleanFormula;)V");
			if(mid2 == 0){
				printf("Cannot Find MethodID for add\n");
				exit(0);
			}
			(*env)->CallVoidMethod(env,java_f, mid2, java_subf);
		}
		(*env)->DeleteLocalRef( env, cls ); 
		return java_f;
	}else{
		jobject java_f=(*env)->NewObject(env,cls, mid, 1);
		int i;
		for(i=0;i<boolformula_get_length(f);i++){
			boolformula_t* subf=boolformula_get_subformula(f,i);
			jobject java_subf=boolformula_c2java(subf);
			jmethodID mid2=(*env)->GetMethodID(env, cls, "add", "(LBooleanFormula;)V");
			if(mid2 == 0){
				printf("Cannot Find MethodID for add\n");
				exit(0);
			}
			(*env)->CallVoidMethod(env,java_f, mid2, java_subf);
		}
		(*env)->DeleteLocalRef( env, cls ); 
		return java_f;
	}
}

membership_result_t is_member (void *info, bitvector *bv)
{
	jclass cls= (*env) ->FindClass(env,"Cdnfp");
        if(cls == 0){
                printf("Cannot Find the Class Cdnfp\n");
                exit(0);
	}      
        jmethodID mid =(*env)->GetMethodID(env, cls, "<init>", "()V");
        if(mid == 0){
                printf("Cannot Find MethodID for the Constructor of Cdnfp\n");
                exit(0);
        }
	jobject cdnfp=(*env)->NewObject(env,cls, mid);
	
	if(cdnfp == 0){
		printf("Cannot Create New Cdnfp Object\n");
		exit(0);
	}
        jmethodID mid2=(*env)->GetMethodID(env, cls, "isMem", "([Z)Z");
        if(mid2 == 0){
                printf("Cannot Find MethodID for isMem\n");
                exit(0);
	}
	jbooleanArray ba = (*env)->NewBooleanArray(env, bv->length);
	jboolean* pba = (*env)->GetBooleanArrayElements( env, ba, 0 );
  	
	int i;
        for(i=0;i<bv->length;i++){
                if(bitvector_get(bv, i)){
			pba[i]=JNI_TRUE;
                }else{
                	pba[i]=JNI_FALSE;
		}
        }
	(*env)->ReleaseBooleanArrayElements( env, ba, pba, 0 );
        jboolean result=(*env)->CallBooleanMethod(env,cdnfp, mid2, ba);
	(*env)->DeleteLocalRef( env, cls ); 
	(*env)->DeleteLocalRef( env, cdnfp ); 
	if(result==JNI_TRUE)
		return true;
	else
		return false;
}

membership_result_t is_comember (void *info, bitvector *bv)
{
	jclass cls= (*env) ->FindClass(env,"Cdnfp");
        if(cls == 0){
                printf("Cannot Find the Class Cdnfp\n");
                exit(0);
	}      
        jmethodID mid =(*env)->GetMethodID(env, cls, "<init>", "()V");
        if(mid == 0){
                printf("Cannot Find MethodID for the Constructor of Cdnfp\n");
                exit(0);
        }
	jobject cdnfp=(*env)->NewObject(env,cls, mid);
	
	if(cdnfp == 0){
		printf("Cannot Create New Cdnfp Object\n");
		exit(0);
	}
        jmethodID mid2=(*env)->GetMethodID(env, cls, "isCoMem", "([Z)Z");
        if(mid2 == 0){
                printf("Cannot Find MethodID for isCoMem\n");
                exit(0);
	}
	jbooleanArray ba = (*env)->NewBooleanArray(env, bv->length);
	jboolean* pba = (*env)->GetBooleanArrayElements( env, ba, 0 );
  	
	int i;
        for(i=0;i<bv->length;i++){
                if(bitvector_get(bv, i)){
			pba[i]=JNI_TRUE;
                }else{
                	pba[i]=JNI_FALSE;
		}
        }
	(*env)->ReleaseBooleanArrayElements( env, ba, pba, 0 );
        jboolean result=(*env)->CallBooleanMethod(env,cdnfp, mid2, ba);
	(*env)->DeleteLocalRef( env, cls ); 
	(*env)->DeleteLocalRef( env, cdnfp ); 
	if(result==JNI_TRUE)
		return true;
	else
		return false;
}

equivalence_result_t *is_equivalent (void *info, uscalar_t num_vars, boolformula_t *bool_f)
{

	jclass cls= (*env) ->FindClass(env,"Cdnfp");
        if(cls == 0){
                printf("Cannot Find the Class Cdnfp\n");
                exit(0);
	}      
        jmethodID mid =(*env)->GetMethodID(env, cls, "<init>", "()V");
        if(mid == 0){
                printf("Cannot Find MethodID for the Constructor of Cdnfp\n");
                exit(0);
        }
	jobject cdnfp=(*env)->NewObject(env,cls, mid);
	
	if(cdnfp == 0){
		printf("Cannot Create New Cdnfp Object\n");
		exit(0);
	}
        jmethodID mid2=(*env)->GetMethodID(env, cls, "isEqu", "(ILBooleanFormula;)[Z");
        if(mid2 == 0){
                printf("Cannot Find MethodID for isEqu\n");
                exit(0);
	}

        jbooleanArray result=(*env)->CallObjectMethod(env,cdnfp, mid2, num_vars, boolformula_c2java(bool_f));
	
	equivalence_result_t* res = malloc(sizeof(equivalence_result_t));
	(*env)->DeleteLocalRef( env, cls ); 
	(*env)->DeleteLocalRef( env, cdnfp ); 
	
	if(result == NULL){
		res->is_equal=true;
	}else{
		res->is_equal=false;
		bitvector *bv = bitvector_new((*env)->GetArrayLength(env,result));
		int j;
		for(j=0;j<(*env)->GetArrayLength(env,result);j++){
			bitvector_set(bv,j,(*env)->GetBooleanArrayElements(env,result,JNI_FALSE)[j]==JNI_TRUE);
		}
		res->counterexample=bv;
	}
        boolformula_free (bool_f);
        return res;
}




JNIEXPORT jobject JNICALL Java_Cdnfp_learn (JNIEnv * jenv, jobject jobj, jint numVar, jint mode){
	env=jenv;
	boolformula_t* c=learn (NULL, numVar, is_member, is_comember, is_equivalent, mode);
		
	return boolformula_c2java(c);
}
