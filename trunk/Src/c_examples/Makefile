PROGRAM = learn
CC = gcc
CXX = g++
CORE = ../core
MINISAT = ../solvers/minisat
CORELIB = cdnfp

CFLAGS = -O2 -g -Wall -c -fmessage-length=0 -I$(CORE) -I$(MINISAT) -I./
CXXFLAGS = -O2 -g -Wall -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -c -fmessage-length=0 -I$(CORE) -I$(MINISAT) -I./
LDFLAGS   := $(MINISAT)/core/Solver.o -L$(CORE) -Wall -l$(CORELIB) -lz


SRCS = oracle.c minisat_stub.cc

OBJS = oracle.o minisat_stub.o

all: $(PROGRAM)
$(PROGRAM) : $(OBJS)
	$(CXX) -o $(PROGRAM) $(OBJS) $(LDFLAGS)

learn_inv: learn_inv.o minisat_stub.o
	$(CXX) -o learn_inv learn_inv.o minisat_stub.o $(LDFLAGS)
%.o:%.c
	$(CC) $(CFLAGS) $<
%.o:%.cc
	$(CXX) $(CXXFLAGS) $<
clean:
	rm -f *.o 
	rm -f learn 
	rm -f learn_inv 

