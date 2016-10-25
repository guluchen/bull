OCAMLTOP := $(wildcard /usr/local/lib/ocaml /opt/local/lib/ocaml)
OCAMLOPT = ocamlopt.opt      # OCaml native compiler
OCAMLC = ocamlc.opt          # OCaml bytecode compiler
OCAMLDEP = ocamldep.opt      # OCaml dependency maker
CC = gcc -D__STDC_LIMIT_MACROS -D__STDC_FORMAT_MACROS
CXX = g++ -D__STDC_LIMIT_MACROS -D__STDC_FORMAT_MACROS
MINISATDIR = ../solvers/minisat
CORE = ../core

CFLAGS = -I$(OCAMLTOP) -I$(CORE)
CXXFLAGS = -I$(OCAMLTOP) -I$(MINISATDIR) -I$(CORE)
LDFLAGS = -L$(CORE)

TARGET = learn.byte
OPTTARGET = $(patsubst %.byte, %.opt, $(TARGET))

SOURCES = minisat.ml minisat_stubs.cc \
	cdnfp.ml cdnfp_stubs.c \
	boolFormula.ml query.ml \
	oracla.ml \
	main.ml

OBJS    = minisat.cmo minisat_stubs.o \
	cdnfp.cmo cdnfp_stubs.o \
	boolFormula.cmo query.cmo \
	oracle.cmo \
	main.cmo

OPTOBJS	= $(patsubst %.cmo, %.cmx, $(OBJS))


all: byte opt

byte: $(OBJS)
	$(OCAMLC) -custom -o learn.byte $(OBJS) \
	-cclib $(LDFLAGS) -cclib -lcdnfp \
	$(MINISATDIR)/core/Solver.o \
	-cclib -lstdc++

opt: $(OPTOBJS)
	$(OCAMLOPT) -o learn.opt $(OPTOBJS) \
	-cclib $(LDFLAGS) -cclib -lcdnfp \
	$(MINISATDIR)/core/Solver.o \
	-cclib -lstdc++

clean:
	rm -f $(TARGET) $(OPTTARGET) *.o *.cmo *.cmx *.cmi

.SUFFIXES: .cc .c .o .mli .ml .cmi .cmo .cmx

.mli.cmi:
	$(OCAMLC) $(MLFLAGS) -c $<

.ml.cmx: 
	$(OCAMLOPT) $(MLFLAGS) -c $<

.ml.cmo:
	$(OCAMLC) $(MLFLAGS) -c $<

.c.o:
	$(CC) $(CFLAGS) -c -o $@ $<

.cc.o:
	$(CXX) $(CXXFLAGS) -c -o $@ $<

.depend:
	$(OCAMLDEP) *.mli *.ml > .depend 

include .depend
