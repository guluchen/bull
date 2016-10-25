UNAME := $(shell uname)

ifeq ($(UNAME), Linux)
include Makefile.linux
endif
ifeq ($(UNAME), Darwin)
include Makefile.macos
endif

