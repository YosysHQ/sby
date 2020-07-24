SBY_FILES=$(wildcard *.sby)
SBY_TESTS=$(addprefix test_,$(SBY_FILES:.sby=))

.PHONY: test

FORCE:

test: $(SBY_TESTS)

test_%: %.sby FORCE
	python3 ../sbysrc/sby.py -f $<
