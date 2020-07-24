SBY_FILES=$(wildcard *.sby)
SBY_TESTS=$(addprefix test_,$(SBY_FILES:.sby=))

.PHONY: test $(SBY_TESTS)

test: $(SBY_TESTS)

test_%: %.sby
	python3 ../sbysrc/sby.py -f $<
