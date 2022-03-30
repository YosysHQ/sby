SH_FILES=$(wildcard *.sh)
SH_TESTS=$(addprefix test_,$(SH_FILES:.sh=))

test: $(SH_TESTS)

test_%: %.sh FORCE
	bash $<

FORCE:

.PHONY: test FORCE
