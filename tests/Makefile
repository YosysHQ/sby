SBY_FILES=$(wildcard *.sby)
SBY_TESTS=$(addprefix test_,$(SBY_FILES:.sby=))
JUNIT_TESTS=junit_assert_pass junit_assert_fail junit_assert_preunsat \
junit_cover_pass junit_cover_uncovered junit_cover_assert junit_cover_preunsat \
junit_timeout_error_timeout junit_timeout_error_syntax junit_timeout_error_solver

.PHONY: test validate_junit scripted

test: $(JUNIT_TESTS)

test_%: %.sby FORCE
	python3 ../sbysrc/sby.py -f $<

$(JUNIT_TESTS): $(SBY_TESTS)
	python3 validate_junit.py $@/$@.xml

scripted:
	make -C scripted

FORCE:
