SBY_FILES=$(wildcard *.sby)
SBY_TESTS=$(addprefix test_,$(SBY_FILES:.sby=))
CHECK_PY_FILES=$(wildcard *.check.py)
CHECK_PY_TASKS=$(addprefix check_,$(CHECK_PY_FILES:.check.py=))
JUNIT_TESTS=junit_assert_pass junit_assert_fail junit_assert_preunsat \
junit_cover_pass junit_cover_uncovered junit_cover_assert junit_cover_preunsat \
junit_timeout_error_timeout junit_timeout_error_syntax junit_timeout_error_solver

.PHONY: test validate_junit scripted

test: $(JUNIT_TESTS) $(CHECK_PY_TASKS)

test_%: %.sby FORCE
	python3 ../sbysrc/sby.py -f $<

$(CHECK_PY_TASKS): check_%: %.check.py test_%
	python3 $<

$(JUNIT_TESTS): $(SBY_TESTS)
	python3 validate_junit.py $@/$@.xml

scripted:
	make -C scripted

FORCE:
