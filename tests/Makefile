test:

.PHONY: test clean refresh help

help:
	@cat make/help.txt

export SBY_WORKDIR_GITIGNORE=1
export SBY_MAIN=$(realpath $(dir $(firstword $(MAKEFILE_LIST)))/../sbysrc/sby.py)

make/rules/collect.mk: make/collect_tests.py
	python3 make/collect_tests.py

make/rules/test/%.mk:
	python3 make/test_rules.py $<

ifneq (help,$(MAKECMDGOALS))
include make/rules/collect.mk
endif
