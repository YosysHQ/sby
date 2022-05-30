test:

.PHONY: test clean refresh help

TOOL_LIST := \
	btorsim \
	yices \
	aigbmc \
	avy \
	bitwuzla \
	boolector \
	btormc \
	cvc4 \
	mathsat \
	pono \
	suprove \
	yices-smt2 \
	yices \
	yosys-abc \
	z3

help:
	@cat make/help.txt

export SBY_WORKDIR_GITIGNORE=1
export SBY_MAIN=$(realpath $(dir $(firstword $(MAKEFILE_LIST)))/../sbysrc/sby.py)

make/rules/collect.mk: make/collect_tests.py
	python3 make/collect_tests.py

make/rules/test/%.mk:
	python3 make/test_rules.py $<

ifneq (help,$(MAKECMDGOALS))

FIND_TOOLS := $(shell \
	TOOLS=$$(which $(TOOL_LIST) 2>/dev/null || true); \
	echo $$TOOLS | cmp -s make/rules/found_tools || echo $$TOOLS > make/rules/found_tools \
)

include make/rules/collect.mk

endif
