
DESTDIR =
PREFIX = /usr/local
PROGRAM_PREFIX =

# On Windows, manually setting absolute path to Python binary may be required
# for launcher executable to work. From MSYS2, this can be done using the
# following command: "which python3 | cygpath -w -m -f -".
ifeq ($(OS), Windows_NT)
PYTHON = $(shell cygpath -w -m $(PREFIX)/bin/python3)
endif

.PHONY: help install ci test html clean

help:
	@echo ""
	@echo "sudo make install"
	@echo "    build and install SymbiYosys (sby)"
	@echo ""
	@echo "make html"
	@echo "    build documentation in docs/build/html/"
	@echo ""
	@echo "make test"
	@echo "    run tests"
	@echo ""
	@echo "make ci"
	@echo "    run tests and check examples"
	@echo "    note: this requires a full Tabby CAD Suite or OSS CAD Suite install"
	@echo ""
	@echo "make clean"
	@echo "    cleanup"
	@echo ""

install:
	mkdir -p $(DESTDIR)$(PREFIX)/bin
	mkdir -p $(DESTDIR)$(PREFIX)/share/yosys/python3
	cp sbysrc/sby_*.py $(DESTDIR)$(PREFIX)/share/yosys/python3/
	sed -e 's|##yosys-program-prefix##|"'$(PROGRAM_PREFIX)'"|' < sbysrc/sby_core.py > $(DESTDIR)$(PREFIX)/share/yosys/python3/sby_core.py
ifeq ($(OS), Windows_NT)
	sed -e 's|##yosys-sys-path##|sys.path += [os.path.dirname(__file__) + p for p in ["/share/python3", "/../share/yosys/python3"]]|;' \
		-e "s|#!/usr/bin/env python3|#!$(PYTHON)|" < sbysrc/sby.py > $(DESTDIR)$(PREFIX)/bin/sby-script.py
	gcc -DGUI=0 -O -s -o $(DESTDIR)$(PREFIX)/bin/sby.exe extern/launcher.c
else
	sed 's|##yosys-sys-path##|sys.path += [os.path.dirname(__file__) + p for p in ["/share/python3", "/../share/yosys/python3"]]|;' < sbysrc/sby.py > $(DESTDIR)$(PREFIX)/bin/sby
	chmod +x $(DESTDIR)$(PREFIX)/bin/sby
endif

ci: \
  test_demo1 test_demo2 test_demo3 \
  test_abstract_abstr test_abstract_props \
  test_demos_fib_cover test_demos_fib_prove test_demos_fib_live \
  test_multiclk_dpmem \
  test_puzzles_djb2hash test_puzzles_pour853to4 test_puzzles_wolfgoatcabbage \
  test_puzzles_primegen_primegen test_puzzles_primegen_primes_pass test_puzzles_primegen_primes_fail \
  test_quickstart_demo test_quickstart_cover test_quickstart_prove test_quickstart_memory \
  test
	if yosys -qp 'read -verific' 2> /dev/null; then set -x; \
		YOSYS_NOVERIFIC=1 $(MAKE) ci; \
	fi

test_demo1:
	cd sbysrc && python3 sby.py -f demo1.sby

test_demo2:
	cd sbysrc && python3 sby.py -f demo2.sby

test_demo3:
	cd sbysrc && python3 sby.py -f demo3.sby

test_abstract_abstr:
	@if yosys -qp 'read -verific' 2> /dev/null; then set -x; \
		cd docs/examples/abstract && python3 ../../../sbysrc/sby.py -f abstr.sby; \
	else echo "skipping $@"; fi

test_abstract_props:
	if yosys -qp 'read -verific' 2> /dev/null; then set -x; \
		cd docs/examples/abstract && python3 ../../../sbysrc/sby.py -f props.sby; \
	else echo "skipping $@"; fi

test_demos_fib_cover:
	cd docs/examples/demos && python3 ../../../sbysrc/sby.py -f fib.sby cover

test_demos_fib_prove:
	cd docs/examples/demos && python3 ../../../sbysrc/sby.py -f fib.sby prove

test_demos_fib_live:
	cd docs/examples/demos && python3 ../../../sbysrc/sby.py -f fib.sby live

test_multiclk_dpmem:
	cd docs/examples/multiclk && python3 ../../../sbysrc/sby.py -f dpmem.sby

test_puzzles_djb2hash:
	cd docs/examples/puzzles && python3 ../../../sbysrc/sby.py -f djb2hash.sby

test_puzzles_pour853to4:
	cd docs/examples/puzzles && python3 ../../../sbysrc/sby.py -f pour_853_to_4.sby

test_puzzles_wolfgoatcabbage:
	cd docs/examples/puzzles && python3 ../../../sbysrc/sby.py -f wolf_goat_cabbage.sby

test_puzzles_primegen_primegen:
	cd docs/examples/puzzles && python3 ../../../sbysrc/sby.py -f primegen.sby primegen

test_puzzles_primegen_primes_pass:
	cd docs/examples/puzzles && python3 ../../../sbysrc/sby.py -f primegen.sby primes_pass

test_puzzles_primegen_primes_fail:
	cd docs/examples/puzzles && python3 ../../../sbysrc/sby.py -f primegen.sby primes_fail

test_quickstart_demo:
	cd docs/examples/quickstart && python3 ../../../sbysrc/sby.py -f demo.sby

test_quickstart_cover:
	cd docs/examples/quickstart && python3 ../../../sbysrc/sby.py -f cover.sby

test_quickstart_prove:
	cd docs/examples/quickstart && python3 ../../../sbysrc/sby.py -f prove.sby

test_quickstart_memory:
	cd docs/examples/quickstart && python3 ../../../sbysrc/sby.py -f memory.sby

test:
	$(MAKE) -C tests test

html:
	$(MAKE) -C docs html

clean:
	$(MAKE) -C docs clean
	rm -rf docs/build sbysrc/sby sbysrc/__pycache__
