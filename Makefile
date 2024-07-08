
DESTDIR =
PREFIX ?= /usr/local
PROGRAM_PREFIX =

# On Windows, manually setting absolute path to Python binary may be required
# for launcher executable to work. From MSYS2, this can be done using the
# following command: "which python3 | cygpath -w -m -f -".
ifeq ($(OS), Windows_NT)
PYTHON = $(shell cygpath -w -m $(PREFIX)/bin/python3)
endif

ifeq ($(file < .gittag),$$Format:%(describe)$$)
YOSYS_RELEASE_VERSION := SBY $(shell git describe --dirty)
else
YOSYS_RELEASE_VERSION := SBY $(file < .gittag)
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
	@echo "    run tests, skipping tests with missing dependencies"
	@echo ""
	@echo "make ci"
	@echo "    run all tests, failing tests with missing dependencies"
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
		-e "s|##yosys-release-version##|release_version = '$(YOSYS_RELEASE_VERSION)'|;" \
		-e "s|#!/usr/bin/env python3|#!$(PYTHON)|" < sbysrc/sby.py > $(DESTDIR)$(PREFIX)/bin/sby-script.py
	gcc -DGUI=0 -O -s -o $(DESTDIR)$(PREFIX)/bin/sby.exe extern/launcher.c
else
	sed -e 's|##yosys-sys-path##|sys.path += [os.path.dirname(__file__) + p for p in ["/share/python3", "/../share/yosys/python3"]]|;' \
		-e "s|##yosys-release-version##|release_version = '$(YOSYS_RELEASE_VERSION)'|;" < sbysrc/sby.py > $(DESTDIR)$(PREFIX)/bin/sby
	chmod +x $(DESTDIR)$(PREFIX)/bin/sby
endif

.PHONY: check_cad_suite run_ci

ci: check_cad_suite
	@$(MAKE) run_ci

run_ci:
	$(MAKE) test NOSKIP=1
	if yosys -qp 'read -verific' 2> /dev/null; then set -x; \
		YOSYS_NOVERIFIC=1 $(MAKE) run_ci; \
	fi

check_cad_suite:
	@if ! which tabbypip >/dev/null 2>&1; then \
		echo "'make ci' requries the Tabby CAD Suite or the OSS CAD Suite"; \
		echo "try 'make test' instead or run 'make run_ci' to proceed anyway."; \
		exit 1; \
	fi

test_demo1:
	cd sbysrc && python3 sby.py -f demo1.sby

test_demo2:
	cd sbysrc && python3 sby.py -f demo2.sby

test_demo3:
	cd sbysrc && python3 sby.py -f demo3.sby

test:
	$(MAKE) -C tests test

html:
	$(MAKE) -C docs html

clean:
	$(MAKE) -C docs clean
	rm -rf docs/build sbysrc/sby sbysrc/__pycache__
