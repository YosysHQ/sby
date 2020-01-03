
PREFIX ?= /usr/local

# On Windows, manually setting absolute path to Python binary may be required
# for launcher executable to work. From MSYS2, this can be done using the
# following command: "which python3 | cygpath -w -m -f -".
ifeq ($(OS), Windows_NT)
PYTHON = $(shell cygpath -w -m $(PREFIX)/bin/python3)
endif

help:
	@echo ""
	@echo "sudo make install"
	@echo "    build and install SymbiYosys (sby)"
	@echo ""
	@echo "make html"
	@echo "    build documentation in docs/build/html/"
	@echo ""
	@echo "make clean"
	@echo "    cleanup"
	@echo ""

install:
	mkdir -p $(DESTDIR)$(PREFIX)/bin
	mkdir -p $(DESTDIR)$(PREFIX)/share/yosys/python3
	cp sbysrc/sby_*.py $(DESTDIR)$(PREFIX)/share/yosys/python3/
ifeq ($(OS), Windows_NT)
	sed -e 's|##yosys-sys-path##|sys.path += [os.path.dirname(__file__) + p for p in ["/share/python3", "/../share/yosys/python3"]]|;' \
		-e "s|#!/usr/bin/env python3|#!$(PYTHON)|" < sbysrc/sby.py > $(DESTDIR)$(PREFIX)/bin/sby-script.py
	gcc -DGUI=0 -O -s -o $(DESTDIR)$(PREFIX)/bin/sby.exe extern/launcher.c
else
	sed 's|##yosys-sys-path##|sys.path += [os.path.dirname(__file__) + p for p in ["/share/python3", "/../share/yosys/python3"]]|;' < sbysrc/sby.py > $(DESTDIR)$(PREFIX)/bin/sby
	chmod +x $(DESTDIR)$(PREFIX)/bin/sby
endif

html:
	make -C docs html

clean:
	make -C docs clean
	rm -rf docs/build sbysrc/sby sbysrc/__pycache__

