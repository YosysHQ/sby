
DESTDIR =
PREFIX = /usr/local

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
	cp sbysrc/sby_*.py $(DESTDIR)$(PREFIX)/share/yosys/python3/
	sed 's|##yosys-sys-path##|sys.path += [os.path.dirname(__file__) + p for p in ["/share/python3", "/../share/yosys/python3"]]|;' < sbysrc/sby.py > $(DESTDIR)$(PREFIX)/bin/sby
	chmod +x $(DESTDIR)$(PREFIX)/bin/sby

html:
	make -C docs html

clean:
	make -C docs clean
	rm -rf docs/build sbysrc/sby sbysrc/__pycache__

