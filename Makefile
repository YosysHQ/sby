
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
	pip3 install -e .

html:
	make -C docs html

clean:
	make -C docs clean
	rm -rf docs/build sbysrc/sby sbysrc/__pycache__

