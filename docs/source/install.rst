.. _install-doc:

Installation guide
==================

This document will guide you through the process of installing SymbiYosys.

CAD suite(s)
************

SymbiYosys (sby) is part of the `Tabby CAD Suite
<https://www.yosyshq.com/tabby-cad-datasheet>`_ and the `OSS CAD Suite
<https://github.com/YosysHQ/oss-cad-suite-build>`_! The easiest way to use sby
is to install the binary software suite, which contains all required
dependencies, including all supported solvers.

* `Contact YosysHQ <https://www.yosyshq.com/contact>`_ for a `Tabby CAD Suite
  <https://www.yosyshq.com/tabby-cad-datasheet>`_ Evaluation License and
  download link
* OR go to https://github.com/YosysHQ/oss-cad-suite-build/releases to download
  the free OSS CAD Suite
* Follow the `Install Instructions on GitHub
  <https://github.com/YosysHQ/oss-cad-suite-build#installation>`_

Make sure to get a Tabby CAD Suite Evaluation License for extensive
SystemVerilog Assertion (SVA) support, as well as industry-grade SystemVerilog
and VHDL parsers!

For more information about the difference between Tabby CAD Suite and the OSS
CAD Suite, please visit https://www.yosyshq.com/tabby-cad-datasheet.

Installing from source
**********************

Follow the instructions below to install SymbiYosys and its dependencies.
Yosys, SymbiYosys, and Z3 are non-optional. The other packages are only
required for some engine configurations.

Prerequisites
-------------

Installing prerequisites (this command is for Ubuntu 16.04):

.. code-block:: text

   sudo apt-get install build-essential clang bison flex libreadline-dev \
                        gawk tcl-dev libffi-dev git mercurial graphviz   \
                        xdot pkg-config python python3 libftdi-dev gperf \
                        libboost-program-options-dev autoconf libgmp-dev \
                        cmake curl

Required components
-------------------

Yosys, Yosys-SMTBMC and ABC
^^^^^^^^^^^^^^^^^^^^^^^^^^^

https://yosyshq.net/yosys/

https://people.eecs.berkeley.edu/~alanmi/abc/

Next install Yosys, Yosys-SMTBMC and ABC (``yosys-abc``):

.. code-block:: text

   git clone https://github.com/YosysHQ/yosys
   cd yosys
   make -j$(nproc)
   sudo make install

SymbiYosys
^^^^^^^^^^

https://github.com/YosysHQ/sby

.. code-block:: text

   git clone https://github.com/YosysHQ/sby
   cd sby
   sudo make install

Z3
^^

https://github.com/Z3Prover/z3/wiki

.. code-block:: text

   git clone https://github.com/Z3Prover/z3
   cd z3
   python scripts/mk_make.py
   cd build
   make -j$(nproc)
   sudo make install

Optional components
-------------------

Yices 2
^^^^^^^

http://yices.csl.sri.com/

.. code-block:: text

   git clone https://github.com/SRI-CSL/yices2
   cd yices2
   autoconf
   ./configure
   make -j$(nproc)
   sudo make install

super_prove
^^^^^^^^^^^

https://github.com/sterin/super-prove-build

.. code-block:: text

   sudo apt-get install cmake ninja-build g++ python-dev python-setuptools \
                        python-pip git
   git clone --recursive https://github.com/sterin/super-prove-build
   cd super-prove-build
   mkdir build
   cd build
   cmake -DCMAKE_BUILD_TYPE=Release -G Ninja ..
   ninja
   ninja package

This creates a .tar.gz archive for the target system. Extract it to
``/usr/local/super_prove``

.. code-block:: text

   sudo tar -C /usr/local -x super_prove-X-Y-Release.tar.gz

Then create a wrapper script ``/usr/local/bin/suprove`` with the following contents:

.. code-block:: text

   #!/bin/bash
   tool=super_prove; if [ "$1" != "${1#+}" ]; then tool="${1#+}"; shift; fi
   exec /usr/local/super_prove/bin/${tool}.sh "$@"

And make this wrapper script executable:

.. code-block:: text

   sudo chmod +x /usr/local/bin/suprove

Avy
^^^

https://arieg.bitbucket.io/avy/

.. code-block:: text

   git clone https://bitbucket.org/arieg/extavy.git
   cd extavy
   git submodule update --init
   mkdir build; cd build
   cmake -DCMAKE_BUILD_TYPE=Release ..
   make -j$(nproc)
   sudo cp avy/src/{avy,avybmc} /usr/local/bin/

Boolector
^^^^^^^^^

http://fmv.jku.at/boolector/

.. code-block:: text

   git clone https://github.com/boolector/boolector
   cd boolector
   ./contrib/setup-btor2tools.sh
   ./contrib/setup-lingeling.sh
   ./configure.sh
   make -C build -j$(nproc)
   sudo cp build/bin/{boolector,btor*} /usr/local/bin/
   sudo cp deps/btor2tools/bin/btorsim /usr/local/bin/

