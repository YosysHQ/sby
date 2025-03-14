.. _install-doc:

Installation guide
==================

This document will guide you through the process of installing sby.

CAD suite(s)
************

Sby (SymbiYosys) is part of the `Tabby CAD Suite
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

Follow the instructions below to install sby and its dependencies. Yosys and sby
are non-optional.  Boolector is recommended to install but not required.  The
other packages are only required for some engine configurations.

Prerequisites
-------------

Installing prerequisites (this command is for Ubuntu 20.04):

.. code-block:: text

   sudo apt-get install build-essential clang bison flex \
                        libreadline-dev gawk tcl-dev libffi-dev git \
                        graphviz xdot pkg-config python3 zlib1g-dev
   
   python3 -m pip install click

Required components
-------------------

Yosys, Yosys-SMTBMC and ABC
^^^^^^^^^^^^^^^^^^^^^^^^^^^

https://yosyshq.net/yosys/

https://people.eecs.berkeley.edu/~alanmi/abc/

Note that this will install Yosys, Yosys-SMTBMC and ABC (as ``yosys-abc``):

.. code-block:: text

   git clone https://github.com/YosysHQ/yosys --recurse-submodules
   cd yosys
   make -j$(nproc)
   sudo make install

sby
^^^

https://github.com/YosysHQ/sby

.. code-block:: text

   git clone https://github.com/YosysHQ/sby
   cd sby
   sudo make install

Recommended components
----------------------

Boolector
^^^^^^^^^

https://boolector.github.io

.. code-block:: text
    
    git clone https://github.com/boolector/boolector
    cd boolector
    ./contrib/setup-btor2tools.sh
    ./contrib/setup-lingeling.sh
    ./configure.sh
    make -C build -j$(nproc)
    sudo cp build/bin/{boolector,btor*} /usr/local/bin/
    sudo cp deps/btor2tools/build/bin/btorsim /usr/local/bin/

To use the ``btor`` engine you will need to install btor2tools from 
`commit c35cf1c <https://github.com/Boolector/btor2tools/commit/c35cf1c>`_ or
newer. 

Yices 2
-------

http://yices.csl.sri.com/

.. code-block:: text

   git clone https://github.com/SRI-CSL/yices2.git yices2
   cd yices2
   autoconf
   ./configure
   make -j$(nproc)
   sudo make install

Optional components
-------------------
Additional solver engines can be installed as per their instructions, links are
provided below.

Z3
^^^

  https://github.com/Z3Prover/z3

super_prove
^^^^^^^^^^^
  https://github.com/sterin/super-prove-build

Avy
^^^
  https://arieg.bitbucket.io/avy/

rIC3
^^^^
  https://github.com/gipsyh/rIC3/

The minimum required version is 1.3.5
