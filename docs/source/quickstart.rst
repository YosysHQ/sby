
Getting Started
===============

The example files used in this chapter can be downloaded from `here
<https://github.com/cliffordwolf/SymbiYosys/tree/master/docs/examples/quickstart>`_.

Installing
----------

Follow the instructions below to install SymbiYosys and its dependencies.
Yosys, SymbiYosys, and Z3 are non-optional. The other packages are only
required for some engine configurations.

Prerequisites
~~~~~~~~~~~~~

Installing prerequisites (this command is for Ubuntu 16.04):

.. code-block:: text

   sudo apt-get install build-essential clang bison flex libreadline-dev \
                        gawk tcl-dev libffi-dev git mercurial graphviz   \
                        xdot pkg-config python python3 libftdi-dev

Yosys, Yosys-SMTBMC and ABC
~~~~~~~~~~~~~~~~~~~~~~~~~~~

http://www.clifford.at/yosys/

https://people.eecs.berkeley.edu/~alanmi/abc/

Next install Yosys, Yosys-SMTBMC and ABC (``yosys-abc``):

.. code-block:: text

   git clone https://github.com/cliffordwolf/yosys.git yosys
   cd yosys
   make -j$(nproc)
   sudo make install

SymbiYosys
~~~~~~~~~~

https://github.com/cliffordwolf/SymbiYosys

.. code-block:: text

   git clone https://github.com/cliffordwolf/SymbiYosys.git SymbiYosys
   cd SymbiYosys
   sudo make install

Yices 2
~~~~~~~

http://yices.csl.sri.com/

.. code-block:: text

   git clone https://github.com/SRI-CSL/yices2.git yices2
   cd yices2
   autoconf
   ./configure
   make -j$(nproc)
   sudo make install

Z3
~~

https://github.com/Z3Prover/z3/wiki

.. code-block:: text

   git clone https://github.com/Z3Prover/z3.git z3
   cd z3
   python scripts/mk_make.py
   cd build
   make -j$(nproc)
   sudo make install

super_prove
~~~~~~~~~~~

https://bitbucket.org/sterin/super_prove_build

Download the right binary .tar.gz for your system from http://downloads.bvsrc.org/super_prove/
and extract it to ``/usr/local/super_prove``.

Then create a wrapper script ``/usr/local/bin/suprove`` with the following contents:

.. code-block:: text

   #!/bin/bash
   tool=super_prove; if [ "$1" != "${1#+}" ]; then tool="${1#+}"; shift; fi
   exec /usr/local/super_prove/bin/${tool}.sh "$@"

Avy
~~~

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
~~~~~~~~~

http://fmv.jku.at/boolector/

.. code-block:: text

   wget http://fmv.jku.at/boolector/boolector-2.4.1-with-lingeling-bbc.tar.bz2
   tar xvjf boolector-2.4.1-with-lingeling-bbc.tar.bz2
   cd boolector-2.4.1-with-lingeling-bbc/
   make
   sudo cp boolector/bin/boolector /usr/local/bin/boolector

Other packages
~~~~~~~~~~~~~~

Until I find the time to write install guides for the following packages, this
links must suffice:

  * AIGER: http://fmv.jku.at/aiger/

First step: A simple BMC example
--------------------------------

Here is a simple example design with a safety property (assertion).

.. literalinclude:: ../examples/quickstart/demo.v
   :language: systemverilog

The property in this example is true. We'd like to verify this using a bounded
model check (BMC) that is 100 cycles deep.

SymbiYosys is controlled by ``.sby`` files. The following file can be used to
configure SymbiYosys to run a BMC for 100 cycles on the design:

.. literalinclude:: ../examples/quickstart/demo.sby
   :language: text

Simply create a text file ``demo.v`` with the example design and another text
file ``demo.sby`` with the SymbiYosys configuration. Then run::

   sby demo.sby

This will run a bounded model check for 100 cycles. The last few lines of the
output should look something like this:

.. code-block:: text

   SBY [demo] engine_0: ##      0   0:00:00  Checking asserts in step 96..
   SBY [demo] engine_0: ##      0   0:00:00  Checking asserts in step 97..
   SBY [demo] engine_0: ##      0   0:00:00  Checking asserts in step 98..
   SBY [demo] engine_0: ##      0   0:00:00  Checking asserts in step 99..
   SBY [demo] engine_0: ##      0   0:00:00  Status: PASSED
   SBY [demo] engine_0: Status returned by engine: PASS
   SBY [demo] engine_0: finished (returncode=0)
   SBY [demo] summary: Elapsed clock time [H:MM:SS (secs)]: 0:00:00 (0)
   SBY [demo] summary: Elapsed process time [H:MM:SS (secs)]: 0:00:00 (0)
   SBY [demo] summary: engine_0 (smtbmc) returned PASS
   SBY [demo] DONE (PASS)

This will also create a ``demo/`` directory tree with all relevant information,
such as a copy of the design source, various log files, and trace data in case
the proof fails.

(Use ``sby -f demo.sby`` to re-run the proof. Without ``-f`` the command will
fail because the output directory ``demo/`` already exists.)

Time for a simple exercise: Modify the design so that the property is false
and the offending state is reachable within 100 cycles. Re-run ``sby`` with
the modified design and see if the proof now fails. Inspect the counterexample
trace (``.vcd`` file) produced by ``sby``. (`GTKWave <http://gtkwave.sourceforge.net/>`_
is an open source VCD viewer that you can use.)

Selecting the right engine
--------------------------

The ``.sby`` file for a project selects one or more engines. (When multiple
engines are selected, all engines are executed in parallel and the result
returned by the first engine to finish is the result returned by SymbiYosys.)

Each engine has its strengths and weaknesses. Therefore it is important to
select the right engine for each project. The documentation for the individual
engines can provide some guidance for engine selection. (Trial and error can
also be a useful method for evaluating engines.)

Let's consider the following example:

.. literalinclude:: ../examples/quickstart/memory.v
   :language: systemverilog

This example is expected to fail verification (see the BUG comment).
The following ``.sby`` file can be used to show this:

.. literalinclude:: ../examples/quickstart/memory.sby
   :language: text

This project uses the ``smtbmc`` engine, which uses SMT solvers to perform the
proof. This engine uses the array-theories provided by those solvers to
efficiently model memories. Since this example uses large memories, the
``smtbmc`` engine is a good match.

(``smtbmc boolector`` uses boolector as SMT solver. Note that boolector is
only free-to-use for noncommercial purposes. Use ``smtbmc z3`` to use the
permissively licensed solver Z3, or use ``smtbmc yices`` to use the
copyleft licensed solver Yices 2 intead. Yices 2 is the default solver when
no argument is used with ``smtbmc``.)

Exercise: The engine ``abc bmc3`` does not provide abstract memory models.
Therefore SymbiYosys has to synthesize the memories in the example to FFs
and address logic. How does the performance of this project change if
``abc bmc3`` is used as engine instead of ``smtbmc boolector``? How fast
can either engine verify the design when the bug has been fixed?

Beyond bounded model checks
---------------------------

Bounded model checks only prove that the safety properties hold for the first
*N* cycles (where *N* is the depth of the BMC). Sometimes this is insufficient
and we need to prove that the safety properties hold forever, not just the first
*N* cycles. Let us consider the following example:

.. literalinclude:: ../examples/quickstart/prove.v
   :language: systemverilog

Proving this design in an unbounded manner can be achieved using the following
SymbiYosys configuration file:

.. literalinclude:: ../examples/quickstart/prove.sby
   :language: text

Note that ``mode`` is now set to ``prove`` instead of ``bmc``. The ``smtbmc``
engine in ``prove`` mode will perform a k-induction proof. Other engines can
use other methods, e.g. using ``abc pdr`` will prove the design using the IC3
algorithm.

