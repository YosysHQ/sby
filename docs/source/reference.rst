
Reference for .sby file format
==============================

A ``.sby`` file consists of sections. Each section start with a single-line
section header in square brackets. The order of sections in a ``.sby`` file
is for the most part irrelevant, but by convention the usual order is
``[tasks]``, ``[options]``, ``[engines]``, ``[script]``,  and ``[files]``.

Tasks section
-------------

The optional ``[tasks]`` section can be used to configure multiple verification tasks in
a single ``.sby`` file. Each line in the ``[tasks]`` section configures one task. For example:

.. code-block:: text

   [tasks]
   task1 task_1_or_2 task_1_or_3
   task2 task_1_or_2
   task3 task_1_or_3

Each task can be assigned additional group aliases, such as ``task_1_or_2``
and ``task_1_or_3`` in the above example.

One or more tasks can be specified as additional command line arguments when
calling ``sby`` on a ``.sby`` file:

.. code-block:: text

   sby example.sby task2

If no task is specified then all tasks in the ``[tasks]`` section are run.

After the ``[tasks]`` section individual lines can be specified for specific
tasks or task groups:

.. code-block:: text

   [options]
   task_1_or_2: mode bmc
   task_1_or_2: depth 100
   task3: mode prove

If the tag ``<taskname>:`` is used on a line by itself then the conditional string
extends until the next conditional block or ``--`` on a line by itself.

.. code-block:: text

   [options]
   task_1_or_2:
   mode bmc
   depth 100

   task3:
   mode prove
   --

The tag ``~<taskname>:`` can be used for a line or block that should not be used when
the given task is active:

.. code-block:: text

   [options]
   ~task3:
   mode bmc
   depth 100

   task3:
   mode prove
   --

The following example demonstrates how to configure safety and liveness checks for all
combinations of some host implementations A and B and device implementations X and Y:

.. code-block:: text

   [tasks]
   prove_hAdX prove hostA deviceX
   prove_hBdX prove hostB deviceX
   prove_hAdY prove hostA deviceY
   prove_hBdY prove hostB deviceY
   live_hAdX live hostA deviceX
   live_hBdX live hostB deviceX
   live_hAdY live hostA deviceY
   live_hBdY live hostB deviceY


   [options]
   prove: mode prove
   live: mode live

   [engines]
   prove: abc pdr
   live: aiger suprove

   [script]
   hostA: read_verilog hostA.v
   hostB: read_verilog hostB.v
   deviceX: read_verilog deviceX.v
   deviceY: read_verilog deviceY.v
   ...

The ``[tasks]`` section must appear in the ``.sby`` file before the first
``<taskname>:`` or ``~<taskname>:`` tag.

Options section
---------------

The ``[options]`` section contains lines with key-value pairs. The ``mode``
option is mandatory. The possible values for the ``mode`` option are:

========= ===========
Mode      Description
========= ===========
``bmc``   Bounded model check to verify safety properties (``assert(...)`` statements)
``prove`` Unbounded model check to verify safety properties (``assert(...)`` statements)
``live``  Unbounded model check to verify liveness properties (``assert(s_eventually ...)`` statements)
``cover`` Generate set of shortest traces required to reach all cover() statements
``equiv`` Formal equivalence checking (usually to verify pre- and post-synthesis equivalence)
``synth`` Reactive Synthesis (synthesis of circuit from safety properties)
========= ===========

All other options have default values and thus are optional. The available
options are:

+------------------+------------+---------------------------------------------------------+
|   Option         |   Modes    | Description                                             |
+==================+============+=========================================================+
| ``expect``       |   All      | Expected result as comma-separated list of the tokens   |
|                  |            | ``pass``, ``fail``, ``unknown``, ``error``, and         |
|                  |            | ``timeout``. Unexpected results yield a nonzero return  |
|                  |            | code . Default: ``pass``                                |
+------------------+------------+---------------------------------------------------------+
| ``timeout``      |   All      | Timeout in seconds. Default: ``none`` (i.e. no timeout) |
+------------------+------------+---------------------------------------------------------+
| ``multiclock``   |   All      | Create a model with multiple clocks and/or asynchronous |
|                  |            | logic. Values: ``on``, ``off``. Default: ``off``        |
+------------------+------------+---------------------------------------------------------+
| ``wait``         |   All      | Instead of terminating when the first engine returns,   |
|                  |            | wait for all engines to return and check for            |
|                  |            | consistency. Values: ``on``, ``off``. Default: ``off``  |
+------------------+------------+---------------------------------------------------------+
| ``aigsmt``       |   All      | Which SMT2 solver to use for converting AIGER witnesses |
|                  |            | to counter example traces. Use ``none`` to disable      |
|                  |            | conversion of AIGER witnesses. Default: ``yices``       |
+------------------+------------+---------------------------------------------------------+
| ``tbtop``        |   All      | The top module for generated Verilog test benches, as   |
|                  |            | hierarchical path relative to the design top module.    |
+------------------+------------+---------------------------------------------------------+
| ``smtc``         | ``bmc``,   | Pass this ``.smtc`` file to the smtbmc engine. All      |
|                  | ``prove``, | other engines are disabled when this option is used.    |
|                  | ``cover``  | Default: None                                           |
+------------------+------------+---------------------------------------------------------+
| ``depth``        | ``bmc``,   | Depth of the bounded model check. Only the specified    |
|                  | ``cover``  | number of cycles are considered. Default: ``20``        |
|                  +------------+---------------------------------------------------------+
|                  | ``prove``  | Depth for the k-induction performed by the ``smtbmc``   |
|                  |            | engine. Other engines ignore this option in ``prove``   |
|                  |            | mode. Default: ``20``                                   |
+------------------+------------+---------------------------------------------------------+
| ``append``       | ``bmc``,   | When generating a counter-example trace, add the        |
|                  | ``prove``, | specified number of cycles at the end of the trace.     |
|                  | ``cover``  | Default: ``0``                                          |
+------------------+------------+---------------------------------------------------------+

Engines section
---------------

The ``[engines]`` section configures which engines should be used to solve the
given problem. Each line in the ``[engines]`` section specifies one engine. When
more than one engine is specified then the result returned by the first engine
to finish is used.

Each engine configuration consists of an engine name followed by engine options,
usually followed by a solver name and solver options.

Example:

.. code-block:: text

   [engines]
   smtbmc --syn --nopresat z3 rewriter.cache_all=true opt.enable_sat=true
   abc sim3 -W 15

In the first line ``smtbmc`` is the engine, ``--syn --nopresat`` are engine options,
``z3`` is the solver, and ``rewriter.cache_all=true opt.enable_sat=true`` are
solver options.

In the 2nd line ``abc`` is the engine, there are no engine options, ``sim3`` is the
solver, and ``-W 15`` are solver options.

``smtbmc`` engine
~~~~~~~~~~~~~~~~~

The ``smtbmc`` engine supports the ``bmc``, ``prove``, and ``cover`` modes and supports
the following options:

+-----------------+---------------------------------------------------------+
|   Option        | Description                                             |
+=================+=========================================================+
| ``--nomem``     | Don't use the SMT theory of arrays to model memories.   |
|                 | Instead synthesize memories to registers and address    |
|                 | logic.                                                  |
+-----------------+---------------------------------------------------------+
| ``--syn``       | Synthesize the circuit to a gate-level representation   |
|                 | instead of using word-level SMT operators. This also    |
|                 | runs some low-level logic optimization on the circuit.  |
+-----------------+---------------------------------------------------------+
| ``--stbv``      | Use large bit vectors (instead of uninterpreted         |
|                 | functions) to represent the circuit state.              |
+-----------------+---------------------------------------------------------+
| ``--stdt``      | Use SMT-LIB 2.6 datatypes to represent states.          |
+-----------------+---------------------------------------------------------+
| ``--nopresat``  | Do not run "presat" SMT queries that make sure that     |
|                 | assumptions are non-conflicting (and potentially        |
|                 | warmup the SMT solver).                                 |
+-----------------+---------------------------------------------------------+
| ``--unroll``,   | Disable/enable unrolling of the SMT problem. The        |
| ``--nounroll``  | default value depends on the solver being used.         |
+-----------------+---------------------------------------------------------+
| ``--dumpsmt2``  | Write the SMT2 trace to an additional output file.      |
|                 | (Useful for benchmarking and troubleshooting.)          |
+-----------------+---------------------------------------------------------+
| ``--progress``  | Enable Yosys-SMTBMC timer display.                      |
+-----------------+---------------------------------------------------------+

Any SMT2 solver that is compatible with ``yosys-smtbmc`` can be passed as
argument to the ``smtbmc`` engine. The solver options are passed to the solver
as additional command line options.

The following solvers are currently supported by ``yosys-smtbmc``:

  * yices
  * boolector
  * z3
  * mathsat
  * cvc4

``aiger`` engine
~~~~~~~~~~~~~~~~

The ``aiger`` engine is a generic front-end for hardware modelcheckers that are capable
of processing AIGER files. The engine supports no engine options and supports the following
solvers:

+-------------------------------+---------------------------------+
|   Solver                      |   Modes                         |
+===============================+=================================+
| ``suprove``                   |   ``prove``, ``live``           |
+-------------------------------+---------------------------------+
| ``avy``                       |   ``prove``                     |
+-------------------------------+---------------------------------+
| ``aigbmc``                    |   ``prove``, ``live``           |
+-------------------------------+---------------------------------+

Solver options are passed to the solver as additional command line options.

``abc`` engine
~~~~~~~~~~~~~~

The ``abc`` engine is a front-end for the functionality in Berkeley ABC. It
currently supports no engine options and supports the following
solvers:

+------------+-----------------+---------------------------------+
|   Solver   |   Modes         |   ABC Command                   |
+============+=================+=================================+
| ``bmc3``   |  ``bmc``        |  ``bmc3 -F <depth> -v``         |
+------------+-----------------+---------------------------------+
| ``sim3``   |  ``bmc``        |  ``sim3 -F <depth> -v``         |
+------------+-----------------+---------------------------------+
| ``pdr``    |  ``prove``      |  ``pdr``                        |
+------------+-----------------+---------------------------------+

Solver options are passed as additional arguments to the ABC command
implementing the solver.

Script section
--------------

TBD

Files section
-------------

The files section lists the source files for the proof. ``sby`` copies
these files to ``<outdir>/src/`` before running the Yosys script.

For example:

.. code-block:: text

   [engines]
   top.sv
   ../common/defines.vh
   /data/prj42/modules/foobar.sv

Will copy these files as ``top.v``, ``defines.vh``, and ``foobar.sv``
to ``<outdir>/src/``.

If the name of the file in ``<outdir>/src/`` should be different from the
basename of the specified file, then the new file name can be specified before
the source file name. For example:

.. code-block:: text

   [engines]
   top.sv
   defines.vh ../common/defines_footest.vh
   /data/prj42/modules/foobar.sv

File sections
-------------

File sections can be used to create additional files in ``<outdir>/src/`` from
the literal content of the ``[file <filename>]`` section ("here document"). For
example:

.. code-block:: text

   [file params.vh]
   `define RESET_LEN 42
   `define FAULT_CYCLE 57

Pycode blocks
-------------

TBD
