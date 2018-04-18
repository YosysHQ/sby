
SystemVerilog, VHDL, SVA
========================

Run ``verific -sv <files>`` in the ``[script]`` section of you ``.sby`` file
to read a SystemVerilog source file, and ``verific -vhdl <files>`` to read a
VHDL source file.

After all source files have been read, run ``verific -import <topmodule>``
to import the design elaborated at the specified top module.

Run ``yosys -h verific`` in a terminal window and enter for more information
on the ``verific`` script command.

Supported SVA Property Syntax
-----------------------------

SVA support in Yosys' Verific bindings is currently in development. At the time
of writing, the following subset of SVA property syntax is supported in
concurrent assertions, assumptions, and cover statements when using the
``verific`` command in Yosys to read the design.

High-Level Convenience Features
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Most of the high-level convenience features of the SVA language are supported,
such as

  * ``default clocking`` ... ``endclocking``
  * ``default disable iff`` ... ``;``
  * ``property`` ... ``endproperty``
  * ``sequence`` ... ``endsequence``
  * ``checker`` ... ``endchecker``
  * Arguments to sequences, properties, and checkers
  * Storing sequences, properties, and checkers in packages

In addition the SVA-specific features, the SystemVerilog ``bind`` statement and
deep hierarchical references are supported, simplifying the integration of
formal properties with the design under test.

The ``verific`` command also allows parsing of VHDL designs and supports binding
SystemVerilog modules to VHDL entities and deep hierarchical references from a
SystemVerilog formal test-bench into a VHDL design under test.

Expressions in Sequences
~~~~~~~~~~~~~~~~~~~~~~~~

Any standard Verilog boolean expression is supported, as well as the
SystemVerilog functions ``$past``, ``$stable``, ``$changed``, ``$rose``, and
``$fell``. This functions can also be used outside of SVA sequences.

Additionally the ``<sequence>.triggered`` syntax for checking if the end of
any given sequence matches the current cycle is supported in expressions.

Finally the usual SystemVerilog functions such as ``$countones``, ``$onehot``,
and ``$onehot0`` are also supported.

Sequences
~~~~~~~~~

Most importantly, expressions and variable-length concatenation are supported:

  * *expression*
  * *sequence* ``##N`` *sequence*
  * *sequence* ``##[*]`` *sequence*
  * *sequence* ``##[+]`` *sequence*
  * *sequence* ``##[N:M]`` *sequence*
  * *sequence* ``##[N:$]`` *sequence*

Also variable-length repetition:

  * *sequence* ``[*]``
  * *sequence* ``[+]``
  * *sequence* ``[*N]``
  * *sequence* ``[*N:M]``
  * *sequence* ``[*N:$]``

And the following more complex operators:

  * *sequence* ``or`` *sequence*
  * *sequence* ``and`` *sequence*
  * *expression* ``throughout`` *sequence*
  * *sequence* ``intersect`` *sequence*
  * *sequence* ``within`` *sequence*
  * ``first_match(`` *sequence* ``)``
  * *expression* ``[=N]``
  * *expression* ``[=N:M]``
  * *expression* ``[=N:$]``
  * *expression* ``[->N]``
  * *expression* ``[->N:M]``
  * *expression* ``[->N:$]``

Properties
~~~~~~~~~~

Currently only a certain set of patterns are supported for SVA properties:

  * [*antecedent_condition*] *sequence*
  * [*antecedent_condition*] ``not`` *sequence*
  * *antecedent_condition* *sequence* *until_condition*
  * *antecedent_condition* ``not`` *sequence* *until_condition*

Where *antecedent_condition* is one of:

  * sequence ``|->``
  * sequence ``|=>``

And *until_condition* is one of:

  * ``until`` *expression*
  * ``s_until`` *expression*
  * ``until_with`` *expression*
  * ``s_until_with`` *expression*

Clocking and Reset
~~~~~~~~~~~~~~~~~~

The following constructs are supported for clocking and reset in most of the
places the SystemVerilog standard permits them. However, properties spanning
multiple different clock domains are currently unsupported.

  * ``@(posedge`` *clock* ``)``
  * ``@(negedge`` *clock* ``)``
  * ``@(posedge`` *clock* ``iff`` *enable* ``)``
  * ``@(negedge`` *clock* ``iff`` *enable* ``)``
  * ``disable iff (`` *expression* ``)``

