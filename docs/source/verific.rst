
SystemVerilog, VHDL, SVA
========================

TBD

``verific -sv <files>``

``verific -vhdl <files>``

``verific -import <top>``

TBD

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
  * Parameters to sequences and properties
  * Storing sequences and properties in packages

In addition the SVA-specific fetures, the SystemVerilog ``bind`` statement and
deep hierarchical references are supported, simplifying the integration of
formal properties with the design under test.

The ``verific`` command also allows parsing of VHDL designs and supports binding
SystemVerilog modules to VHDL entities and deep hierarchical references from a
SystemVerilog formal test-bench into a VHDL design under test.

Expressions in Sequences
~~~~~~~~~~~~~~~~~~~~~~~~

Any standard Verilog boolean expression is supported, as well as the SystemVerilog
functions ``$past``, ``$stable``, ``$rose``, and ``$fell``. This functions can
also be used outside of SVA sequences.

Additionally the ``<sequence>.triggered`` syntax for checking if the end of
any given sequence matches the current cycle is supported everywhere in expressions
used in SVA sequences.

Sequences
~~~~~~~~~

The following sequence operators are currently supported. Note that some of
them only allow expressions in places where complete SVA would allow sequences
as well.

Most importantly, expressions and variable-length concatenation are supported:

  * *expression*
  * *sequence* ``##N`` *sequence*
  * *sequence* ``##[*]`` *sequence*
  * *sequence* ``##[+]`` *sequence*
  * *sequence* ``##[N:M]`` *sequence*
  * *sequence* ``##[N:$]`` *sequence*

Also variable-length repetition:

  * *expression* ``[*]``
  * *expression* ``[+]``
  * *expression* ``[*N]``
  * *expression* ``[*N:M]``
  * *expression* ``[*N:$]``

And some additional more complex operators:

  * *sequence* ``or`` *sequence*
  * *sequence* ``and`` *sequence*
  * *expression* ``throughout`` *sequence*

The following operators are currently **unsupported** but support for them is
planned for the near future:

  * ``first_match(`` *sequence* ``)``
  * *sequence* ``intersect`` *sequence*
  * *sequence* ``within`` *sequence*
  * *expression* [=N]
  * *expression* [=N:M]
  * *expression* [->N]
  * *expression* [->N:M]

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

The following cunstructs are supported for clocking in reset in most of the
places the SystemVerilog standard permits them, but properties spanning
multiple different clock domains are currently not supported.

  * ``@(posedge`` *clock* ``)``
  * ``@(negedge`` *clock* ``)``
  * ``@(posedge`` *clock* ``iff`` *enable* ``)``
  * ``@(negedge`` *clock* ``iff`` *enable* ``)``
  * ``disable iff (`` *expression* ``)``

