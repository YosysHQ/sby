
Formal extensions to Verilog
============================

Any Verilog file may be read using ``read -formal <file>`` within the
SymbiYosys ``script`` section.  Multiple files may be given on the sames
line, or various files may be read in subsequent lines.

``read -formal`` will also define the ``FORMAL`` macro, which can be used
to separate a section having formal properties from the rest of the logic
within the core.

.. code-block:: systemverilog

   module somemodule(port1, port2, ...);
       // User logic here
       //
   `ifdef FORMAL
       // Formal properties here
   `endif
   endmodule

The ``bind()`` operator can also be used when using the Verific front end. This
will provide an option to attach formal properties to a given piece of logic,
without actually modifying the module in question to do so as we did in the
example above. Refer to :doc:`verific` for more on the Verific front end.

SystemVerilog Immediate Assertions
----------------------------------

SymbiYosys supports three basic immediate assertion types.

1. ``assume(<expr>);``

   An assumption restricts the possibilities the formal tool examines, making
   the search space smaller.  In any solver generated trace, all of the
   assumptions will always be true.

2. ``assert(<expr>);``

   An assertion is something the solver will try to make false.  Any time
   SymbiYosys is run with ``mode bmc``, the proof will fail if some set
   of inputs can cause the ``<expr>`` within the assertion to be zero (false).
   When SymbiYosys is run with ``mode prove``, the proof may also yield an
   ``UNKNOWN`` result if an assertion can be made to fail during the induction
   step.

3. ``cover(<expr>);``

   A cover statement only applies when SymbiYosys is ran with option
   ``mode cover``.  In this case, the formal solver will start at the
   beginning of time (i.e. when all initial statements are true), and it will
   try to find some clock when ``<expr>`` can be made to be true.  Such a
   cover run will "PASS" once all internal ``cover()`` statements have been
   fulfilled.  It will "FAIL" if any ``cover()`` statement exists that cannot
   be reached in the first ``N`` states, where ``N`` is set by the
   ``depth`` option.  A cover pass will also fail if an assertion needs to
   be broken in order to reach the covered state.

To be used, each of these statements needs to be placed into an *immediate*
context.  That is, it needs to be placed within an ``always`` block of some
type.  Two types of ``always`` block contexts are permitted:

- ``always @(*)``

  Formal properties within an ``always @(*)`` block will be checked on every
  time step.  For synchronous proofs, the property will be checked every
  clock period.  For asynchronous proofs, i.e. those with ``multiclock on``,
  the property will still be checked on every time step but, depending upon
  how you set up your time steps, it may also be checked multiple times
  per clock interval.

  As an example, consider the following assertion that the ``error_flag``
  signal must remain low.

.. code-block:: systemverilog

   always @(*)
       assert(!error_flag);

While it is not recommended that formal properties be mixed with logic in
the same ``always @(*)`` block, the language supports it.  In such cases,
the formal property will be evaluated as though it took place in the middle
of the logic block.

- ``always @(posedge <clock>)``

  The second form of immediate assertion is one within a clocked always block.
  This form of assertion is required when attempting to use the ``$past``,
  ``$stable``, ``$changed``, ``$rose``, or ``$fell`` SystemVerilog functions
  discussed in the next section.

  Unlike the ``@(*)`` assertion, this one will only be checked on the clock
  edge.  Depending upon how the clock is set up, that may mean that there are
  several formal time steps between when this assertion is checked.

  The two types of immediate assertions, both with and without a clock
  reference, are very similar.  There is one critical difference between
  them, however.  The clocked assertion will not be checked until the
  positive edge of the clock following the time period in question.  Within
  a synchronous design, this means that the fault will not lie on the last
  time step, but rather the time step prior.  New users often find this
  non-intuitive.

One subtlety to be aware of is that any ``always @(*)`` assertion that
depends upon an ``always @(posedge <clock>)`` assumption might fail before
the assumption is applied.  One solution is to use all clocked or all
combinatorial blocks.  Another solution is to move the assertion into an
``always @(posedge <clock>)`` block.

SystemVerilog Functions
-----------------------

Yosys supports five formal related functions: ``$past``, ``$stable``,
``$changed``, ``$rose``, and ``$fell``.  Internally, these are all implemented
in terms of the implementation of the ``$past`` operator.

The ``$past(<expr>)`` function returns the value of ``<expr>`` from one clock
ago.  It can only be used within a clocked always block, since the clock is
used to define "one clock ago."  It is roughly equivalent to,

.. code-block:: systemverilog

   reg past_value;
   always @(posedge clock)
       past_value <= expression;

There are two keys to the use of ``$past``.  The first is that
``$past(<expr>)`` can only be used within a clocked always block.  The second
is that there is no initial value given to any ``$past(<expr>)``.  That means
that on the first clock period of any design, ``$past(<expr>)`` will be
undefined.

Yosys supports both one and two arguments to ``$past``.  In the two argument
form, ``$past(<expr>,N)``, the expression returns the value of ``<expr>``
from ``N`` clocks ago.  ``N`` must be a synthesis time constant.

``$stable(<expr>)`` is short hand for ``<expr> == $past(<expr>)``.

``$changed(<expr>)`` is short hand for ``<expr> != $past(<expr>)``.

While the next two functions, ``$rose`` and ``$fell``, can be applied to
multi-bit expressions, only the least significant bits will be examined.
If we allow that ``<expr>`` has only a single bit within it, perhaps selected
from the least significant bit of a larger expression, then we can
express the following equivalencies.

``$rose(<expr>)`` is short hand for ``<expr> && !$past(<expr)``.

``$fell(<expr>)`` is short hand for ``!<expr> && $past(<expr)``.

Liveness and Fairness
---------------------

TBD

``assert property (eventually <expr>);``

``assume property (eventually <expr>);``

Unconstrained Variables
-----------------------

Yosys supports four attributes which can be used to create unconstrained
variables.  These attributes can be applied to the variable at declaration
time, as in

.. code-block:: systemverilog

   (* anyconst ) reg some_value;

The ``(* anyconst *)`` attribute will create a solver chosen constant.
It is often used when verifying memories: the proof allows the solver to
pick a constant address, and then proves that the value at that address
matches however the designer desires.

``(* anyseq *)`` differs from ``(* anyconst *)`` in that the solver chosen
value can change from one time step to the next.  In many ways, it is
similar to how the solver will treat an input to the design, with the
difference that an ``(* anyseq *)`` variable can originate internal
to the design.

Both ``(* anyseq *)`` and ``(* anyconst *)`` marked values can be constrained
with assumptions.

Yosys supports two other attributes useful to formal processing,
``(* allconst *)`` and ``(* allseq *)``.  These are very similar in their
functionality to the ``(* anyseq *)`` and ``(* anyconst *)`` attributes we
just discussed for creating unconstrained values.  Indeed, for both assertions
and cover statements, the two sets are identical.  Where they differ is
with respect to assumptions.  Assumed properties of an ``(* allseq *)``
or ``(* allconst *)`` value will be applied to all possible values of that
variable may take on.  This gets around the annoying reality associated with
defining a property using ``(* anyconst *)`` or ``(* anyseq *)`` only to
have the solver pick a value which wasn't the one that was constrained.

Global Clock
------------

Accessing the formal timestep becomes important when verifying code in any
asynchronous context.  In such asynchronous contexts, there may be multiple
independent clocks within the design.  Each of the clocks may be defined by
an assumption allowing the designer to carefully select the relationships
between them.

All of this requires the ``multiclock on`` line in the SBY options section.

It also requires the ``(* gclk *)`` attribute.

To use ``(* gclk *)``, define a register with that attribute, as in:

.. code-block:: systemverilog

    (* gclk *) reg formal_timestep;

You can then reference this ``formal_timestep`` in the clocking section
of an always block, as in,

.. code-block:: systemverilog

    always @(posedge formal_timestep)
        assume(incoming_clock == !$past(incoming_clock));

SystemVerilog Concurrent Assertions
-----------------------------------

TBD, see :ref:`sva`.

