A simple example for using abstractions
=======================================

Abstractions are a way to deal with formal properties that are difficult to
prove directly because they require the design to pass through many intermediate
stages to observe the behavior in question. An abstraction can elide the
irrelevant steps and boil the behavior down to the steps important to the proof.

Instead of directly proving that the properties are satisfied by the design,
abstractions can be used to prove in a two-step process
 1. that the abstraction correctly models the design's behavior
    ("the design does X")
 2. that the properties are satisfied by the abstraction's behavior
    ("anything that does X will do Y").
From this, we can deduce by simple syllogism that the design must satisfy the
properties ("the design does Y").

A simple example is the design in `demo.v`. It defines a module containing a
20-bit counter, which has four outputs A, B, C, D that indicate when the counter
value happens to be one of four specific numbers (123456, 234567, 345678, 456789).

`props.sv` defines some properties about the outputs A, B, C, D and binds them
to the module. These properties assert that the counter values are reached in
order. For example, the first assertion describes that when output A is active
(i.e. the counter value is 123456), the outputs B, C, and D are not (the counter
value is not 234567, 345678, or 456789), and they will remain inactive for an
unspecified number of cycles, followed by B becoming active (counter reaches
234567). The cover property checks that it is possible for the module to pass
through the four values A, B, C, D and then return to A at least once.

However, it would be infeasible to prove these properties directly: because the
counter counts up one by one, it would take thousands of steps to pass from one
output activation to the next, and over a million steps to reach the sequence in
the cover property.

Introducing an abstraction is a way to get around this limitation. The
abstraction in `abstr.sv` describes only the aspects of the counter's behavior
that are relevant to the problem at hand:
 - its value strictly increases except at reset and when overflowing from
 2**20-1 to 0
 - a counter value strictly smaller than one of the four values of interest is
 always followed by either another value strictly smaller, or the value of
 interest itself.

In a first step, the test in `abstr.sby` proves (asserts) that the properties
in the abstraction apply to the counter module. To do this, the macro
`` `demo_counter_abstr_mode`` in `abstr.sv` is defined to mean `assert` when
reading the file. Run it with the command `sby -f abstr.sby`; if it returns
`PASS`, you have proved that the abstraction correctly models the counter.

In a second step, for the test in `props.sby` the actual counter implementation
is removed from the design using the `cutpoint demo/counter` command. This
command disconnects the net carrying the counter value from the logic driving
it and instead replaces it with an `$anyseq` cell - meaning that the solver is
free to chose any new counter value that suits it every time step (cycle). The
counter value is restricted only by the properties in the abstraction - which
this time are assumed by defining `` `demo_counter_abstr_mode`` as `assume` when
reading `abstr.sby`.

Concretely, this means that instead of having to use 123456 time steps to
consider each individual value that the counter will hold between reset and A
becoming active, the solver can consider all 123456 values until the activation
of A simultaneously, in a single time step.

You can see this in the cover trace produced for the cover property. After
running `sby -f props.sby`, open the file `props_cvr/engine_0/trace0.vcd` in a
waveform viewer such as `gtkwave`. You will find that the counter value jumps
immediately from one value of interest to the next - the solver actually
considers all the other possible values inbetween as well, but picks the one
that leads to the most useful behavior in the next time step, which is in this
case always the highest value permitted by the constraints of the abstraction.

Suggested exercises:

- Make modifications to `abstr.sv` and/or `demo.v`. Make a prediction if the
  change will make `sby -f abstr.sby` or `sby -f props.sby prv` fail and test your
  prediction.

- What happens if we remove `abstr.sv` from `props.sby`, but leave the `cutpoint`
  command in place?

- What happens if we remove the `cutpoint` command from `props.sby`, but leave
  `abstr.sv` in place?
