A simple example for using abstractions
=======================================

Consider the design in `demo.v` and the properties in `props.sv`. Obviously the
properties are true, but that is hard to prove because it would take thousands of
cycles to get from the activation of one output signal to the next.

This can be solved by replacing counter with the abstraction in `abstr.sv`.

In order to do this we must first prove that the abstraction is correct. This is
done with `sby -f abstr.sby`.

Then we apply the abstriction by assuming what we have just proven and otherwise
turn `counter` into a cutpoint. See `props.sby` for details.

Running `sby -f props.sby prv` proves the properties and `sby -f props.sby cvr`
produces a cover trace that shows the abstraction in action.

Suggested exercises:

- Make modifications to `abstr.sv` and/or `demo.v`. Make a prediction if the
  change will make `sby -f abstr.sby` or `sby -f props.sby prv` fail and test your
  prediction.

- What happens if we remove `abstr.sv` from `props.sby`, but leave the `cutpoint`
  command in place?

- What happens if we remove the `cutpoint` command from `props.sby`, but leave
  `abstr.sv` in place?
