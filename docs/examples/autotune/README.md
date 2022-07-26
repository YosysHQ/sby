# Autotune demo

This directory contains a simple sequential integer divider circuit. The
verilog implementation in [divider.sv](divider.sv) comes with assertions that
this circuit will always produce the correct result and will always finish
within a fixed number of cycles. The circuit has the divider bit-width as
parameter.

Increasing the WIDTH parameter quickly turns proving those assertions into a
very difficult proof for fully autmated solvers. This makes it a good example
for the `--autotune` option which tries different backend engines to find the
best performing engine configuration for a given verification task.

The [divider.sby](divider.sby) file defines 3 tasks named `small`, `medium` and
`large` which configure the divider with different bit-widths. To verify the
`small` divider using the default engine run:

    sby -f divider.sby small

To automatically try different backend engines using autotune, run

    sby --autotune -f divider.sby small

The `small` task should finish quickly using both the default engine and using
autotune. The `medium` and `large` tasks take significantly longer and show
greater differences between engine configurations. Note that the `large` tasks
can take many minutes to hours, depending on the machine you are using.

You can learn more about Sby's autotune feature from [Sby's
documentation](https://symbiyosys.readthedocs.io/en/latest/autotune.html).
