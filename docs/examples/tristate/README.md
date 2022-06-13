# Tristate demo

Run 

    sby -f tristate.sby pass

to run the pass task. This uses the top module that exclusively enables each of the submodules.

Run 

    sby -f tristate.sby fail

to run the fail task. This uses the top module that allows submodule to independently enable its tristate outputs.
