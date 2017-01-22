
Getting Started
===============

Installing
----------

TBD

Until I find the time to write this section this links must be sufficient:

  * Yosys: http://www.clifford.at/yosys/
  * SymbiYosys: https://github.com/cliffordwolf/SymbiYosys
  * Z3: https://github.com/Z3Prover/z3
  * Yices2: http://yices.csl.sri.com/
  * Boolector: http://fmv.jku.at/boolector/
  * super_prove: http://downloads.bvsrc.org/super_prove/

(Yosys, SymbiYosys, and Z3 are non-optional. The other packages are only
required for some engine configurations.)

First step: A simple BMC example
--------------------------------

Here is a simple example design with a safety property (assertion).

.. code-block:: systemverilog

   module demo (

     input clk,
     output [5:0] counter
   );
     reg [5:0] counter = 0;

     always @(posedge clk) begin
       if (counter == 15)
         counter <= 0;
       else
         counter <= counter + 1;
     end

     assert property (counter < 32);
   endmodule

The property in this example is true. We'd like to verify this using a bounded
model check (BMC) that is 100 cycles deep.

SymbiYosys is controlled by ``.sby`` files. The following file can be used to
configure SymbiYosys to run a BMC for 100 cycles on the design:

.. code-block:: text

   [options]
   mode bmc
   depth 100

   [engines]
   smtbmc

   [script]
   read_verilog -formal demo.v
   prep -top demo

   [files]
   demo.v

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
the modified design and see if the proof now fails.

Going beyond bounded model checks
---------------------------------

TBD


