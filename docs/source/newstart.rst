
Getting started
===============

.. note:: This tutorial assumes sby installation as per the :ref:`install-doc`. 
    It is also recommended to install 
    `GTKWave <http://gtkwave.sourceforge.net/>`_, an open source VCD viewer.

First In, First Out (FIFO) buffer
*********************************

From `Wikipedia <https://en.wikipedia.org/wiki/FIFO_(computing_and_electronics)>`_,
a FIFO is 
    
    a method for organizing the manipulation of a data structure (often,
    specifically a data buffer) where the oldest (first) entry, or "head" of the
    queue, is processed first.

    Such processing is analogous to servicing people in a queue area on a
    first-come, first-served (FCFS) basis, i.e. in the same sequence in which
    they arrive at the queue's tail. 

In hardware we can create such a construct by providing two addresses into a
register file.  See the Verilog code below for the two main modules of an
example implementation.

.. literalinclude:: ../examples/fifo/fifo.sv
   :language: systemverilog

Notice that this register design includes a synchronous write and asynchronous
read.  Each word is 8 bits, and up to 16 words can be stored in the buffer.  The
address generator module will be instantiated twice; once for the write address
and once for the read address.  In both cases, the address will start at and
reset to 0, and will increment by 1 when an enable signal is received.  When the
address pointers increment from the maximum storage value they reset back to 0,
providing a circular queue.  The top level design implemented, can be found in
``top.sv``.  

Verification properties
***********************

In order to verify our design we must first define properties that it must
satisfy.  For example, there must never be a negative number of values in the
FIFO.  Similarly, there must never be more than there is memory available.  By
assigning a signal to count the number of values in the buffer, we can make the
following assertions in the code:

.. code-block:: systemverilog

    a_uflow:  assert (count >= 0);
    a_oflow:  assert (count <= MAX_DATA);

It is also possible to use the prior value of a signal for comparison.  This can
be used, for example, to ensure that the count is only able to increase or
decrease by 1.  A case must be added to handle resetting the count directly to
0, as well as if the count does not change.  This can be seen in the following
code; at least one of these conditions must be true at all times if our design
is to be correct.

.. code-block:: systemverilog

    a_counts: assert (count == 0
                   || count == $past(count)
                   || count == $past(count) + 1
                   || count == $past(count) - 1);

As our count signal is used independently of the read and write pointers, we
must verify that the count is always correct.  While the write pointer will
always be at the same point or *after* the read pointer, the circular buffer
means that the write *address* could wrap around and appear *less than* the read
address.  So we must first perform some simple arithmetic to find the absolute
difference in addresses, and then compare with the count signal.

.. code-block:: systemverilog

    assign addr_diff = waddr >= raddr 
                     ? waddr - raddr 
                     : waddr + MAX_DATA - raddr;
                     
    a_count_diff: assert  (count == addr_diff 
                        || count == MAX_DATA && addr_diff == 0);

SymbiYosys
**********

SymbiYosys (sby) uses a .sby file to define a set of tasks used for
verification.  

**prove_oss**
    Prove mode (unbounded model check), for use with OSS CAD Suite.

**noskip**
    Demonstration of failing model check with OSS CAD Suite.

**cover_oss**
    Cover mode (testing cover statements), for use with OSS CAD Suite.

**prove_tabby**
    Prove mode, for use with Tabby CAD Suite.

**cover_tabby**
    Cover mode, for use with Tabby CAD Suite.

The use of the ``:default`` tag indicates that by default, prove_oss and
cover_oss should be run if no tasks are specified, such as when running the
command below.

    sby fifo.sby

.. note:: The default set of tests should all pass.  If this is not the case 
    there may be a problem with the installation of sby or one of its solvers. 

To see what happens when a test fails, the below command can be used.  Note the
use of the ``-f`` flag to automatically overwrite existing task output.  While
this may not be necessary on the first run, it is quite useful when making
adjustments to code and rerunning tests to validate.
    
    sby -f fifo.sby noskip

The noskip task disables the code shown below.  Because the count signal has
been written such that it cannot exceed MAX_DATA, removing this code will lead
to the ``a_count_diff`` assertion failing.  Without this assertion, there is no
guarantee that data will be read in the same order it was written should an
overflow occur and the oldest data be written.

.. code-block:: systemverilog

    `ifndef NOSKIP
        // write while full => overwrite oldest data, move read pointer
        assign rskip = wen && !ren && data_count >= MAX_DATA;
        // read while empty => read invalid data, keep write pointer in sync
        assign wskip = ren && !wen && data_count == 0;
    `endif // NOSKIP

The last few lines of output for the noskip task should be similar to the
following:

.. code-block:: text

    SBY [fifo_noskip] engine_0: ##   0:00:00  BMC failed!
    SBY [fifo_noskip] engine_0: ##   0:00:00  Assert failed in fifo: a_count_diff
    SBY [fifo_noskip] engine_0: ##   0:00:00  Writing trace to VCD file: engine_0/trace.vcd
    SBY [fifo_noskip] engine_0: ##   0:00:00  Writing trace to Verilog testbench: engine_0/trace_tb.v
    SBY [fifo_noskip] engine_0: ##   0:00:00  Writing trace to constraints file: engine_0/trace.smtc
    SBY [fifo_noskip] engine_0: ##   0:00:00  Status: FAILED
    SBY [fifo_noskip] engine_0: finished (returncode=1)
    SBY [fifo_noskip] summary: Elapsed clock time [H:MM:SS (secs)]: 0:00:01 (1)
    SBY [fifo_noskip] summary: Elapsed process time unvailable on Windows
    SBY [fifo_noskip] summary: engine_0 (abc pdr) returned FAIL
    SBY [fifo_noskip] summary: counterexample trace: fifo_noskip/engine_0/trace.vcd
    SBY [fifo_noskip] DONE (FAIL, rc=2)
    SBY The following tasks failed: ['noskip']

Using the ``noskip.gtkw`` file provided, use the below command to examine the
error trace.

    gtkwave fifo_noskip/engine_0/trace.vcd noskip.gtkw

This should result in something similar to the below image.  We can immediately
see that ``data_count`` and ``addr_diff`` are different.  Looking a bit deeper
we can see that in order to reach this state the read enable signal was high in
the first clock cycle while write enable is low.  This leads to an underfill
where a value is read while the buffer is empty and the read address increments
to a higher value than the write address.

.. image:: media/gtkwave_noskip.png

During correct operation, the ``w_underfill`` witness will cover the underflow
case.  Examining ``fifo_cover_oss/logfile.txt`` will reveal which trace file
includes the witness we are looking for.  If this file doesn't exist, run the
code below.

    sby fifo.sby fifo_cover_oss

Searching the file for ``w_underfill`` will reveal the below.

.. code-block:: text

    $ grep "w_underfill" fifo_cover_oss/logfile.txt -A 1
    SBY [fifo_cover_oss] engine_0: ##   0:00:00  Reached cover statement at w_underfill in step 2.
    SBY [fifo_cover_oss] engine_0: ##   0:00:00  Writing trace to VCD file: engine_0/trace2.vcd

We can then run gtkwave with the trace file indicated to see the correct
operation as in the image below.  When the buffer is empty, a read with no write
will result in the ``wksip`` signal going high, incrementing *both* read and
write addresses and avoiding underflow.
    
    gtkwave fifo_cover_oss/engine_0/trace2.vcd noskip.gtkw

.. image:: media/gtkwave_coverskip.png

For more on using the .sby file, see the :ref:`.sby reference page <Reference for .sby file format>`.

Concurrent assertions
*********************

Until this point, all of the properties described have been *immediate*
assertions.  As the name suggests, immediate assertions are evaluated
immediately whereas concurrent assertions allow for the capture of sequences of
events which occur across time.  The use of concurrent assertions requires a
more advanced parser, such as Verific.  Verific is included for use in the
*Tabby CAD Suite*.  

With concurrent assertions we are able to verify more fully that our enables and
status flags work as desired.  For example, we can assert that if the read
enable signal is high then the address of the read pointer *must* change.
Because of our earlier *immediate* assertions that the pointer address can only
increment or remain the same we do not need to specify that here.  We can also
assert that if the enable is low, and the buffer is not full and potentially
requires a skip in the read address, then the read address will *not* change.

.. code-block:: systemverilog

    ap_raddr2: assert property (ren |=> $changed(raddr));
    ap_raddr3: assert property (!ren && !full  |=> $stable(raddr));


Further information
*******************
For more information on the uses of assertions and the difference between
immediate and concurrent assertions, refer to appnote 109: Property Checking
with SystemVerilog Assertions.
