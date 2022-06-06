
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
