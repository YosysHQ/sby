
Getting started
===============

.. note:: This tutorial assumes sby installation as per the :ref:`install-doc`. 
    It is also recommended to install 
    `GTKWave <http://gtkwave.sourceforge.net/>`_, an open source VCD viewer.

First In, First Out (FIFO) buffer
********************************

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
providing a circular queue.
