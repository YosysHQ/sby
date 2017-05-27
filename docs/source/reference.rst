
Reference for .sby file format
==============================

A ``.sby`` file consists of sections. Each section start with a single-line
section header in square brackets. The order of sections in a ``.sby`` file
is irrelevant, but by convention the usual order is ``[options]``,
``[engines]``, ``[script]``, and ``[files]``.

Options section
---------------

The ``[options]`` section contains lines with key-value pairs. The ``mode``
option is mandatory. The possible values for the ``mode`` option are:

========= ===========
Mode      Description
========= ===========
``bmc``   Bounded model check to verify safety properties (``assert(...)`` statements)
``prove`` Unbounded model check to verify safety properties (``assert(...)`` statements)
``live``  Unbounded model check to verify liveness properties (``assert(s_eventually ...)`` statements)
``cover`` Generate set of shortest traces required to reach all cover() statements
========= ===========

All other options have default values and thus are optional. The available
options are:

+-------------+------------+---------------------------------------------------------+
|   Option    |   Modes    | Description                                             |
+=============+============+=========================================================+
| ``expect``  |   All      | Expected result as comma-separated list of the tokens   |
|             |            | ``pass``, ``fail``, ``unknown``, ``error``, and         |
|             |            | ``timeout``. Unexpected results yield a nonzero return  |
|             |            | code . Default: ``pass``                                |
+-------------+------------+---------------------------------------------------------+
| ``timeout`` |   All      | Timeout in seconds. Default: ``none`` (i.e. no timeout) |
+-------------+------------+---------------------------------------------------------+
| ``wait``    |   All      | Instead of terminating when the first engine returns,   |
|             |            | wait for all engines to return and check for            |
|             |            | consistency. Values: ``on``, ``off``. Default: ``off``  |
+-------------+------------+---------------------------------------------------------+
| ``aigsmt``  |   All      | Which SMT2 solver to use for converting AIGER witnesses |
|             |            | to counter example traces. Default: ``yices``           |
+-------------+------------+---------------------------------------------------------+
| ``smtc``    | ``bmc``,   | Pass this ``.smtc`` file to the smtbmc engine. All      |
|             | ``prove``, | other engines are disabled when this option is used.    |
|             | ``cover``  | Default: None                                           |
+-------------+------------+---------------------------------------------------------+
| ``depth``   | ``bmc``,   | Depth of the bounded model check. Only the specified    |
|             | ``cover``  | number of cycles are considered. Default: ``20``        |
|             +------------+---------------------------------------------------------+
|             | ``prove``  | Depth for the k-induction performed by the ``smtbmc``   |
|             |            | engine. Other engines ignore this option in ``prove``   |
|             |            | mode. Default: ``20``                                   |
+-------------+------------+---------------------------------------------------------+
| ``append``  | ``bmc``,   | When generating a counter-example trace, add the        |
|             | ``prove``, | specified number of cycles at the end of the trace.     |
|             | ``cover``  | Default: ``0``                                          |
+-------------+------------+---------------------------------------------------------+

Engines section
---------------

TBD

Script section
--------------

TBD

Files section
-------------

TBD

