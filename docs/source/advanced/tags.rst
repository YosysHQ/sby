Tasks and tags
==============

Multi-line tag sections
-----------------------
If ``<tag>:`` is used on a line by itself then the conditional string
extends until ``--`` is found on a line by itself.

.. code-block:: sby

   [options]
   task_1_or_2:
   mode bmc
   depth 100
   --

   task3:
   mode prove
   --

If the closing ``--`` line is ommitted, the current conditional block will
extend until the next conditional block.  However it is recommended to always
include the closing ``--`` line to avoid inadvertently making the rest of the
file conditional.

.. literalinclude:: /../examples/tags/bad.sby
   :language: sby
   :start-at: [options]
   :caption: ``bad.sby``

.. literalinclude:: /../examples/tags/bad.log
   :language: console
   :start-at: dumpcfg
   :caption: ``[engines]`` section is only enabled for ``task3``


Complex pycode blocks
---------------------
The following example demonstrates how to configure safety and liveness checks
for all combinations of host and device implementations.  Note that the ``task``
variable is set to a value of ``None`` when initially parsing the ``.sby`` file,
so it is important to check ``if task is not None`` to avoid the
``AttributeError`` when trying to use string methods on it.

.. literalinclude:: /../examples/tags/complex.sby
   :language: sby
   :caption: ``docs/examples/tags/complex.sby``

.. warning::

   Including section headings in pycode blocks like this is a quick way to make
   your ``.sby`` file very difficult to follow and is generally not recommended.
   However since it is not possible to share variables between pycode sections,
   in cases such as this it does simplify adding new host/device implementations
   while avoiding duplication of the tag parsing.

When working with complex ``.sby`` files like this, it is very helpful to use
``--dumptasks`` and ``--dumpcfg`` to confirm things are being pre-processed as
expected.

.. literalinclude:: /../examples/tags/complex.log
   :language: console
   :start-at: dumptasks
   :end-before: dumptags

.. literalinclude:: /../examples/tags/complex.log
   :language: console
   :start-at: dumpcfg
