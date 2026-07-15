Tasks and tags
==============

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
