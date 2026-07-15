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
   :end-before: dumpcfg
   :caption: ``[engines]`` section is only enabled for ``task3``


Alternative tag assignment
--------------------------

An alternative tag assignment method is provided which uses the colon (``:``)
character to separate tasks and tags.  With this method it is possible to assign
a group of tags to multiple tasks at the same time.

.. code-block:: sby

   [tasks]
   task1
   task2
   task3

   task1 task2 : deep bounded


Default tasks
-------------

A special tag, ``default``, is provided for controlling which tasks should be
run when no specific tasks are provided.  The ``--dumpdefaults`` option is
provided for getting the list of default tasks for a given ``.sby`` file.  Note
that ``default`` does *not* get added to the list of tags, and should not be
used for controlling conditional lines.

.. literalinclude:: /../examples/tags/default.sby
   :language: sby
   :caption: ``default.sby`` tasks section

.. literalinclude:: /../examples/tags/default.log
   :language: console
   :start-at: dumpdefaults
   :end-before: dumpcfg
   :caption: Using ``--dumpdefaults``


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
expected.  Note that when ``--dumpcfg`` is called without any tasks, the
generated config does not include any lines that are conditionally enabled
(``<tag>:``) and all lines that are conditionally disabled (``~<tag>:``).  The
``[tasks]`` section is also only included when called without any tasks.

.. literalinclude:: /../examples/tags/complex.log
   :language: console
   :start-at: dumptasks
   :end-before: dumptags

.. literalinclude:: /../examples/tags/complex.log
   :language: console
   :start-at: dumpcfg
