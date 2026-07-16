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
provided for getting the list of default tasks for a given ``.sby`` file.  If no
``default`` tag is provided, all tasks listed in the ``[tasks]`` section will be
used as the default.  Note that ``default`` does *not* get added to the list of
tags, and should not be used for controlling conditional lines.

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

A better way
~~~~~~~~~~~~

For this particular example, a better approach might be the following:

.. literalinclude:: /../examples/tags/alt.sby
   :language: sby

This uses regex string matching on the task name, allowing any task to be
provided in the ``sby`` call that matches at least one task.  This allows for
all of the same calls, e.g. ``sby alt.sby unbounded_hAdX``, but there are no
longer any default tasks, so calling ``sby alt.sby`` is no longer valid.

.. warning::

   So long as the provided task matches *any* regex task then SBY will recognize
   it as valid, opening up the potential for downstream issues where a partially
   recognized task name is not fully configured.  Extreme care should be taken
   when using multiple regex tasks.

We use the tag ``known`` here to validate that the host/device implementations
are valid. This isn't strictly necessary, but it does mean that we can provide
an error message if an unknown host/device is used, and demonstrates that care
must be taken when using regex matching.  e.g. without the ``assert task is
None`` line, a task of ``witness_hAdX`` would provide an error message about
``mode`` being unset, which may not be immediately obvious as to why that is.


Running tasks in parallel
-------------------------

By default, if there are multiple tasks available then SBY will attempt to run
them in parallel.  If SBY is called by a modern version of ``make``, it will
attempt to connect to the Make jobserver for controlling parallelism.  If no
jobserver is available, such as when calling ``sby`` directly, the maximum
number of parallel jobs can be set by the ``-j`` command line option:

.. code-block:: shell

   # Calling SBY with up to 4 parallel tasks
   sby -j4 <jobname>.sby

Task dependencies with Make
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Say we have some set of tasks which can be broken into two stages, and the
second stage shouldn't run until the first stage has completed.  In SBY we have
no way to describe such a dependency.  Instead, we can use a Makefile for flow
control:

.. literalinclude:: /../examples/tags/dependencies.sby
   :language: sby
   :caption: ``docs/examples/tags/dependencies.sby``

.. literalinclude:: /../examples/tags/dependencies.mk
   :language: make
   :caption: ``docs/examples/tags/dependencies.mk``
   :start-after: PHONY
   :end-before: both tasks

Since each task will (by default) output to a directory called
``<jobname>_<taskname>``, we are able to provide a single pattern rule that
will call ``sby`` for any given ``<taskname>``.

An alternative approach is to define a single rule for each stage, allowing a
single invocation of SBY to run multiple tasks.  Remember that SBY can connect
to the Make jobserver, so no parallelism is lost here.  This may even reduce the
overhead of launching multiple ``sby`` processes, particularly if there are many
tasks.

.. literalinclude:: /../examples/tags/dependencies.mk
   :language: make
   :caption: Make rule for running both stage 2 tasks together
   :start-after: both tasks


