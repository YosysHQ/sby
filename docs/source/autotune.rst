Autotune: Automatic Engine Selection
====================================

Selecting the best performing engine for a given verification task often
requires some amount of trial and error. To reduce the manual work required for
this, sby offers the ``--autotune`` option. This takes an ``.sby`` file and
runs it using engines and engine configurations. At the end it produces a
report listing the fastest engines among these candidates.

Using Autotune
--------------

To run autotune, you can add the ``--autotune`` option to your usual sby
invocation. For example, if you usually run ``sby demo.sby`` you would run
``sby --autotune demo.sby`` instead. When the ``.sby`` file contains multiple
tasks, autotune is run for each task independently. As without ``--autotune``,
it is possible to specify which tasks to run on the command line.

Autotune runs without requiring further interaction, and will eventually print a
list of engine configurations and their respective solving times. To
permanently use an engine configuration you can copy it from the
``sby --autotune`` output into the ``[engines]`` section of your ``.sby`` file.

Example
^^^^^^^

The Sby repository contains a `small example`_ in the ``docs/examples/autotune``
directory.

The ``divider.sby`` file contains the following ``[engines]`` section:

.. code-block:: sby

   [engines]
   smtbmc

We notice that running ``sby -f divider.sby medium`` takes a long time and want
to see if another engine would speed things up, so we run
``sby --autotune -f divider.sby medium``. After a few minutes this prints:

.. code-block:: text

   SBY [divider_medium] finished engines:
   SBY [divider_medium]   #4: engine_7: smtbmc --nopresat bitwuzla -- --noincr (32 seconds, status=PASS)
   SBY [divider_medium]   #3: engine_2: smtbmc boolector -- --noincr (32 seconds, status=PASS)
   SBY [divider_medium]   #2: engine_3: smtbmc --nopresat boolector -- --noincr (32 seconds, status=PASS)
   SBY [divider_medium]   #1: engine_6: smtbmc bitwuzla -- --noincr (31 seconds, status=PASS)
   SBY [divider_medium] DONE (AUTOTUNED, rc=0)

This tells us that for the ``medium`` task, the best engine choice (#1) is
``smtbmc bitwuzla -- --noincr``. To use this engine by default we can change
the ``[engines]`` section of ``divider.sby`` to:

.. code-block:: sby

   [engines]
   smtbmc bitwuzla -- --noincr

.. _`small example`: https://github.com/YosysHQ/sby/tree/master/docs/examples/autotune

Autotune Log Output
-------------------

The log output in ``--autotune`` mode differs from the usual sby log output.

It also starts with preparing the design (this includes running the user
provided ``[script]``) so it can be passed to the solvers. This is only done
once and will be reused to run every candidate engine.

.. code-block:: text

   SBY [demo] model 'base': preparing now...
   SBY [demo] base: starting process "cd demo/src; yosys -ql ../model/design.log ../model/design.ys"
   SBY [demo] base: finished (returncode=0)
   SBY [demo] prepared model 'base'

This is followed by selecting the engine candidates to run. The design
and sby configuration are analyzed to skip engines that are not compatible or
unlikely to work well. When an engine is skipped due to a recommendation, a
corresponding log message is displayed as well as the total number of
candidates to try:

.. code-block:: text

   SBY [demo] checking more than 20 timesteps (100), disabling nonincremental smtbmc
   SBY [demo] testing 16 engine configurations...

After this, the candidate engine configurations are started. Depending on the
configuration, engines can run in parallel. The engine output itself is not
logged to stdout when running autotune, so you will only see messages about
starting an engine:

.. code-block:: text

   SBY [demo] engine_1 (smtbmc --nopresat boolector): starting... (14 configurations pending)
   SBY [demo] engine_2 (smtbmc bitwuzla): starting... (13 configurations pending)
   SBY [demo] engine_3 (smtbmc --nopresat bitwuzla): starting... (12 configurations pending)
   ...

The engine log that would normally be printed is instead redirected to files
named ``engine_*_autotune.txt`` within sby's working directory.

To run an engine, further preparation steps may be necessary. These are cached
and will be reused for every engine requiring them, while properly accounting
for the required prepration time. Below is an example of the log output
produced by such a preparation step. Note that this runs in parallel, so it may
be interspersed with other log output.

.. code-block:: text

   SBY [demo] model 'smt2': preparing now...
   SBY [demo] smt2: starting process "cd demo/model; yosys -ql design_smt2.log design_smt2.ys"
   ...
   SBY [demo] smt2: finished (returncode=0)
   SBY [demo] prepared model 'smt2'

Whenever an engine finishes, a log message is printed:

.. code-block:: text

   SBY [demo] engine_4 (smtbmc --unroll yices): succeeded (status=PASS)
   SBY [demo] engine_4 (smtbmc --unroll yices): took 30 seconds (first engine to finish)

When an engine takes longer than the current hard timeout, it is stopped:

.. code-block:: text

   SBY [demo] engine_2 (smtbmc bitwuzla): timeout (150 seconds)

Depending on the configuration, autotune will also stop an engine earlier when
reaching a soft timeout. If no other engine finishes in less
time, the engine will be retried later with a longer soft timeout:

.. code-block:: text

   SBY [demo] engine_0 (smtbmc boolector): timeout (60 seconds, will be retried if necessary)


Finally, a summary of all finished engines is printed, sorted by
their solving time:

.. code-block:: text

   SBY [demo] finished engines:
   SBY [demo]   #3: engine_1: smtbmc --nopresat boolector (52 seconds, status=PASS)
   SBY [demo]   #2: engine_5: smtbmc --nopresat --unroll yices (41 seconds, status=PASS)
   SBY [demo]   #1: engine_4: smtbmc --unroll yices (30 seconds, status=PASS)
   SBY [demo] DONE (AUTOTUNED, rc=0)

If any tried engine encounters an error or produces an unexpected result,
autotune will also output a list of failed engines. Note that when the sby file
does not contain the ``expect`` option, autotune defaults to
``expect pass,fail`` to simplify running autotune on a verification task with a
currently unknown outcome.

Configuring Autotune
--------------------

Autotune can be configured by adding an ``[autotune]`` section to the ``.sby``
file. Each line in that section has the form ``option_name value``, the
possible options and their supported values are described below. In addition,
the ``--autotune-config`` command line option can be used to specify a file
containing further autotune options, using the same syntax. When both are used,
the command line option takes precedence. This makes it easy to run autotune
with existing ``.sby`` files without having to modify them.

Autotune Options
----------------

+--------------------+------------------------------------------------------+
| Autotune Option    | Description                                          |
+====================+======================================================+
| ``timeout``        | Set a different timeout value (in seconds) used only |
|                    | for autotune. The value ``none`` can be used to      |
|                    | disable the timeout. Default: uses the non-autotune  |
|                    | timeout option.                                      |
+--------------------+------------------------------------------------------+
| ``soft_timeout``   | Initial timeout value (in seconds) used to interrupt |
|                    | a candidate engine when other candidates are         |
|                    | pending. Increased every time a candidate is retried |
|                    | to ensure progress. Default: ``60``                  |
+--------------------+------------------------------------------------------+
| ``wait``           | Additional time to wait past the time taken by the   |
|                    | fastest finished engine candidate so far. Can be an  |
|                    | absolute time in seconds, a percentage of the        |
|                    | fastest candidate or a sum of both.                  |
|                    | Default: ``50%+10``                                  |
+--------------------+------------------------------------------------------+
| ``parallel``       | Maximal number of engine candidates to try in        |
|                    | parallel. When set to ``auto``, the number of        |
|                    | available CPUs is used. Default: ``auto``            |
+--------------------+------------------------------------------------------+
| ``presat``         | Filter candidates by whether they perform a presat   |
|                    | check. Values ``on``, ``off``, ``any``.              |
|                    | Default: ``any``                                     |
+--------------------+------------------------------------------------------+
| ``incr``           | Filter candidates by whether they use incremental    |
|                    | solving (when applicable). Values ``on``, ``off``,   |
|                    | ``any``, ``auto`` (see next option).                 |
|                    | Default: ``auto``                                    |
+--------------------+------------------------------------------------------+
| ``incr_threshold`` | Number of timesteps required to only consider        |
|                    | incremental solving when ``incr`` is set to          |
|                    | ``auto``. Default: ``20``                            |
+--------------------+------------------------------------------------------+
| ``mem``            | Filter candidates by whether they have native        |
|                    | support for memory. Values ``on``, ``any``, ``auto`` |
|                    | (see next option). Default: ``auto``                 |
+--------------------+------------------------------------------------------+
| ``mem_threshold``  | Number of memory bits required to only consider      |
|                    | candidates with native memory support when ``mem``   |
|                    | is set to ``auto``. Default: ``10240``               |
+--------------------+------------------------------------------------------+
| ``forall``         | Filter candidates by whether they support            |
|                    | ``$allconst``/``$allseq``. Values ``on``, ``any``,   |
|                    | ``auto`` (``on`` when ``$allconst``/``allseq`` are   |
|                    | found in the design). Default: ``auto``              |
+--------------------+------------------------------------------------------+
