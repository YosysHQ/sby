# Callback JSON Protocol

The `--callback` option allows controlling the counter-example enumeration using a JSON based protocol.

With `--callback '-'`, callback events are output to stdout and callback responses are read from stdin.

With `--callback '<command-line>'` the given command line is launched as subprocess which recieves callback events on stdin and produces callback responses on stdout.

Each event and response consists of a single line containing a JSON object.

## Callback Events

A callback event is emitted whenever:

* a step is entered for the first time (`"event": "step"`),
* a new counter-example trace was found (`"event": "trace"`) or
* no counter-examples remain for the current step (`"event": "unsat"`).

Every callback event includes the current step (`"step": <step>`) and a list of enabled named blocked patterns (`"enabled": [...]`, see below).

A trace event also includes a path to the `.yw` file of the counter-example trace. The `.aiw` file can be found by replacing the file extension.

After an event is emitted, the enumeration script waits for one or multiple callback responses, continuing when a callback response includes the `"action"` key.

## Callback Responses

### Actions

An action hands control back to the enumeration script. The following three actions are available:

* `{"action": "search"}`: Search for a further counter-example in the current time step.
* `{"action": "advance"}`: Advance to the next time step, abandoning any not-yet-enumerated counter-examples of the current time step.
* `{"action": "next"}`: Search for the next counter-example, automatically advancing to the next time-step when necessary.

Note that an `{"action": "search"}` response to an `"unsat"` event remains at the same time step, which can be used to disable a named blocked pattern, which can make further counter-examples available.

In the interactive callback mode (`--callback '-'`) it is possible to use single letter shortcuts `s`, `a` and `n` instead of the JSON syntax `{"action": "search"}`, `{"action": "advance"}` and `{"action": "next"}` respectively.

### Blocking Patterns

A specific input pattern given as an `.yw` or `.aiw` file can be blocked.
During enumeration, only counter-examples that differ from in at least one non-`x` bit from every blocked pattern are considered.

A `.yw` pattern can be blocked using `{"block_yw": "<file-path>"}` and a `.aiw` pattern using `{"block_aiw": "<file-path>"}`. Additionally a pattern can be given a name by using `{"block_...": "<file-path>", "name": "<name>"}`, in which case it will be possible to disable and reenable the blocked pattern. By default a newly added named blocked pattern is enabled.

A named pattern can be disable with the `{"disable": "<name>"}` response and re-enabled with the `{"enable": "<name>"}` response.
