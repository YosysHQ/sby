#
# SymbiYosys (sby) -- Front-end for Yosys-based formal verification flows
#
# Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#

import os, re, glob, json
from sby_core import SbyProc
from sby_design import pretty_path

def sim_witness_trace(prefix, task, engine_idx, witness_file, *, append, deps=()):
    trace_name = os.path.basename(witness_file)[:-3]
    formats = []
    tracefile = None
    if task.opt_vcd and task.opt_vcd_sim:
        tracefile = f"engine_{engine_idx}/{trace_name}.vcd"
        formats.append(f"-vcd {trace_name}.vcd")
    if task.opt_fst:
        tracefile = f"engine_{engine_idx}/{trace_name}.fst"
        formats.append(f"-fst {trace_name}.fst")

    # for warnings / error messages
    error_tracefile = f"{task.workdir}/{tracefile}" or f"{task.workdir}/engine_{engine_idx}/{trace_name}.yw"

    sim_log = task.log_prefix(f"{prefix}.{trace_name}")

    sim_log(f"Generating simulation trace for witness file: {witness_file}")

    with open(f"{task.workdir}/engine_{engine_idx}/{trace_name}.ys", "w") as f:
        print(f"# running in {task.workdir}/engine_{engine_idx}/", file=f)
        print(f"read_rtlil ../model/design_prep.il", file=f)
        print(f"sim -hdlname -summary {trace_name}.json -append {append} -r {trace_name}.yw {' '.join(formats)}", file=f)

    def exit_callback(retval):

        if task.design:
            task.precise_prop_status = True

        assertion_types = set()

        with open(f"{task.workdir}/engine_{engine_idx}/{trace_name}.json") as summary:
            summary = json.load(summary)
            for assertion in summary["assertions"]:
                assertion["path"] = tuple(assertion["path"])

        first_appended = summary["steps"] + 1 - append

        printed_assumption_warning = False

        task.summary.add_event(engine_idx=engine_idx, trace=trace_name, path=tracefile)

        for assertion in summary["assertions"]:
            if task.design:
                try:
                    prop = task.design.properties_by_path[tuple(assertion["path"])]
                except KeyError:
                    prop = None
            else:
                prop = None

            hdlname = pretty_path((summary['top'], *assertion['path'])).rstrip()
            task.summary.add_event(
                engine_idx=engine_idx,
                trace=trace_name, path=tracefile, hdlname=hdlname,
                type=assertion["type"], src=assertion.get("src"), step=assertion["step"],
                prop=prop)

            assertion_types.add(assertion["type"])

            if assertion["type"] == '$assume':
                if assertion["step"] < first_appended:
                    task.error(f"produced trace {error_tracefile!r} violates assumptions during simulation")
                elif not printed_assumption_warning:
                    sim_log(f"Warning: trace {error_tracefile!r} violates assumptions during simulation of the appended time steps.")
                    if not task.opt_append_assume:
                        sim_log("For supported engines, the option 'append_assume on' can be used to find inputs that uphold assumptions during appended time steps.")
                    printed_assumption_warning = True

    proc = SbyProc(
        task,
        f"{prefix}.{trace_name}",
        deps,
        f"""cd {task.workdir}/engine_{engine_idx}; {task.exe_paths["yosys"]} -ql {trace_name}.log {trace_name}.ys""",
    )
    proc.noprintregex = re.compile(r"Warning: Assert .* failed.*")
    proc.register_exit_callback(exit_callback)
    return proc
