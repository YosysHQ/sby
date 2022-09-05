#
# SymbiYosys (sby) -- Front-end for Yosys-based formal verification flows
#
# Copyright (C) 2016  Claire Xenia Wolf <claire@yosyshq.com>
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

import re, os, getopt
from types import SimpleNamespace
from sby_core import SbyProc

def run(mode, task, engine_idx, engine):
    random_seed = None

    opts, solver_args = getopt.getopt(engine[1:], "", ["seed="])

    if len(solver_args) == 0:
        task.error("Missing solver command.")

    for o, a in opts:
        if o == "--seed":
            random_seed = a
        else:
            task.error("Unexpected BTOR engine options.")

    if solver_args[0] == "btormc":
        solver_cmd = ""
        if random_seed:
            solver_cmd += f"BTORSEED={random_seed} "
        solver_cmd += task.exe_paths["btormc"] + f""" --stop-first {0 if mode == "cover" else 1} -v 1 -kmax {task.opt_depth - 1}"""
        if task.opt_skip is not None:
            solver_cmd += f" -kmin {task.opt_skip}"
        solver_cmd += " ".join([""] + solver_args[1:])

    elif solver_args[0] == "pono":
        if random_seed:
            task.error("Setting the random seed is not available for the pono solver.")
        if task.opt_skip is not None:
            task.error("The btor engine supports the option skip only for the btormc solver.")
        solver_cmd = task.exe_paths["pono"] + f" --witness -v 1 -e bmc -k {task.opt_depth - 1}"
        solver_cmd += " ".join([""] + solver_args[1:])

    else:
        task.error(f"Invalid solver command {solver_args[0]}.")

    common_state = SimpleNamespace()
    common_state.solver_status = None
    common_state.produced_cex = 0
    common_state.expected_cex = 1
    common_state.wit_file = None
    common_state.assert_fail = False
    common_state.produced_traces = []
    common_state.print_traces_max = 5
    common_state.running_procs = 0

    def print_traces_and_terminate():
        if mode == "cover":
            if common_state.assert_fail:
                proc_status = "FAIL"
            elif common_state.expected_cex == 0:
                proc_status = "pass"
            elif common_state.solver_status == "sat":
                proc_status = "pass"
            elif common_state.solver_status == "unsat":
                proc_status = "FAIL"
            else:
                task.error(f"engine_{engine_idx}: Engine terminated without status.")
        else:
            if common_state.expected_cex == 0:
                proc_status = "pass"
            elif common_state.solver_status == "sat":
                proc_status = "FAIL"
            elif common_state.solver_status == "unsat":
                proc_status = "pass"
            else:
                task.error(f"engine_{engine_idx}: Engine terminated without status.")

        task.update_status(proc_status.upper())
        task.log(f"engine_{engine_idx}: Status returned by engine: {proc_status}")
        task.summary.append(f"""engine_{engine_idx} ({" ".join(engine)}) returned {proc_status}""")

        if len(common_state.produced_traces) == 0:
            task.log(f"""engine_{engine_idx}: Engine did not produce a{" counter" if mode != "cover" else "n "}example.""")
        elif len(common_state.produced_traces) <= common_state.print_traces_max:
            task.summary.extend(common_state.produced_traces)
        else:
            task.summary.extend(common_state.produced_traces[:common_state.print_traces_max])
            excess_traces = len(common_state.produced_traces) - common_state.print_traces_max
            task.summary.append(f"""and {excess_traces} further trace{"s" if excess_traces > 1 else ""}""")

        task.terminate()

    if mode == "cover":
        def output_callback2(line):
            match = re.search(r"Assert failed in test", line)
            if match:
                common_state.assert_fail = True
            return line
    else:
        def output_callback2(line):
            return line

    def make_exit_callback(suffix):
        def exit_callback2(retcode):
            vcdpath = f"{task.workdir}/engine_{engine_idx}/trace{suffix}.vcd"
            if os.path.exists(vcdpath):
                common_state.produced_traces.append(f"""{"" if mode == "cover" else "counterexample "}trace: {vcdpath}""")

            common_state.running_procs -= 1
            if (common_state.running_procs == 0):
                print_traces_and_terminate()

        return exit_callback2

    def output_callback(line):
        if mode == "cover":
            if solver_args[0] == "btormc":
                match = re.search(r"calling BMC on ([0-9]+) properties", line)
                if match:
                    common_state.expected_cex = int(match[1])
                    if common_state.produced_cex != 0:
                        task.error(f"engine_{engine_idx}: Unexpected engine output (property count).")

            else:
                task.error(f"engine_{engine_idx}: BTOR solver '{solver_args[0]}' is currently not supported in cover mode.")

        if (common_state.produced_cex < common_state.expected_cex) and line == "sat":
            if common_state.wit_file != None:
                task.error(f"engine_{engine_idx}: Unexpected engine output (sat).")
            if common_state.expected_cex == 1:
                common_state.wit_file = open(f"{task.workdir}/engine_{engine_idx}/trace.wit", "w")
            else:
                common_state.wit_file = open(f"""{task.workdir}/engine_{engine_idx}/trace{common_state.produced_cex}.wit""", "w")
            if solver_args[0] != "btormc":
                proc.log("Found satisfiability witness.")

        if common_state.wit_file:
            print(line, file=common_state.wit_file)
            if line == ".":
                if common_state.expected_cex == 1:
                    suffix = ""
                else:
                    suffix = common_state.produced_cex

                if mode == "cover" or task.opt_vcd:
                    # TODO cover runs btorsim not only for trace generation, can we run it without VCD generation in that case?
                    proc2 = SbyProc(
                        task,
                        f"engine_{engine_idx}_{common_state.produced_cex}",
                        task.model("btor"),
                        "cd {dir} ; btorsim -c --vcd engine_{idx}/trace{i}.vcd --hierarchical-symbols --info model/design_btor{s}.info model/design_btor{s}.btor engine_{idx}/trace{i}.wit".format(dir=task.workdir, idx=engine_idx, i=suffix, s='_single' if solver_args[0] == 'pono' else ''),
                        logfile=open(f"{task.workdir}/engine_{engine_idx}/logfile2.txt", "w")
                    )
                    proc2.output_callback = output_callback2
                    proc2.exit_callback = make_exit_callback(suffix)
                    proc2.checkretcode = True
                    common_state.running_procs += 1

                common_state.produced_cex += 1
                common_state.wit_file.close()
                common_state.wit_file = None
                if common_state.produced_cex == common_state.expected_cex:
                    common_state.solver_status = "sat"

        else:
            if solver_args[0] == "btormc":
                if "calling BMC on" in line:
                    return line
                if "SATISFIABLE" in line:
                    return line
                if "bad state properties at bound" in line:
                    return line
                if "deleting model checker:" in line:
                    if common_state.solver_status is None:
                        common_state.solver_status = "unsat"
                    return line

            elif solver_args[0] == "pono":
                if line == "unknown":
                    if common_state.solver_status is None:
                        common_state.solver_status = "unsat"
                    return "No CEX found."
                if line not in ["b0"]:
                    return line

            print(line, file=proc.logfile)

        return None

    def exit_callback(retcode):
        if common_state.expected_cex != 0:
            if common_state.solver_status is None:
                task.error(f"engine_{engine_idx}: Could not determine engine status.")

        if common_state.solver_status == "unsat":
            if common_state.expected_cex == 1:
                with open(f"""{task.workdir}/engine_{engine_idx}/trace.wit""", "w") as wit_file:
                    print("unsat", file=wit_file)
            else:
                for i in range(common_state.produced_cex, common_state.expected_cex):
                    with open(f"{task.workdir}/engine_{engine_idx}/trace{i}.wit", "w") as wit_file:
                        print("unsat", file=wit_file)

        common_state.running_procs -= 1
        if (common_state.running_procs == 0):
            print_traces_and_terminate()

    proc = SbyProc(
        task,
        f"engine_{engine_idx}", task.model("btor"),
        f"cd {task.workdir}; {solver_cmd} model/design_btor{'_single' if solver_args[0]=='pono' else ''}.btor",
        logfile=open(f"{task.workdir}/engine_{engine_idx}/logfile.txt", "w")
    )
    proc.checkretcode = True
    if solver_args[0] == "pono":
        proc.retcodes = [0, 1, 255] # UNKNOWN = -1, FALSE = 0, TRUE = 1, ERROR = 2
    proc.output_callback = output_callback
    proc.exit_callback = exit_callback
    common_state.running_procs += 1
