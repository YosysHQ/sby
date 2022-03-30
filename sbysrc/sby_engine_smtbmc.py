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
from sby_core import SbyProc

def run(mode, task, engine_idx, engine):
    smtbmc_opts = []
    nomem_opt = False
    presat_opt = True
    unroll_opt = None
    syn_opt = False
    stbv_opt = False
    stdt_opt = False
    dumpsmt2 = False
    progress = False
    basecase_only = False
    induction_only = False
    keep_going = False
    random_seed = None
    task.precise_prop_status = True

    opts, args = getopt.getopt(engine[1:], "", ["nomem", "syn", "stbv", "stdt", "presat",
            "nopresat", "unroll", "nounroll", "dumpsmt2", "progress", "basecase", "induction", "keep-going", "seed="])

    for o, a in opts:
        if o == "--nomem":
            nomem_opt = True
        elif o == "--syn":
            syn_opt = True
        elif o == "--stbv":
            stbv_opt = True
        elif o == "--stdt":
            stdt_opt = True
        elif o == "--presat":
            presat_opt = True
        elif o == "--nopresat":
            presat_opt = False
        elif o == "--unroll":
            unroll_opt = True
        elif o == "--nounroll":
            unroll_opt = False
        elif o == "--dumpsmt2":
            dumpsmt2 = True
        elif o == "--progress":
            progress = True
        elif o == "--basecase":
            if induction_only:
                task.error("smtbmc options --basecase and --induction are exclusive.")
            basecase_only = True
        elif o == "--induction":
            if basecase_only:
                task.error("smtbmc options --basecase and --induction are exclusive.")
            induction_only = True
        elif o == "--keep-going":
            if mode not in ("bmc", "prove", "prove_basecase", "prove_induction"):
                task.error("smtbmc option --keep-going is only supported in bmc and prove mode.")
            keep_going = True
        elif o == "--seed":
            random_seed = a
        else:
            task.error(f"Invalid smtbmc options {o}.")

    xtra_opts = False
    for i, a in enumerate(args):
        if i == 0 and a == "z3" and unroll_opt is None:
                unroll_opt = False
        if a == "--":
            xtra_opts = True
            continue
        if xtra_opts:
            smtbmc_opts.append(a)
        else:
            smtbmc_opts += ["-s" if i == 0 else "-S", a]

    if presat_opt:
        smtbmc_opts += ["--presat"]

    if unroll_opt is None or unroll_opt:
        smtbmc_opts += ["--unroll"]

    if task.opt_smtc is not None:
        smtbmc_opts += ["--smtc", f"src/{task.opt_smtc}"]

    if task.opt_tbtop is not None:
         smtbmc_opts += ["--vlogtb-top", task.opt_tbtop]

    model_name = "smt2"
    if syn_opt: model_name += "_syn"
    if nomem_opt: model_name += "_nomem"
    if stbv_opt: model_name += "_stbv"
    if stdt_opt: model_name += "_stdt"

    if mode == "prove":
        if not induction_only:
            run("prove_basecase", task, engine_idx, engine)
        if not basecase_only:
            run("prove_induction", task, engine_idx, engine)
        return

    procname = f"engine_{engine_idx}"
    trace_prefix = f"engine_{engine_idx}/trace"
    logfile_prefix = f"{task.workdir}/engine_{engine_idx}/logfile"

    if mode == "prove_basecase":
        procname += ".basecase"
        logfile_prefix += "_basecase"

    if mode == "prove_induction":
        procname += ".induction"
        trace_prefix += "_induct"
        logfile_prefix += "_induction"
        smtbmc_opts.append("-i")

    if mode == "cover":
        smtbmc_opts.append("-c")
        trace_prefix += "%"

    if keep_going:
        smtbmc_opts.append("--keep-going")
        trace_prefix += "%"

    if dumpsmt2:
        smtbmc_opts += ["--dump-smt2", trace_prefix.replace("%", "") + ".smt2"]

    if not progress:
        smtbmc_opts.append("--noprogress")


    if task.opt_skip is not None:
        t_opt = "{}:{}".format(task.opt_skip, task.opt_depth)
    else:
        t_opt = "{}".format(task.opt_depth)

    random_seed = f"--info \"(set-option :random-seed {random_seed})\"" if random_seed else ""
    proc = SbyProc(
        task,
        procname,
        task.model(model_name),
        f"""cd {task.workdir}; {task.exe_paths["smtbmc"]} {" ".join(smtbmc_opts)} -t {t_opt} {random_seed} --append {task.opt_append} --dump-vcd {trace_prefix}.vcd --dump-vlogtb {trace_prefix}_tb.v --dump-smtc {trace_prefix}.smtc model/design_{model_name}.smt2""",
        logfile=open(logfile_prefix + ".txt", "w"),
        logstderr=(not progress)
    )

    if mode == "prove_basecase":
        task.basecase_procs.append(proc)

    if mode == "prove_induction":
        task.induction_procs.append(proc)

    proc_status = None
    last_prop = []

    def output_callback(line):
        nonlocal proc_status
        nonlocal last_prop
        smt2_trans = {'\\':'/', '|':'/'}

        match = re.match(r"^## [0-9: ]+ Status: FAILED", line)
        if match:
            proc_status = "FAIL"
            return line.replace("FAILED", "failed")

        match = re.match(r"^## [0-9: ]+ Status: PASSED", line)
        if match:
            proc_status = "PASS"
            return line.replace("PASSED", "passed")

        match = re.match(r"^## [0-9: ]+ Status: PREUNSAT", line)
        if match:
            proc_status = "ERROR"
            return line

        match = re.match(r"^## [0-9: ]+ Unexpected response from solver:", line)
        if match:
            proc_status = "ERROR"
            return line

        match = re.match(r"^## [0-9: ]+ Assert failed in (\S+): (\S+) \((\S+)\)", line)
        if match:
            cell_name = match[3]
            prop = task.design_hierarchy.find_property_by_cellname(cell_name, trans_dict=smt2_trans)
            prop.status = "FAIL"
            last_prop.append(prop)
            return line

        match = re.match(r"^## [0-9: ]+ Reached cover statement at (\S+) \((\S+)\) in step \d+.", line)
        if match:
            cell_name = match[2]
            prop = task.design_hierarchy.find_property_by_cellname(cell_name, trans_dict=smt2_trans)
            prop.status = "PASS"
            last_prop.append(prop)
            return line

        match = re.match(r"^## [0-9: ]+ Writing trace to VCD file: (\S+)", line)
        if match and last_prop:
            for p in last_prop:
                if not p.tracefile:
                    p.tracefile = match[1]
            last_prop = []
            return line

        match = re.match(r"^## [0-9: ]+ Unreached cover statement at (\S+) \((\S+)\).", line)
        if match:
            cell_name = match[2]
            prop = task.design_hierarchy.find_property_by_cellname(cell_name, trans_dict=smt2_trans)
            prop.status = "FAIL"

        return line

    def exit_callback(retcode):
        if proc_status is None:
            task.error(f"engine_{engine_idx}: Engine terminated without status.")

        if mode == "bmc" or mode == "cover":
            task.update_status(proc_status)
            proc_status_lower = proc_status.lower() if proc_status == "PASS" else proc_status
            task.log(f"engine_{engine_idx}: Status returned by engine: {proc_status_lower}")
            task.summary.append(f"""engine_{engine_idx} ({" ".join(engine)}) returned {proc_status_lower}""")

            if proc_status == "FAIL" and mode != "cover":
                if os.path.exists(f"{task.workdir}/engine_{engine_idx}/trace.vcd"):
                    task.summary.append(f"counterexample trace: {task.workdir}/engine_{engine_idx}/trace.vcd")
            elif proc_status == "PASS" and mode == "cover":
                print_traces_max = 5
                for i in range(print_traces_max):
                    if os.path.exists(f"{task.workdir}/engine_{engine_idx}/trace{i}.vcd"):
                        task.summary.append(f"trace: {task.workdir}/engine_{engine_idx}/trace{i}.vcd")
                    else:
                        break
                else:
                    excess_traces = 0
                    while os.path.exists(f"{task.workdir}/engine_{engine_idx}/trace{print_traces_max + excess_traces}.vcd"):
                        excess_traces += 1
                    if excess_traces > 0:
                        task.summary.append(f"""and {excess_traces} further trace{"s" if excess_traces > 1 else ""}""")
            elif proc_status == "PASS" and mode == "bmc":
                for prop in task.design_hierarchy:
                    if prop.type == prop.Type.ASSERT and prop.status == "UNKNOWN":
                        prop.status = "PASS"

            task.terminate()

        elif mode in ["prove_basecase", "prove_induction"]:
            proc_status_lower = proc_status.lower() if proc_status == "PASS" else proc_status
            task.log(f"""engine_{engine_idx}: Status returned by engine for {mode.split("_")[1]}: {proc_status_lower}""")
            task.summary.append(f"""engine_{engine_idx} ({" ".join(engine)}) returned {proc_status_lower} for {mode.split("_")[1]}""")

            if mode == "prove_basecase":
                for proc in task.basecase_procs:
                    proc.terminate()

                if proc_status == "PASS":
                    task.basecase_pass = True

                else:
                    task.update_status(proc_status)
                    if os.path.exists(f"{task.workdir}/engine_{engine_idx}/trace.vcd"):
                        task.summary.append(f"counterexample trace: {task.workdir}/engine_{engine_idx}/trace.vcd")
                    task.terminate()

            elif mode == "prove_induction":
                for proc in task.induction_procs:
                    proc.terminate()

                if proc_status == "PASS":
                    task.induction_pass = True

            else:
                assert False

            if task.basecase_pass and task.induction_pass:
                for prop in task.design_hierarchy:
                    if prop.type == prop.Type.ASSERT and prop.status == "UNKNOWN":
                        prop.status = "PASS"
                task.update_status("PASS")
                task.summary.append("successful proof by k-induction.")
                task.terminate()

        else:
            assert False

    proc.output_callback = output_callback
    proc.exit_callback = exit_callback
