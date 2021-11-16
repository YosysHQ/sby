#
# SymbiYosys (sby) -- Front-end for Yosys-based formal verification flows
#
# Copyright (C) 2016  Clifford Wolf <clifford@clifford.at>
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
from sby_core import SbyTask

def run(mode, job, engine_idx, engine):
    smtbmc_opts = []
    nomem_opt = False
    presat_opt = True
    unroll_opt = None
    syn_opt = False
    stbv_opt = False
    stdt_opt = False
    dumpsmt2 = False
    progress = False
    anybase = False
    basecase_only = False
    induction_only = False
    random_seed = None

    opts, args = getopt.getopt(engine[1:], "", ["nomem", "syn", "stbv", "stdt", "presat",
            "nopresat", "unroll", "nounroll", "dumpsmt2", "progress", "anybase",
            "basecase", "induction", "seed="])

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
        elif o == "--anybase":
            anybase = True
        elif o == "--basecase":
            if induction_only:
                job.error("smtbmc options --basecase and --induction are exclusive.")
            basecase_only = True
        elif o == "--induction":
            if basecase_only:
                job.error("smtbmc options --basecase and --induction are exclusive.")
            induction_only = True
        elif o == "--seed":
            random_seed = a
        else:
            job.error(f"Invalid smtbmc options {o}.")

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

    if job.opt_smtc is not None:
        smtbmc_opts += ["--smtc", f"src/{job.opt_smtc}"]

    if job.opt_tbtop is not None:
         smtbmc_opts += ["--vlogtb-top", job.opt_tbtop]

    model_name = "smt2"
    if syn_opt: model_name += "_syn"
    if nomem_opt: model_name += "_nomem"
    if stbv_opt: model_name += "_stbv"
    if stdt_opt: model_name += "_stdt"

    if mode == "prove":
        if not induction_only:
            run("prove_basecase", job, engine_idx, engine)
        if not basecase_only:
            run("prove_induction", job, engine_idx, engine)
        return

    taskname = f"engine_{engine_idx}"
    trace_prefix = f"engine_{engine_idx}/trace"
    logfile_prefix = f"{job.workdir}/engine_{engine_idx}/logfile"

    if mode == "prove_basecase":
        taskname += ".basecase"
        logfile_prefix += "_basecase"
        if anybase:
            smtbmc_opts.append("-g")

    if mode == "prove_induction":
        taskname += ".induction"
        trace_prefix += "_induct"
        logfile_prefix += "_induction"
        smtbmc_opts.append("-i")

    if mode == "cover":
        smtbmc_opts.append("-c")
        trace_prefix += "%"

    if dumpsmt2:
        smtbmc_opts += ["--dump-smt2", trace_prefix.replace("%", "") + ".smt2"]

    if not progress:
        smtbmc_opts.append("--noprogress")


    if job.opt_skip is not None:
        t_opt = "{}:{}".format(job.opt_skip, job.opt_depth)
    else:
        t_opt = "{}".format(job.opt_depth)

    random_seed = f"--info \"(set-option :random-seed {random_seed})\"" if random_seed else ""
    task = SbyTask(
        job,
        taskname,
        job.model(model_name),
        f"""cd {job.workdir}; {job.exe_paths["smtbmc"]} {" ".join(smtbmc_opts)} -t {t_opt} {random_seed} --append {job.opt_append} --dump-vcd {trace_prefix}.vcd --dump-vlogtb {trace_prefix}_tb.v --dump-smtc {trace_prefix}.smtc model/design_{model_name}.smt2""",
        logfile=open(logfile_prefix + ".txt", "w"),
        logstderr=(not progress)
    )

    if mode == "prove_basecase":
        job.basecase_tasks.append(task)

    if mode == "prove_induction":
        job.induction_tasks.append(task)

    task_status = None

    def output_callback(line):
        nonlocal task_status

        match = re.match(r"^## [0-9: ]+ Status: FAILED", line)
        if match:
            task_status = "FAIL"
            return line.replace("FAILED", "failed")

        match = re.match(r"^## [0-9: ]+ Status: PASSED", line)
        if match:
            task_status = "PASS"
            return line.replace("PASSED", "passed")

        match = re.match(r"^## [0-9: ]+ Status: PREUNSAT", line)
        if match:
            task_status = "ERROR"
            return line

        match = re.match(r"^## [0-9: ]+ Unexpected response from solver:", line)
        if match:
            task_status = "ERROR"
            return line

        return line

    def exit_callback(retcode):
        if task_status is None:
            job.error(f"engine_{engine_idx}: Engine terminated without status.")

        if mode == "bmc" or mode == "cover":
            job.update_status(task_status)
            task_status_lower = task_status.lower() if task_status == "PASS" else task_status
            job.log(f"engine_{engine_idx}: Status returned by engine: {task_status_lower}")
            job.summary.append(f"""engine_{engine_idx} ({" ".join(engine)}) returned {task_status_lower}""")

            if task_status == "FAIL" and mode != "cover":
                if os.path.exists(f"{job.workdir}/engine_{engine_idx}/trace.vcd"):
                    job.summary.append(f"counterexample trace: {job.workdir}/engine_{engine_idx}/trace.vcd")
            elif task_status == "PASS" and mode == "cover":
                print_traces_max = 5
                for i in range(print_traces_max):
                    if os.path.exists(f"{job.workdir}/engine_{engine_idx}/trace{i}.vcd"):
                        job.summary.append(f"trace: {job.workdir}/engine_{engine_idx}/trace{i}.vcd")
                    else:
                        break
                else:
                    excess_traces = 0
                    while os.path.exists(f"{job.workdir}/engine_{engine_idx}/trace{print_traces_max + excess_traces}.vcd"):
                        excess_traces += 1
                    if excess_traces > 0:
                        job.summary.append(f"""and {excess_traces} further trace{"s" if excess_traces > 1 else ""}""")

            job.terminate()

        elif mode in ["prove_basecase", "prove_induction"]:
            task_status_lower = task_status.lower() if task_status == "PASS" else task_status
            job.log(f"""engine_{engine_idx}: Status returned by engine for {mode.split("_")[1]}: {task_status_lower}""")
            job.summary.append(f"""engine_{engine_idx} ({" ".join(engine)}) returned {task_status_lower} for {mode.split("_")[1]}""")

            if mode == "prove_basecase":
                for task in job.basecase_tasks:
                    task.terminate()

                if not anybase:
                    if task_status == "PASS":
                        job.basecase_pass = True

                    else:
                        job.update_status(task_status)
                        if os.path.exists(f"{job.workdir}/engine_{engine_idx}/trace.vcd"):
                            job.summary.append(f"counterexample trace: {job.workdir}/engine_{engine_idx}/trace.vcd")
                        job.terminate()
                else:
                    if task_status == "PASS":
                        job.basecase_pass = True
                        if os.path.exists(f"{job.workdir}/engine_{engine_idx}/trace.vcd"):
                            job.summary.append(f"basecase trace: {job.workdir}/engine_{engine_idx}/trace.vcd")

                    else:
                        job.update_status(task_status)
                        job.terminate()

            elif mode == "prove_induction":
                for task in job.induction_tasks:
                    task.terminate()

                if task_status == "PASS":
                    job.induction_pass = True

            else:
                assert False

            if job.basecase_pass and job.induction_pass:
                job.update_status("PASS")
                job.summary.append("successful proof by k-induction.")
                job.terminate()

        else:
            assert False

    task.output_callback = output_callback
    task.exit_callback = exit_callback
