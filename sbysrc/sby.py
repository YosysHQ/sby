#!/usr/bin/env python3
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

import os, sys, shutil, tempfile
##yosys-sys-path##
from sby_core import SbyJob, SbyAbort
from time import localtime
import argparse

parser = argparse.ArgumentParser(
    description="SymbiYosys (sby) -- Front-end for Yosys-based formal verification flows."
)

parser.add_argument(
    "sbyfile", default=None, type=str, metavar="<jobname>.sby", help="sby job file"
)
parser.add_argument(
    "tasks", default=[None], type=str, nargs="*", metavar="task", help="tasks to run"
)
parser.add_argument(
    "-d",
    default=None,
    type=str,
    metavar="dir",
    help="set workdir name. default: <jobname> (without .sby)",
)
parser.add_argument(
    "-f", action="store_true", default=False, help="remove workdir if it already exists"
)
parser.add_argument(
    "-b", action="store_true", default=False, help="backup workdir if it already exists"
)
parser.add_argument(
    "-t",
    action="store_true",
    default=False,
    help="run in a temporary workdir (remove when finished)",
)
# NOTE: Depreciated argument, use positional task argument instead
# parser.add_argument(
#     '-T',
#     default=[],
#     nargs='+',
#     metavar='task',
#     help='add taskname (useful when sby file is read from stdin)'
# )
parser.add_argument(
    "-E",
    action="store_true",
    default=False,
    help="throw an exception (incl stack trace) for most errors",
)

exe_group = parser.add_argument_group(
    title="executable paths",
    description="configure which executable to use for the respective tool",
)

exe_group.add_argument("--yosys", default="yosys", metavar="<path>")
exe_group.add_argument("--abc", default="yosys-abc", metavar="<path>")
exe_group.add_argument("--smtbmc", default="yosys-smtbmc", metavar="<path>")
exe_group.add_argument("--suprove", default="suprove", metavar="<path>")
exe_group.add_argument("--aigbmc", default="aigbmc", metavar="<path>")
exe_group.add_argument("--avy", default="avy", metavar="<path>")
exe_group.add_argument("--btormc", default="btormc", metavar="<path>")

parser.add_argument(
    "--dumpcfg",
    action="store_true",
    default=False,
    help="print the pre-processed configuration file",
)
parser.add_argument(
    "--dumptasks", action="store_true", default=False, help="print the list of tasks"
)
parser.add_argument(
    "--setup",
    action="store_true",
    default=False,
    help="set up the working directory and exit",
)

args = parser.parse_args()

sbyfile = args.sbyfile
workdir = args.d
tasknames = args.tasks
opt_force = args.f
opt_backup = args.b
opt_tmpdir = args.t
throw_err = args.E
dump_cfg = args.dumpcfg
dump_tasks = args.dumptasks
reusedir = False
setupmode = args.setup

# add args to exe_paths dictionary
exe_paths = dict()
exe_paths["yosys"] = args.yosys
exe_paths["abc"] = args.abc
exe_paths["smtbmc"] = args.smtbmc
exe_paths["suprove"] = args.suprove
exe_paths["aigbmc"] = args.aigbmc
exe_paths["avy"] = args.avy
exe_paths["btormc"] = args.btormc

if os.path.isdir(sbyfile):
    workdir = sbyfile
    sbyfile += "/config.sby"
    reusedir = True
    if not opt_force and os.path.exists(workdir + "/model"):
        print("ERROR: Use -f to re-run in existing directory.", file=sys.stderr)
        sys.exit(1)
    if len(tasknames) > 1:
        print("ERROR: Can't use tasks when running in existing directory.", file=sys.stderr)
        sys.exit(1)
    if setupmode:
        print("ERROR: Can't use --setup with existing directory.", file=sys.stderr)
        sys.exit(1)
    if opt_force:
        for f in "PASS FAIL UNKNOWN ERROR TIMEOUT".split():
            if os.path.exists(workdir + "/" + f):
                os.remove(workdir + "/" + f)
elif not sbyfile.endswith(".sby"):
    print("ERROR: Sby file does not have .sby file extension.", file=sys.stderr)
    sys.exit(1)

early_logmsgs = list()


def early_log(workdir, msg):
    tm = localtime()
    early_logmsgs.append("SBY %2d:%02d:%02d [%s] %s" % (tm.tm_hour, tm.tm_min, tm.tm_sec, workdir, msg))
    print(early_logmsgs[-1])


def read_sbyconfig(sbydata, taskname):
    cfgdata = list()
    tasklist = list()

    pycode = None
    tasks_section = False
    task_tags_active = set()
    task_tags_all = set()
    task_skip_block = False
    task_skiping_blocks = False

    def handle_line(line):
        nonlocal pycode, tasks_section, task_tags_active, task_tags_all
        nonlocal task_skip_block, task_skiping_blocks

        line = line.rstrip("\n")
        line = line.rstrip("\r")

        if pycode is not None:
            if line == "--pycode-end--":
                gdict = globals().copy()
                gdict["task"] = taskname
                gdict["tags"] = set(task_tags_active)
                gdict["output_lines"] = list()
                exec("def output(line):\n  output_lines.append(line)\n" + pycode, gdict)
                pycode = None
                for line in gdict["output_lines"]:
                    handle_line(line)
                return
            pycode += line + "\n"
            return

        if line == "--pycode-begin--":
            pycode = ""
            return

        if tasks_section and line.startswith("["):
            tasks_section = False

        if task_skiping_blocks:
            if line == "--":
                task_skip_block = False
                task_skiping_blocks = False
                return

        found_task_tag = False
        task_skip_line = False

        for t in task_tags_all:
            if line.startswith(t+":"):
                line = line[len(t)+1:].lstrip()
                match = t in task_tags_active
            elif line.startswith("~"+t+":"):
                line = line[len(t)+2:].lstrip()
                match = t not in task_tags_active
            else:
                continue

            if line == "":
                task_skiping_blocks = True
                task_skip_block = not match
                task_skip_line = True
            else:
                task_skip_line = not match

            found_task_tag = True
            break

        if len(task_tags_all) and not found_task_tag:
            tokens = line.split()
            if len(tokens) > 0 and tokens[0][0] == line[0] and tokens[0].endswith(":"):
                print("ERROR: Invalid task specifier \"%s\"." % tokens[0], file=sys.stderr)
                sys.exit(1)

        if task_skip_line or task_skip_block:
            return

        if tasks_section:
            if taskname is None:
                cfgdata.append(line)
            if line.startswith("#"):
                return
            line = line.split()
            if len(line) > 0:
                tasklist.append(line[0])
            for t in line:
                if taskname == line[0]:
                    task_tags_active.add(t)
                task_tags_all.add(t)

        elif line == "[tasks]":
            if taskname is None:
                cfgdata.append(line)
            tasks_section = True

        else:
            cfgdata.append(line)

    for line in sbydata:
        handle_line(line)

    return cfgdata, tasklist


sbydata = list()
with (open(sbyfile, "r") if sbyfile is not None else sys.stdin) as f:
    for line in f:
        sbydata.append(line)

if dump_cfg:
    assert len(tasknames) < 2
    sbyconfig, _ = read_sbyconfig(sbydata, tasknames[0] if len(tasknames) else None)
    print("\n".join(sbyconfig))
    sys.exit(0)

if len(tasknames) == 0:
    _, tasknames = read_sbyconfig(sbydata, None)
    if len(tasknames) == 0:
        tasknames = [None]

if dump_tasks:
    for task in tasknames:
        if task is not None:
            print(task)
    sys.exit(0)

if (workdir is not None) and (len(tasknames) != 1):
    print("ERROR: Exactly one task is required when workdir is specified.", file=sys.stderr)
    sys.exit(1)


def run_job(taskname):
    my_workdir = workdir
    my_opt_tmpdir = opt_tmpdir

    if my_workdir is None and sbyfile is not None and not my_opt_tmpdir:
        my_workdir = sbyfile[:-4]
        if taskname is not None:
            my_workdir += "_" + taskname

    if my_workdir is not None:
        if opt_backup:
            backup_idx = 0
            while os.path.exists("%s.bak%03d" % (my_workdir, backup_idx)):
                backup_idx += 1
            early_log(my_workdir, "Moving direcory '%s' to '%s'." % (my_workdir, "%s.bak%03d" % (my_workdir, backup_idx)))
            shutil.move(my_workdir, "%s.bak%03d" % (my_workdir, backup_idx))

        if opt_force and not reusedir:
            early_log(my_workdir, "Removing direcory '%s'." % (my_workdir))
            if sbyfile:
                shutil.rmtree(my_workdir, ignore_errors=True)

        if reusedir:
            pass
        elif os.path.isdir(my_workdir):
            print("ERROR: Direcory '%s' already exists." % (my_workdir))
            sys.exit(1)
        else:
            os.makedirs(my_workdir)

    else:
        my_opt_tmpdir = True
        my_workdir = tempfile.mkdtemp()

    junit_ts_name = os.path.basename(sbyfile[:-4]) if sbyfile is not None else workdir if workdir is not None else "stdin"
    junit_tc_name = taskname if taskname is not None else "default"

    if reusedir:
        junit_filename = os.path.basename(my_workdir)
    elif sbyfile is not None:
        junit_filename = os.path.basename(sbyfile[:-4])
        if taskname is not None:
            junit_filename += "_" + taskname
    elif taskname is not None:
        junit_filename = taskname
    else:
        junit_filename = "junit"

    sbyconfig, _ = read_sbyconfig(sbydata, taskname)
    job = SbyJob(sbyconfig, my_workdir, early_logmsgs, reusedir)

    for k, v in exe_paths.items():
        job.exe_paths[k] = v

    if throw_err:
        job.run(setupmode)
    else:
        try:
            job.run(setupmode)
        except SbyAbort:
            pass

    if my_opt_tmpdir:
        job.log("Removing direcory '%s'." % (my_workdir))
        shutil.rmtree(my_workdir, ignore_errors=True)

    if setupmode:
        job.log("SETUP COMPLETE (rc=%d)" % (job.retcode))
    else:
        job.log("DONE (%s, rc=%d)" % (job.status, job.retcode))
    job.logfile.close()

    if not my_opt_tmpdir and not setupmode:
        with open("%s/%s.xml" % (job.workdir, junit_filename), "w") as f:
            junit_errors = 1 if job.retcode == 16 else 0
            junit_failures = 1 if job.retcode != 0 and junit_errors == 0 else 0
            print('<?xml version="1.0" encoding="UTF-8"?>', file=f)
            print('<testsuites disabled="0" errors="%d" failures="%d" tests="1" time="%d">' % (junit_errors, junit_failures, job.total_time), file=f)
            print('<testsuite disabled="0" errors="%d" failures="%d" name="%s" skipped="0" tests="1" time="%d">' % (junit_errors, junit_failures, junit_ts_name, job.total_time), file=f)
            print('<properties>', file=f)
            print('<property name="os" value="%s"/>' % os.name, file=f)
            print('</properties>', file=f)
            print('<testcase classname="%s" name="%s" status="%s" time="%d">' % (junit_ts_name, junit_tc_name, job.status, job.total_time), file=f)
            if junit_errors:
                print('<error message="%s" type="%s"/>' % (job.status, job.status), file=f)
            if junit_failures:
                print('<failure message="%s" type="%s"/>' % (job.status, job.status), file=f)
            print('<system-out>', end="", file=f)
            with open("%s/logfile.txt" % (job.workdir), "r") as logf:
                for line in logf:
                    print(line.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("\"", "&quot;"), end="", file=f)
            print('</system-out></testcase></testsuite></testsuites>', file=f)
        with open("%s/status" % (job.workdir), "w") as f:
            print("%s %d %d" % (job.status, job.retcode, job.total_time), file=f)

    return job.retcode


retcode = 0
for t in tasknames:
    retcode |= run_job(t)

sys.exit(retcode)
