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

import argparse, os, sys, shutil, tempfile, re
##yosys-sys-path##
from sby_core import SbyJob, SbyAbort, process_filename
from time import localtime

class DictAction(argparse.Action):
    def __call__(self, parser, namespace, values, option_string=None):
        assert isinstance(getattr(namespace, self.dest), dict), "Use ArgumentParser.set_defaults() to initialize {} to dict()".format(self.dest)
        name = option_string.lstrip(parser.prefix_chars).replace("-", "_")
        getattr(namespace, self.dest)[name] = values

parser = argparse.ArgumentParser(prog="sby",
        usage="%(prog)s [options] [<jobname>.sby [tasknames] | <dirname>]")
parser.set_defaults(exe_paths=dict())

parser.add_argument("-d", metavar="<dirname>", dest="workdir",
        help="set workdir name. default: <jobname> or <jobname>_<taskname>")
parser.add_argument("-f", action="store_true", dest="force",
        help="remove workdir if it already exists")
parser.add_argument("-b", action="store_true", dest="backup",
        help="backup workdir if it already exists")
parser.add_argument("-t", action="store_true", dest="tmpdir",
        help="run in a temporary workdir (remove when finished)")
parser.add_argument("-T", metavar="<taskname>", action="append", dest="tasknames", default=list(),
        help="add taskname (useful when sby file is read from stdin)")
parser.add_argument("-E", action="store_true", dest="throw_err",
        help="throw an exception (incl stack trace) for most errors")

parser.add_argument("--yosys", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--abc", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--smtbmc", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--suprove", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--aigbmc", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--avy", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--btormc", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--pono", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths",
        help="configure which executable to use for the respective tool")
parser.add_argument("--dumpcfg", action="store_true", dest="dump_cfg",
        help="print the pre-processed configuration file")
parser.add_argument("--dumptasks", action="store_true", dest="dump_tasks",
        help="print the list of tasks")
parser.add_argument("--dumpfiles", action="store_true", dest="dump_files",
        help="print the list of source files")
parser.add_argument("--setup", action="store_true", dest="setupmode",
        help="set up the working directory and exit")

parser.add_argument("--init-config-file", dest="init_config_file",
        help="create a default .sby config file")
parser.add_argument("sbyfile", metavar="<jobname>.sby | <dirname>", nargs="?",
        help=".sby file OR directory containing config.sby file")
parser.add_argument("arg_tasknames", metavar="tasknames", nargs="*",
        help="tasks to run (only valid when <jobname>.sby is used)")

args = parser.parse_args()

sbyfile = args.sbyfile
workdir = args.workdir
tasknames = args.arg_tasknames + args.tasknames
opt_force = args.force
opt_backup = args.backup
opt_tmpdir = args.tmpdir
exe_paths = args.exe_paths
throw_err = args.throw_err
dump_cfg = args.dump_cfg
dump_tasks = args.dump_tasks
dump_files = args.dump_files
reusedir = False
setupmode = args.setupmode
init_config_file = args.init_config_file

if sbyfile is not None:
    if os.path.isdir(sbyfile):
        if workdir is not None:
            print("ERROR: Can't use -d when running in existing directory.", file=sys.stderr)
            sys.exit(1)
        workdir = sbyfile
        sbyfile += "/config.sby"
        reusedir = True
        if not opt_force and os.path.exists(workdir + "/model"):
            print("ERROR: Use -f to re-run in existing directory.", file=sys.stderr)
            sys.exit(1)
        if tasknames:
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

elif init_config_file is not None:
    sv_file = init_config_file + ".sv"
    sby_file = init_config_file + ".sby"
    with open(sby_file, 'w') as config:
        config.write("""[options]
mode bmc

[engines]
smtbmc

[script]
read -formal {0}
prep -top top

[files]
{0}
""".format(sv_file))

    print("sby config written to {}".format(sby_file), file=sys.stderr)
    sys.exit(0)

early_logmsgs = list()

def early_log(workdir, msg):
    tm = localtime()
    early_logmsgs.append("SBY {:2d}:{:02d}:{:02d} [{}] {}".format(tm.tm_hour, tm.tm_min, tm.tm_sec, workdir, msg))
    print(early_logmsgs[-1])

def read_sbyconfig(sbydata, taskname):
    cfgdata = list()
    tasklist = list()
    task_matched = False

    pycode = None
    tasks_section = False
    task_tags_active = set()
    task_tags_all = set()
    task_skip_block = False
    task_skiping_blocks = False

    def handle_line(line):
        nonlocal pycode, tasks_section, task_tags_active, task_tags_all
        nonlocal task_skip_block, task_skiping_blocks, task_matched

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
                print("ERROR: Invalid task specifier \"{}\".".format(tokens[0]), file=sys.stderr)
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
                tname = line[0]
                tpattern = False
                for c in tname:
                    if c in "(?*.[]|)":
                        tpattern = True
                if not tpattern:
                    tasklist.append(tname)
                    task_tags_all.add(tname)
                if taskname is not None and re.fullmatch(tname, taskname):
                    task_matched = True
                    task_tags_active.add(tname)
                    for t in line[1:]:
                        task_tags_active.add(t)
                        task_tags_all.add(t)
                else:
                    for t in line[1:]:
                        task_tags_all.add(t)

        elif line == "[tasks]":
            if taskname is None:
                cfgdata.append(line)
            tasks_section = True

        else:
            cfgdata.append(line)

    for line in sbydata:
        handle_line(line)

    if taskname is not None and not task_matched:
        print("ERROR: Task name '{}' didn't match any lines in [tasks].".format(taskname), file=sys.stderr)
        sys.exit(1)

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

if dump_files:
    file_set = set()

    def find_files(taskname):
        sbyconfig, _ = read_sbyconfig(sbydata, taskname)

        start_index = -1
        for i in range(len(sbyconfig)):
            if sbyconfig[i].strip() == "[files]":
                start_index = i
                break

        if start_index == -1:
            return

        for line in sbyconfig[start_index+1:]:
            line = line.strip()
            if line.startswith("["):
                break
            if line == "" or line.startswith("#"):
                continue
            filename = line.split()[-1]
            file_set.add(process_filename(filename))

    if len(tasknames):
        for taskname in tasknames:
            find_files(taskname)
    else:
        find_files(None)
    print("\n".join(file_set))
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
            while os.path.exists("{}.bak{:03d}".format(my_workdir, backup_idx)):
                backup_idx += 1
            early_log(my_workdir, "Moving directory '{}' to '{}'.".format(my_workdir, "{}.bak{:03d}".format(my_workdir, backup_idx)))
            shutil.move(my_workdir, "{}.bak{:03d}".format(my_workdir, backup_idx))

        if opt_force and not reusedir:
            early_log(my_workdir, "Removing directory '{}'.".format(my_workdir))
            if sbyfile:
                shutil.rmtree(my_workdir, ignore_errors=True)

        if reusedir:
            pass
        elif os.path.isdir(my_workdir):
            print("ERROR: Directory '{}' already exists.".format(my_workdir))
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
        job.log("Removing directory '{}'.".format(my_workdir))
        shutil.rmtree(my_workdir, ignore_errors=True)

    if setupmode:
        job.log("SETUP COMPLETE (rc={})".format(job.retcode))
    else:
        job.log("DONE ({}, rc={})".format(job.status, job.retcode))
    job.logfile.close()

    if not my_opt_tmpdir and not setupmode:
        with open("{}/{}.xml".format(job.workdir, junit_filename), "w") as f:
            junit_errors = 1 if job.retcode == 16 else 0
            junit_failures = 1 if job.retcode != 0 and junit_errors == 0 else 0
            print('<?xml version="1.0" encoding="UTF-8"?>', file=f)
            print('<testsuites disabled="0" errors="{}" failures="{}" tests="1" time="{}">'.format(junit_errors, junit_failures, job.total_time), file=f)
            print('<testsuite disabled="0" errors="{}" failures="{}" name="{}" skipped="0" tests="1" time="{}">'.format(junit_errors, junit_failures, junit_ts_name, job.total_time), file=f)
            print('<properties>', file=f)
            print('<property name="os" value="{}"/>'.format(os.name), file=f)
            print('</properties>', file=f)
            print('<testcase classname="{}" name="{}" status="{}" time="{}">'.format(junit_ts_name, junit_tc_name, job.status, job.total_time), file=f)
            if junit_errors:
                print('<error message="{}" type="{}"/>'.format(job.status, job.status), file=f)
            if junit_failures:
                print('<failure message="{}" type="{}"/>'.format(job.status, job.status), file=f)
            print('<system-out>', end="", file=f)
            with open("{}/logfile.txt".format(job.workdir), "r") as logf:
                for line in logf:
                    print(line.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("\"", "&quot;"), end="", file=f)
            print('</system-out></testcase></testsuite></testsuites>', file=f)
        with open("{}/status".format(job.workdir), "w") as f:
            print("{} {} {}".format(job.status, job.retcode, job.total_time), file=f)

    return job.retcode


retcode = 0
for t in tasknames:
    retcode |= run_job(t)

if retcode and (len(tasknames) > 1 or tasknames[0] is not None):
    tm = localtime()
    print("SBY {:2d}:{:02d}:{:02d} One or more tasks produced a non-zero return code.".format(tm.tm_hour, tm.tm_min, tm.tm_sec))

sys.exit(retcode)
