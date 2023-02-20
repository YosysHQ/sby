#!/usr/bin/env python3
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

import argparse, json, os, sys, shutil, tempfile, re
##yosys-sys-path##
from sby_core import SbyConfig, SbyTask, SbyAbort, SbyTaskloop, process_filename, dress_message
from sby_jobserver import SbyJobClient, process_jobserver_environment
import time, platform, click

process_jobserver_environment()  # needs to be called early

class DictAction(argparse.Action):
    def __call__(self, parser, namespace, values, option_string=None):
        assert isinstance(getattr(namespace, self.dest), dict), f"Use ArgumentParser.set_defaults() to initialize {self.dest} to dict()"
        name = option_string.lstrip(parser.prefix_chars).replace("-", "_")
        getattr(namespace, self.dest)[name] = values

parser = argparse.ArgumentParser(prog="sby",
        usage="%(prog)s [options] [<jobname>.sby [tasknames] | <dirname>]")
parser.set_defaults(exe_paths=dict())

parser.add_argument("-d", metavar="<dirname>", dest="workdir",
        help="set workdir name. default: <jobname> or <jobname>_<taskname>. When there is more than one task, use --prefix instead")
parser.add_argument("--prefix", metavar="<dirname>", dest="workdir_prefix",
        help="set the workdir name prefix. `_<taskname>` will be appended to the path for each task")
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
parser.add_argument("-j", metavar="<N>", type=int, dest="jobcount",
        help="maximum number of processes to run in parallel")
parser.add_argument("--sequential", action="store_true", dest="sequential",
        help="run tasks in sequence, not in parallel")

parser.add_argument("--autotune", action="store_true", dest="autotune",
        help="automatically find a well performing engine and engine configuration for each task")
parser.add_argument("--autotune-config", dest="autotune_config",
        help="read an autotune configuration file (overrides the sby file's autotune options)")

parser.add_argument("--yosys", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--abc", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--smtbmc", metavar="<path_to_executable>",
        action=DictAction, dest="exe_paths")
parser.add_argument("--witness", metavar="<path_to_executable>",
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
parser.add_argument("--dumptags", action="store_true", dest="dump_tags",
        help="print the list of task tags")
parser.add_argument("--dumptasks", action="store_true", dest="dump_tasks",
        help="print the list of tasks")
parser.add_argument("--dumpdefaults", action="store_true", dest="dump_defaults",
        help="print the list of default tasks")
parser.add_argument("--dumptaskinfo", action="store_true", dest="dump_taskinfo",
        help="output a summary of tasks as JSON")
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
workdir_prefix = args.workdir_prefix
if workdir is not None and workdir_prefix is not None:
    print("ERROR: -d and --prefix are mutually exclusive.", file=sys.stderr)
    sys.exit(1)
tasknames = args.arg_tasknames + args.tasknames
opt_force = args.force
opt_backup = args.backup
opt_tmpdir = args.tmpdir
exe_paths = args.exe_paths
throw_err = args.throw_err
dump_cfg = args.dump_cfg
dump_tags = args.dump_tags
dump_tasks = args.dump_tasks
dump_defaults = args.dump_defaults
dump_taskinfo = args.dump_taskinfo
dump_files = args.dump_files
reusedir = False
setupmode = args.setupmode
autotune = args.autotune
autotune_config = args.autotune_config
sequential = args.sequential
jobcount = args.jobcount
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
        config.write(f"""[options]
mode bmc

[engines]
smtbmc

[script]
read -formal {sv_file}
prep -top top

[files]
{sv_file}
""")

    print(f"sby config written to {sby_file}", file=sys.stderr)
    sys.exit(0)

early_logmsgs = list()

def early_log(workdir, msg):
    early_logmsgs.append(dress_message(workdir, msg))
    click.echo(early_logmsgs[-1])

def read_sbyconfig(sbydata, taskname):
    cfgdata = list()
    tasklist = list()
    defaultlist = None
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
        nonlocal defaultlist

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

        if not tasks_section:
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
                    print(f"ERROR: Invalid task specifier \"{tokens[0]}\".", file=sys.stderr)
                    sys.exit(1)

            if task_skip_line or task_skip_block:
                return

        if tasks_section:
            if taskname is None:
                cfgdata.append(line)
            if line.startswith("#"):
                return

            line = line.split(":")
            if len(line) == 1:
                line = line[0].split()
                if len(line) > 0:
                    lhs, rhs = line[:1], line[1:]
                else:
                    return
            elif len(line) == 2:
                lhs, rhs = line[0].split(), line[1].split()
            else:
                print("ERROR: Syntax error in tasks block.", file=sys.stderr)
                sys.exit(1)

            for tagname in rhs:
                if tagname == "default":
                    continue
                if all(map(lambda c: c not in "(?*.[]|)", tagname)):
                    task_tags_all.add(tagname)

            for tname in lhs:
                if all(map(lambda c: c not in "(?*.[]|)", tname)):
                    if tname not in tasklist:
                        tasklist.append(tname)
                    if "default" in rhs:
                        if defaultlist is None:
                            defaultlist = list()
                        if tname not in defaultlist:
                            defaultlist.append(tname)
                    task_tags_all.add(tname)

                if taskname is not None and re.fullmatch(tname, taskname):
                    task_matched = True
                    task_tags_active.add(tname)
                    for tagname in rhs:
                        if tagname == "default":
                            continue
                        if all(map(lambda c: c not in "(?*.[]|)", tagname)):
                            task_tags_active.add(tagname)
                        else:
                            for t in task_tags_all:
                                if re.fullmatch(tagname, t):
                                    task_tags_active.add(t)

        elif line == "[tasks]":
            if taskname is None:
                cfgdata.append(line)
            tasks_section = True

        else:
            cfgdata.append(line)

    for line in sbydata:
        handle_line(line)

    if taskname is not None and not task_matched:
        print(f"ERROR: Task name '{taskname}' didn't match any lines in [tasks].", file=sys.stderr)
        sys.exit(1)

    if defaultlist is None:
        defaultlist = tasklist

    return cfgdata, tasklist, defaultlist, sorted(list(task_tags_all))


sbydata = list()
with (open(sbyfile, "r") if sbyfile is not None else sys.stdin) as f:
    for line in f:
        sbydata.append(line)

if dump_cfg:
    assert len(tasknames) < 2
    sbyconfig, _, _, _ = read_sbyconfig(sbydata, tasknames[0] if len(tasknames) else None)
    print("\n".join(sbyconfig))
    sys.exit(0)

if dump_files:
    file_set = set()

    def find_files(taskname):
        sbyconfig, _, _, _ = read_sbyconfig(sbydata, taskname)

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

if dump_tags:
    _, _, _, tagnames = read_sbyconfig(sbydata, None)
    for tag in tagnames:
        print(tag)
    sys.exit(0)

if dump_tasks or dump_defaults or dump_tags:
    _, tasks, dtasks, tags = read_sbyconfig(sbydata, None)
    for name in tasks if dump_tasks else dtasks if dump_defaults else tags:
        if name is not None:
            print(name)
    sys.exit(0)

if dump_taskinfo:
    _, _, tasknames, _ = read_sbyconfig(sbydata, None)
    taskinfo = {}
    for taskname in tasknames or [None]:
        task_sbyconfig, _, _, _ = read_sbyconfig(sbydata, taskname)
        taskinfo[taskname or ""] = info = {}
        cfg = SbyConfig()
        cfg.parse_config(task_sbyconfig)
        taskinfo[taskname or ""] = {
            "mode": cfg.options.get("mode"),
            "engines": cfg.engines,
            "script": cfg.script,
        }
    print(json.dumps(taskinfo, indent=2))
    sys.exit(0)

if len(tasknames) == 0:
    _, _, tasknames, _ = read_sbyconfig(sbydata, None)
    if len(tasknames) == 0:
        tasknames = [None]

if (workdir is not None) and (len(tasknames) != 1):
    print("ERROR: Exactly one task is required when workdir is specified. Specify the task or use --prefix instead of -d.", file=sys.stderr)
    sys.exit(1)

# Check there are no files in this dir or any of its subdirs
def check_dirtree_empty_of_files(dir):
    list = os.listdir(dir)
    if list:
        for fn in list:
            child_dir = os.path.join(dir, fn)
            if os.path.isdir(child_dir) and check_dirtree_empty_of_files(child_dir):
                continue
            return False
    return True

def start_task(taskloop, taskname):
    sbyconfig, _, _, _ = read_sbyconfig(sbydata, taskname)

    my_opt_tmpdir = opt_tmpdir
    my_workdir = None

    if workdir is not None:
        my_workdir = workdir
    elif workdir_prefix is not None:
        if taskname is None:
            my_workdir = workdir_prefix
        else:
            my_workdir = workdir_prefix + "_" + taskname

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
            early_log(my_workdir, f"Removing directory '{os.path.abspath(my_workdir)}'.")
            if sbyfile:
                shutil.rmtree(my_workdir, ignore_errors=True)

        if reusedir:
            pass
        elif os.path.isdir(my_workdir) and not check_dirtree_empty_of_files(my_workdir):
            print(f"ERROR: Directory '{my_workdir}' already exists, use -f to overwrite the existing directory.")
            sys.exit(1)
        elif not os.path.isdir(my_workdir):
            os.makedirs(my_workdir)

    else:
        my_opt_tmpdir = True
        my_workdir = tempfile.mkdtemp()

    if os.getenv("SBY_WORKDIR_GITIGNORE"):
        with open(f"{my_workdir}/.gitignore", "w") as gitignore:
            print("*", file=gitignore)

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

    task = SbyTask(sbyconfig, my_workdir, early_logmsgs, reusedir, taskloop)

    for k, v in exe_paths.items():
        task.exe_paths[k] = v

    def exit_callback():
        if not autotune and not setupmode:
            task.summarize()
            task.write_summary_file()

        if my_opt_tmpdir:
            task.log(f"Removing directory '{my_workdir}'.")
            shutil.rmtree(my_workdir, ignore_errors=True)

        if setupmode:
            task.log(f"SETUP COMPLETE (rc={task.retcode})")
        else:
            task.log(f"DONE ({task.status}, rc={task.retcode})")
        task.logfile.close()

        if not my_opt_tmpdir and not setupmode and not autotune:
            with open("{}/{}.xml".format(task.workdir, junit_filename), "w") as f:
                task.print_junit_result(f, junit_ts_name, junit_tc_name, junit_format_strict=False)

            with open(f"{task.workdir}/status", "w") as f:
                print(f"{task.status} {task.retcode} {task.total_time}", file=f)

    task.exit_callback = exit_callback

    if not autotune:
        task.setup_procs(setupmode)
        task.task_local_abort = not throw_err

    return task

failed = []
retcode = 0

if jobcount is not None and jobcount < 1:
    print("ERROR: The -j option requires a positive number as argument")
    sys.exit(1)

# Autotune is already parallel, parallelizing it across tasks needs some more work
if autotune:
    sequential = True

if sequential:
    if autotune:
        jobclient = None  # TODO make autotune use a jobclient
    else:
        jobclient = SbyJobClient(jobcount)

    for taskname in tasknames:
        taskloop = SbyTaskloop(jobclient)
        try:
            task = start_task(taskloop, taskname)
        except SbyAbort:
            if throw_err:
                raise
            sys.exit(1)

        if autotune:
            from sby_autotune import SbyAutotune
            SbyAutotune(task, autotune_config).run()
        elif setupmode:
            task.exit_callback()
        else:
            taskloop.run()
        retcode |= task.retcode
        if task.retcode:
            failed.append(taskname)
else:
    jobclient = SbyJobClient(jobcount)
    taskloop = SbyTaskloop(jobclient)

    tasks = {}
    for taskname in tasknames:
        try:
            tasks[taskname] = start_task(taskloop, taskname)
        except SbyAbort:
            if throw_err:
                raise
            sys.exit(1)

    taskloop.run()

    for taskname, task in tasks.items():
        retcode |= task.retcode
        if task.retcode:
            failed.append(taskname)

if failed and (len(tasknames) > 1 or tasknames[0] is not None):
    click.echo(dress_message(None, click.style(f"The following tasks failed: {failed}", fg="red", bold=True)))

sys.exit(retcode)
