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

import os, sys, getopt, shutil, tempfile
##yosys-sys-path##
from sby_core import SbyJob

sbyfile = None
workdir = None
opt_force = False
opt_backup = False
exe_paths = dict()

def usage():
    print("""
sby [options] [<jobname>.sby]

    -d <dirname>
        set workdir name. default: <jobname> (without .sby)

    -f
        remove workdir if it already exists

    -b
        backup workdir if it already exists

    --yosys <path_to_executable>
    --abc <path_to_executable>
    --smtbmc <path_to_executable>
    --suprove <path_to_executable>
    --aigbmc <path_to_executable>
    --avy <path_to_executable>
        configure which executable to use for the respective tool
""")
    sys.exit(1)

try:
    opts, args = getopt.getopt(sys.argv[1:], "d:bf", ["yosys=",
            "abc=", "smtbmc=", "suprove=", "aigbmc=", "avy="])
except:
    usage()

for o, a in opts:
    if o == "-d":
        workdir = a
    elif o == "-f":
        opt_force = True
    elif o == "-b":
        opt_backup = True
    elif o == "--yosys":
        exe_paths["yosys"] = a
    elif o == "--abc":
        exe_paths["abc"] = a
    elif o == "--smtbmc":
        exe_paths["smtbmc"] = a
    elif o == "--suprove":
        exe_paths["suprove"] = a
    elif o == "--aigbmc":
        exe_paths["aigbmc"] = a
    elif o == "--avy":
        exe_paths["avy"] = a
    else:
        usage()

if len(args) > 1:
    usage()

if len(args) == 1:
    sbyfile = args[0]
    assert sbyfile.endswith(".sby")

early_logmsgs = list()

def early_log(msg):
    early_logmsgs.append("SBY [%s] %s" % (workdir, msg))
    print(early_logmsgs[-1])

if workdir is None:
    if sbyfile:
        workdir = sbyfile[:-4]
    else:
        workdir = tempfile.mkdtemp()

if opt_backup:
    backup_idx = 0
    while os.path.exists("%s.bak%03d" % (workdir, backup_idx)):
        backup_idx += 1
    early_log("Moving direcory '%s' to '%s'." % (workdir, "%s.bak%03d" % (workdir, backup_idx)))
    shutil.move(workdir, "%s.bak%03d" % (workdir, backup_idx))

if opt_force:
    early_log("Removing direcory '%s'." % (workdir))
    if sbyfile:
        shutil.rmtree(workdir, ignore_errors=True)

if sbyfile:
    os.makedirs(workdir)

job = SbyJob(sbyfile, workdir, early_logmsgs)

for k, v in exe_paths.items():
    job.exe_paths[k] = v

job.run()

if not sbyfile:
    shutil.rmtree(workdir, ignore_errors=True)

sys.exit(job.retcode)

