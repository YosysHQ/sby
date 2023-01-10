import sys
from check_output import *

workdir = sys.argv[1]
src = "keepgoing_same_step.sv"

assert_a = line_ref(workdir, src, "assert(a)")
assert_not_a = line_ref(workdir, src, "assert(!a)")
assert_0 = line_ref(workdir, src, "assert(0)")

log = open(workdir + "/logfile.txt").read()
log_per_trace = log.split("Writing trace to Yosys witness file")[:-1]

assert len(log_per_trace) == 2

assert re.search(r"Assert failed in test: %s \(.*\)$" % assert_a, log, re.M)
assert re.search(r"Assert failed in test: %s \(.*\)$" % assert_not_a, log, re.M)
assert re.search(r"Assert failed in test: %s \(.*\)$" % assert_0, log_per_trace[0], re.M)
assert re.search(r"Assert failed in test: %s \(.*\) \[failed before\]$" % assert_0, log_per_trace[1], re.M)
