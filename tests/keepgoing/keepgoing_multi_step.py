import sys
from check_output import *

src = "keepgoing_multi_step.sv"

workdir = sys.argv[1]

assert_0 = line_ref(workdir, src, "assert(0)")
step_3_7 = line_ref(workdir, src, "step 3,7")
step_5 = line_ref(workdir, src, "step 5")
step_7 = line_ref(workdir, src, "step 7")

log = open(workdir + "/logfile.txt").read()

if "_abc]" not in log:
    log_per_trace = log.split("Writing trace to Yosys witness file")[:-1]
    assert len(log_per_trace) == 4
    assert re.search(r"Assert failed in test: %s \(.*\)$" % assert_0, log_per_trace[0], re.M)

    for i in range(1, 4):
        assert re.search(r"Assert failed in test: %s \(.*\) \[failed before\]$" % assert_0, log_per_trace[i], re.M)


    assert re.search(r"Assert failed in test: %s \(.*\)$" % step_3_7, log_per_trace[1], re.M)
    assert re.search(r"Assert failed in test: %s \(.*\)$" % step_5, log_per_trace[2], re.M)
    assert re.search(r"Assert failed in test: %s \(.*\) \[failed before\]$" % step_3_7, log_per_trace[3], re.M)
    assert re.search(r"Assert failed in test: %s \(.*\)$" % step_7, log_per_trace[3], re.M)

    pattern = f"Property ASSERT in test at {assert_0} failed. Trace file: engine_0/trace0.(vcd|fst)"
    assert re.search(pattern, open(f"{workdir}/{workdir}.xml").read())

log_per_trace = log.split("summary: counterexample trace")[1:]
assert len(log_per_trace) == 4

for i in range(4):
    assert re.search(r"failed assertion test\..* at %s" % assert_0, log_per_trace[i], re.M)

step_3_7_traces = [i for i, t in enumerate(log_per_trace) if re.search(r"failed assertion test\..* at %s" % step_3_7, t, re.M)]
step_5_traces = [i for i, t in enumerate(log_per_trace) if re.search(r"failed assertion test\..* at %s" % step_5, t, re.M)]
step_7_traces = [i for i, t in enumerate(log_per_trace) if re.search(r"failed assertion test\..* at %s" % step_7, t, re.M)]

assert len(step_3_7_traces) == 2
assert len(step_5_traces) == 1
assert len(step_7_traces) == 1
