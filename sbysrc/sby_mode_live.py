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

def run(job):
    job.handle_str_option("aigsmt", "yices")

    job.status = "UNKNOWN"

    for engine_idx in range(len(job.engines)):
        engine = job.engines[engine_idx]
        assert len(engine) > 0

        job.log("engine_{}: {}".format(engine_idx, " ".join(engine)))
        job.makedirs("{}/engine_{}".format(job.workdir, engine_idx))

        if engine[0] == "aiger":
            import sby_engine_aiger
            sby_engine_aiger.run("live", job, engine_idx, engine)

        else:
            job.error("Invalid engine '{}' for live mode.".format(engine[0]))
