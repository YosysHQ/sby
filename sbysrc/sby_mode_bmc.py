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

def init(job):
    job.handle_int_option("depth", 20)
    job.handle_int_option("append", 0)
    job.handle_str_option("aigsmt", "yices")

    for engine_idx in range(len(job.engines)):
        engine = job.engines[engine_idx]
        assert len(engine) > 0

        job.log("engine_{}: {}".format(engine_idx, " ".join(engine)))
        job.makedirs("{}/engine_{}".format(job.workdir, engine_idx))

        if engine[0] == "smtbmc":
            import sby_engine_smtbmc
            sby_engine_smtbmc.init("bmc", job, engine_idx, engine)

        elif engine[0] == "abc":
            import sby_engine_abc
            sby_engine_abc.init("bmc", job, engine_idx, engine)

        elif engine[0] == "btor":
            import sby_engine_btor
            sby_engine_btor.init("bmc", job, engine_idx, engine)

        else:
            job.error("Invalid engine '{}' for bmc mode.".format(engine[0]))
