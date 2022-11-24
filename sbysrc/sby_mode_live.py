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

import re, os, getopt, click
from sby_core import SbyProc

def run(task):
    task.handle_str_option("aigsmt", "yices")

    task.status = "UNKNOWN"

    for engine_idx, engine in task.engine_list():
        task.log(f"{click.style(f'engine_{engine_idx}', fg='magenta')}: {' '.join(engine)}")
        task.makedirs(f"{task.workdir}/engine_{engine_idx}")

        if engine[0] == "aiger":
            import sby_engine_aiger
            sby_engine_aiger.run("live", task, engine_idx, engine)

        elif engine[0] == "none":
            pass

        else:
            task.error(f"Invalid engine '{engine[0]}' for live mode.")
