#!/usr/bin/env python3
from __future__ import annotations

import argparse
import asyncio
import json
import re
from pathlib import Path

def arg_parser():
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "btor_file",
        type=Path
    )

    parser.add_argument(
        "ywb_file",
        type=Path
    )

    parser.add_argument(
        "-d", "--dest",
        dest="dest",
        required=False,
        type=Path
    )

    return parser

def fix_path(path: str) -> list[str]:
    if path[0] == '$':
        fixed = [path]
    else:
        fixed = [f"\\{s}" for s in path.replace('[','.[').split('.')]
    return fixed

async def main() -> None:
    args = arg_parser().parse_args()

    work_dir: Path = args.dest or Path()

    proc = await asyncio.create_subprocess_shell(
        f"btor2aiger {args.btor_file}",
        stdout=asyncio.subprocess.PIPE
    )

    data = True

    # output aig
    aig_file = work_dir / "design_aiger.aig"
    aigf = open(aig_file, mode="wb")
    data = await proc.stdout.readline()
    aig_header = data.decode()
    while data:
        aigf.write(data)
        data = await proc.stdout.readline()
        if b'i0' in data:
            break
    end_pos = data.find(b'i0')
    aigf.write(data[:end_pos])
    aigf.close()

    # initialize yw aiger map
    aig_MILOA = aig_header.split()
    ywa = {
        "version": "Yosys Witness Aiger map",
        "generator": "btor2aig_yw.py",
        "latch_count": int(aig_MILOA[3]),
        "input_count": int(aig_MILOA[2]),
        "clocks": [],
        "inputs": [],
        "seqs": [],
        "inits": [],
        "latches": [],
        "asserts": [],
        "assumes": []
    }

    # output aim & build ywa
    aim_file = work_dir / "design_aiger.aim"
    aimf = open(aim_file, mode="w")
    data = data[end_pos:]
    while data:
        # decode data
        string = data.decode().rstrip()
        pattern = r"(?P<type>[cil])(?P<input>\d+) (?P<path>.*?)(\[(?P<offset>\d+)\])?$"
        m = re.match(pattern, string)
        md = m.groupdict()
        md['input'] = int(md['input'])
        if md['type'] == 'i':
            md['type'] = 'input'
        elif md['type'] == 'c':
            md['type'] = 'clk'
        elif md['type'] == 'l':
            md['type'] = 'latch'
            md['input'] += ywa['input_count']
        else:
            raise ValueError(f"Unknown type identifier {md['type']!r}")
        for k in ['input', 'offset']:
            if md[k]:
                md[k] = int(md[k])
            else:
                md[k] = 0

        # output to aim
        if md['type'] in ['input', 'latch']:
            print("{type} {input} {offset} {path}".format(**md), file=aimf)

        # update ywa
        md_type = md.pop('type')
        md['path'] = fix_path(md['path'])
        if md_type == 'clk':
            md['edge'] = "posedge" # always?
            ywa['clocks'].append(md)
        elif md_type == 'input':
            ywa['inputs'].append(md)
        elif md_type == 'latch':
            ywa['inits'].append(md)

        # get next line
        data = await proc.stdout.readline()
    aimf.close()

    with open(args.ywb_file, mode='r') as f:
        data = json.load(f)
        ywa['asserts'].extend(data['asserts'])
        ywa['assumes'].extend(data['assumes'])


    with open(work_dir / "design_aiger.ywa", mode="w") as f:
        json.dump(ywa, f, indent=2)

if __name__ == "__main__":
    asyncio.run(main())
