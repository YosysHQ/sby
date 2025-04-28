import sys
import os
import subprocess
import json
import shlex
import argparse
from pathlib import Path

from required_tools import REQUIRED_TOOLS

parser = argparse.ArgumentParser()
parser.add_argument("--rule", required=True)
parser.add_argument("--source", required=True)
args = parser.parse_args()


def unix_path(path):
    source_path = "/".join(path.parts)
    if source_path.startswith("//"):
        source_path = source_path[1:]
    return source_path


sby_file = Path(args.source)
rules_file = Path(args.rule)
rules_base = rules_file.parent.parts[3:]
sby_dir = sby_file.parent


taskinfo = json.loads(
    subprocess.check_output(
        [sys.executable, os.getenv("SBY_MAIN"), "--dumptaskinfo", sby_file.name],
        cwd=sby_dir,
    )
)


def parse_engine(engine):
    engine, *args = engine
    default_solvers = {"smtbmc": "yices"}
    for arg in args:
        if not arg.startswith("-"):
            return engine, arg
    return engine, default_solvers.get(engine)


rules_file.parent.mkdir(exist_ok=True, parents=True)

with rules_file.open("w") as rules:
    name = unix_path(sby_dir / sby_file.stem)
    rule_name = "/".join(rules_base) + f"/{sby_file.stem}"

    for task, info in taskinfo.items():
        target = name
        rule_target = rule_name
        workdirname = sby_file.stem
        if task:
            target += f"_{task}"
            rule_target += f"_{task}"
            workdirname += f"_{task}"

        engines = set()
        solvers = set()
        engine_solvers = set()

        required_tools = set()

        for mode_engines in info["engines"].values():
            for engine in mode_engines:
                engine, solver = parse_engine(engine)
                engines.add(engine)
                required_tools.update(
                    REQUIRED_TOOLS.get((engine, solver), REQUIRED_TOOLS.get(engine, ()))
                )
                if solver:
                    solvers.add(solver)
                    engine_solvers.add((engine, solver))

        if any(
            line.startswith("read -verific") or line.startswith("verific")
            for line in info["script"]
        ):
            required_tools.add("verific")

        required_tools = sorted(required_tools)

        print(f".PHONY: {rule_target}", file=rules)
        print(f"{rule_target}:", file=rules)

        shell_script = sby_dir / f"{sby_file.stem}.sh"

        sby_dir_unix = unix_path(sby_dir)

        if shell_script.exists():
            command = f"cd {sby_dir_unix} && env SBY_FILE={sby_file.name} WORKDIR={workdirname} TASK={task} bash {shell_script.name}"
        else:
            command = (
                f"cd {sby_dir_unix} && python3 $(SBY_MAIN) -f {sby_file.name} {task}"
            )

        print(
            f"\t+@python3 make/required_tools.py run {target} {shlex.quote(command)} {shlex.join(required_tools)}",
            file=rules,
        )

        print(f".PHONY: clean-{rule_target}", file=rules)
        print(f"clean-{rule_target}:", file=rules)
        print(f"\trm -rf {target}", file=rules)

        test_groups = []

        mode = info["mode"]

        test_groups.append(f"test_m_{mode}")

        for engine in sorted(engines):
            test_groups.append(f"test_e_{engine}")
            test_groups.append(f"test_m_{mode}_e_{engine}")

        for solver in sorted(solvers):
            test_groups.append(f"test_s_{solver}")
            test_groups.append(f"test_m_{mode}_s_{solver}")

        for engine, solver in sorted(engine_solvers):
            test_groups.append(f"test_e_{engine}_s_{solver}")
            test_groups.append(f"test_m_{mode}_e_{engine}_s_{solver}")

        prefix = ""

        for part in [*rules_base, ""]:
            print(f".PHONY: {prefix}clean {prefix}test", file=rules)
            print(f"{prefix}clean: clean-{rule_target}", file=rules)
            print(f"{prefix}test: {rule_target}", file=rules)

            for test_group in test_groups:
                print(f".PHONY: {prefix}{test_group}", file=rules)
                print(f"{prefix}{test_group}: {rule_target}", file=rules)
            prefix += f"{part}/"

    tasks = [task for task in taskinfo.keys() if task]

    if tasks:
        print(f".PHONY: {rule_name}", file=rules)
        print(f"{rule_name}:", *(f"{rule_name}_{task}" for task in tasks), file=rules)
