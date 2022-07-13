import shutil

REQUIRED_TOOLS = {
    ("smtbmc", "yices"): ["yices-smt2"],
    ("smtbmc", "z3"): ["z3"],
    ("smtbmc", "cvc4"): ["cvc4"],
    ("smtbmc", "cvc5"): ["cvc5"],
    ("smtbmc", "mathsat"): ["mathsat"],
    ("smtbmc", "boolector"): ["boolector"],
    ("smtbmc", "bitwuzla"): ["bitwuzla"],
    ("smtbmc", "abc"): ["yosys-abc"],
    ("aiger", "suprove"): ["suprove", "yices"],
    ("aiger", "avy"): ["avy", "yices"],
    ("aiger", "aigbmc"): ["aigbmc", "yices"],
    ("btor", "btormc"): ["btormc", "btorsim"],
    ("btor", "pono"): ["pono", "btorsim"],
    ("abc"): ["yices"],
}


def found_tools():
    with open("make/rules/found_tools") as found_tools_file:
        return [tool.strip() for tool in found_tools_file.readlines()]


if __name__ == "__main__":
    import subprocess
    import sys
    import os
    from pathlib import Path

    args = sys.argv[1:]

    if args and args[0] == "run":
        target, command, *required_tools = args[1:]

        with open("make/rules/found_tools") as found_tools_file:
            found_tools = set(tool.strip() for tool in found_tools_file.readlines())

        if 'verific' in required_tools:
            result = subprocess.run(["yosys", "-qp", "read -verific"], capture_output=True)
            if result.returncode:
                print()
                print(f"SKIPPING {target}: requires yosys with verific support")
                print()
                exit()
            required_tools.remove('verific')

        missing_tools = sorted(
            f"`{tool}`" for tool in required_tools if tool not in found_tools
        )
        if missing_tools:
            noskip = "NOSKIP" in os.environ.get("MAKEFLAGS", "")
            print()
            print(f"SKIPPING {target}: {', '.join(missing_tools)} not found")
            if noskip:
                print("NOSKIP was set, treating this as an error")
            print()
            exit(noskip)

        print(command, flush=True)
        exit(subprocess.call(command, shell=True, close_fds=False))

    found_tools = []
    check_tools = set()
    for tools in REQUIRED_TOOLS.values():
        check_tools.update(tools)

    for tool in sorted(check_tools):
        if not shutil.which(tool):
            continue

        if tool == "btorsim":
            error_msg = subprocess.run(
                ["btorsim", "--vcd"],
                capture_output=True,
                text=True,
            ).stderr
            if "invalid command line option" in error_msg:
                print(
                    "found `btorsim` binary is too old "
                    "to support the `--vcd` option, ignoring"
                )
                continue

        found_tools.append(tool)

    found_tools = "\n".join(found_tools + [""])

    try:
        with open("make/rules/found_tools") as found_tools_file:
            if found_tools_file.read() == found_tools:
                exit(0)
    except FileNotFoundError:
        pass

    Path("make/rules").mkdir(exist_ok=True)

    with open("make/rules/found_tools", "w") as found_tools_file:
        found_tools_file.write(found_tools)
