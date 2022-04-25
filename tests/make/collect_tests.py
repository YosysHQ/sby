from pathlib import Path
import re

tests = []
checked_dirs = []

SAFE_PATH = re.compile(r"^[a-zA-Z0-9_./]*$")

def collect(path):
    # don't pick up any paths that need escaping nor any sby workdirs
    if not SAFE_PATH.match(str(path)) or (path / "config.sby").exists():
        return

    checked_dirs.append(path)
    for entry in path.glob("*.sby"):
        filename = str(entry)
        if not SAFE_PATH.match(filename):
            continue
        if not re.match(r"^[a-zA-Z0-9_./]*$", filename):
            print(f"skipping {filename!r}, use only [a-zA-Z0-9_./] in filenames")
            continue
        tests.append(entry)
    for entry in path.glob("*"):
        if entry.is_dir():
            collect(entry)


collect(Path("."))

out_file = Path("make/rules/collect.mk")
out_file.parent.mkdir(exist_ok=True)

with out_file.open("w") as output:


    for checked_dir in checked_dirs:
        print(f"{out_file}: {checked_dir}", file=output)

    for test in tests:
        print(f"make/rules/test/{test}.mk: {test}", file=output)
        for ext in [".sh", ".py"]:
            script_file = test.parent / (test.stem + ext)
            if script_file.exists():
                print(f"make/rules/test/{test}.mk: {script_file}", file=output)
        print(f"make/rules/test/{test}.mk: make/test_rules.py", file=output)
    for test in tests:
        print(f"-include make/rules/test/{test}.mk", file=output)
