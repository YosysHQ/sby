from pathlib import Path
import re

tests = []
checked_dirs = []

SAFE_PATH = re.compile(r"^[a-zA-Z0-9_./\\]*$")


def collect(path):
    # don't pick up any paths that need escaping nor any sby workdirs
    if (
        not SAFE_PATH.match(str(path))
        or (path / "config.sby").exists()
        or (path / "status.sqlite").exists()
    ):
        return

    checked_dirs.append(path)
    for entry in path.glob("*.sby"):
        filename = str(entry)
        if not SAFE_PATH.match(filename):
            print(f"skipping {filename!r}, use only [a-zA-Z0-9_./] in filenames")
            continue
        if entry.name.startswith("skip_"):
            continue
        tests.append(entry)
    for entry in path.glob("*"):
        if entry.is_dir():
            collect(entry)


def unix_path(path):
    return "/".join(path.parts)


collect(Path("."))
collect(Path("../docs/examples"))

out_file = Path("make/rules/collect.mk")
out_file.parent.mkdir(exist_ok=True)

with out_file.open("w") as output:

    for checked_dir in checked_dirs:
        print(f"{out_file}: {checked_dir}", file=output)

    for test in tests:
        test_unix = unix_path(test)
        print(f"make/rules/test/{test_unix}.mk: {test_unix}", file=output)
        for ext in [".sh", ".py"]:
            script_file = test.parent / (test.stem + ext)
            if script_file.exists():
                script_file_unix = unix_path(script_file)
                print(f"make/rules/test/{test_unix}.mk: {script_file_unix}", file=output)
        print(f"make/rules/test/{test_unix}.mk: make/test_rules.py", file=output)
    for test in tests:
        test_unix = unix_path(test)
        print(f"-include make/rules/test/{test_unix}.mk", file=output)
