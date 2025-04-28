from pathlib import Path
import re
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("--output", required=True)
parser.add_argument("--examples")
parser.add_argument("--check", action='store_true')
args = parser.parse_args()

tests = []
checked_dirs = []

SAFE_PATH = re.compile(r"^[a-zA-Z0-9_./\\]*$")

out_file = Path(args.output)
header_line = f"# example dir = {args.examples}"

if args.check:
    try:
        with out_file.open("r") as f:
            found_header = f.readline().strip()
        if found_header != header_line:
            out_file.unlink()
    except FileNotFoundError:
        pass
    exit()

out_file.parent.mkdir(exist_ok=True)

def collect(path):
    # don't pick up any paths that need escaping nor any sby workdirs
    if (
        not SAFE_PATH.match(str(path))
        or (path / "config.sby").exists()
        or (path / "status.sqlite").exists()
        or (path / "config.mcy").exists()
        or path.name == "__pycache__"
        or path == out_file.parent
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
        if entry.with_suffix(".ivy").exists():
            continue
        tests.append(entry)
    for entry in path.glob("*"):
        if entry.is_dir():
            collect(entry)


def unix_path(path):
    source_path = "/".join(path.parts)
    if source_path.startswith("//"):
        source_path = source_path[1:]
    if args.examples:
        try:
            relative = path.relative_to(args.examples)
        except ValueError:
            pass
        else:
            if '..' not in relative.parts:
                return source_path, "examples/" + "/".join(relative.parts)
    if '..' in path.parts:
        raise RuntimeError("path escapes collect directories")
    return source_path, source_path


collect(Path('.'))
if args.examples:
    collect(Path(args.examples))

with out_file.open("w") as output:
    print(header_line, file=output)

    for checked_dir in checked_dirs:
        print(f"{out_file}: {checked_dir}", file=output)

    for test in tests:
        test_unix_source, test_unix_rule = unix_path(test)
        print(f"make/rules/test/{test_unix_rule}.mk: {test_unix_source}", file=output)
        for ext in [".sh", ".py"]:
            script_file = test.parent / (test.stem + ext)
            if script_file.exists():
                script_file_unix_source, script_file_unix_rule = unix_path(script_file)
                print(f"make/rules/test/{test_unix_rule}.mk: {script_file_unix_source}", file=output)
        print(f"make/rules/test/{test_unix_rule}.mk: make/test_rules.py", file=output)
    for test in tests:
        test_unix_source, test_unix_rule = unix_path(test)
        print(f"-include make/rules/test/{test_unix_rule}.mk", file=output)
