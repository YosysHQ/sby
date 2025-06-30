import os
from pathlib import Path
import sys

def main():
    workdir, task = sys.argv[1:]
    src = Path(workdir) / "src"
    for srcfile in src.iterdir():
        assert(srcfile.is_symlink() == (task == "link"))
    run_counter = src.resolve().parent.parent / task
    try:
        count = run_counter.stat().st_size
        assert(count<10)
    except FileNotFoundError:
        count = 0
    with open(run_counter, 'a') as f:
        print(count, file=f)

if __name__ == "__main__":
    main()
