import os
from pathlib import Path
import sys

def main():
    workdir, task = sys.argv[1:]
    src = Path(workdir) / "src"
    for srcfile in src.iterdir():
        assert(srcfile.is_symlink() == (task == "link"))

if __name__ == "__main__":
    main()
