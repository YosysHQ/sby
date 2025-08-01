from pathlib import Path
import sys

def main():
    workdir, task = sys.argv[1:]
    src = Path(workdir) / "src"
    count = 0
    for srcfile in src.iterdir():
        if srcfile.name == "heredoc":
            assert(not srcfile.is_symlink())
            with open(srcfile, "r") as f:
                local_contents = f.readline()
                assert(local_contents.strip() == 'log foo')
        else:
            assert(srcfile.is_symlink() == (task == "link"))
            assert(srcfile.name != "script.ys")
        count += 1
    assert(count == 4)
    script_ys = src / "dir" / "script.ys"
    assert(script_ys.exists())

if __name__ == "__main__":
    main()
