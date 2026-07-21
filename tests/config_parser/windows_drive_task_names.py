import subprocess
import sys


def run_sby(sby_main, config):
    return subprocess.run(
        [sys.executable, sby_main, "--dumptasks"],
        input=config,
        capture_output=True,
        text=True,
    )


def expect_drive_conflict(sby_main, tasks, drive_path):
    result = run_sby(
        sby_main,
        f"""[tasks]
{tasks}

[options]
mode prep

[files]
{drive_path}
""",
    )

    drive = drive_path[0]
    expected = (
        f'ERROR: Task or group name "{drive}" conflicts with Windows path '
        f'"{drive_path}". Rename the task or group.'
    )
    assert result.returncode == 1, result
    assert expected in result.stderr, result.stderr


def main():
    sby_main = sys.argv[1]

    expect_drive_conflict(sby_main, "C", r"C:\src\example.sv")
    expect_drive_conflict(sby_main, "task D", "D:/src/example.sv")

    result = run_sby(
        sby_main,
        """[tasks]
C

[options]
C: mode prep
""",
    )
    assert result.returncode == 0, result
    assert "C" in result.stdout.splitlines(), result.stdout


if __name__ == "__main__":
    main()
