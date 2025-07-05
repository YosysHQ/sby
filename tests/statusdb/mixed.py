import json
import sqlite3
import sys

def get_prop_type(prop: str):
    prop = json.loads(prop or "[]")
    name_parts = prop[-1].split("_")
    if name_parts[0] == "\check":
        # read_verilog style
        # \check_cover_mixed_v...
        return name_parts[1]
    else:
        # verific style
        # \assert_auto_verificsva_cc...
        return name_parts[0][1:]

def main():
    workdir = sys.argv[1]
    with open(f"{workdir}/status.path", "r") as status_path_file:
        status_path = f"{workdir}/{status_path_file.read().rstrip()}"
    # read only database
    con = sqlite3.connect(f"file:{status_path}?mode=ro", uri=True)
    db = con.cursor()
    # custom sql to get all task property statuses for the current workdir
    rows = db.execute(
        """
            SELECT task.id, task_property.name, task_property.src, task_property_status.status
            FROM task
            LEFT JOIN task_property ON task_property.task=task.id
            LEFT JOIN task_property_status ON task_property_status.task_property=task_property.id
            WHERE task.workdir=:workdir;
        """,
        {"workdir": workdir}
    ).fetchall()
    # only check the most recent iteration of the test
    last_id = 0
    for row_id, _, _, _ in rows:
        if row_id > last_id:
            last_id = row_id
    for row_id, prop, src, status in rows:
        if row_id != last_id:
            continue
        prop_type = get_prop_type(prop)
        valid_status: list[None|str] = []
        if workdir in ["mixed_bmc", "mixed_assert"] and prop_type == "assert":
            valid_status = ["FAIL"]
        elif workdir == "mixed_bmc" and prop_type == "cover":
            valid_status = [None, "UNKNOWN"]
        elif workdir == "mixed_assert" and prop_type == "cover":
            valid_status = ["PASS", None, "UNKNOWN"]
        elif workdir == "mixed_no_assert" and prop_type == "assert":
            valid_status = [None, "UNKNOWN"]
        elif workdir == "mixed_no_assert" and prop_type == "cover":
            valid_status = ["PASS"]
        assert status in valid_status, f"Unexpected {prop_type} status {status} for {prop} ({src})"
        

if __name__ == "__main__":
    main()
