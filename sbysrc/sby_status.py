from __future__ import annotations

import sqlite3
import os
import time
import json
import click
import re
from collections import defaultdict
from functools import wraps
from pathlib import Path
from typing import Any, Callable, TypeVar, Optional, Iterable
from sby_design import SbyProperty, pretty_path


Fn = TypeVar("Fn", bound=Callable[..., Any])

SQLSCRIPT = """\
CREATE TABLE task (
    id INTEGER PRIMARY KEY,
    workdir TEXT,
    name TEXT,
    mode TEXT,
    created REAL
);
CREATE TABLE task_status (
    id INTEGER PRIMARY KEY,
    task INTEGER,
    status TEXT,
    data TEXT,
    created REAL,
    FOREIGN KEY(task) REFERENCES task(id)
);
CREATE TABLE task_property (
    id INTEGER PRIMARY KEY,
    task INTEGER,
    src TEXT,
    name TEXT,
    hdlname TEXT,
    kind TEXT,
    created REAL,
    FOREIGN KEY(task) REFERENCES task(id)
);
CREATE TABLE task_property_status (
    id INTEGER PRIMARY KEY,
    task_property INTEGER,
    task_trace INTEGER,
    status TEXT,
    data TEXT,
    created REAL,
    FOREIGN KEY(task_property) REFERENCES task_property(id),
    FOREIGN KEY(task_trace) REFERENCES task_trace(id)
);
CREATE TABLE task_trace (
    id INTEGER PRIMARY KEY,
    task INTEGER,
    trace TEXT,
    path TEXT,
    kind TEXT,
    engine_case TEXT,
    created REAL,
    FOREIGN KEY(task) REFERENCES task(id)
);"""

def transaction(method: Fn) -> Fn:
    @wraps(method)
    def wrapper(self: SbyStatusDb, *args: Any, **kwargs: Any) -> Any:
        if self.con.in_transaction:
            return method(self, *args, **kwargs)

        try:
            with self.con:
                self.log_debug(f"begin {method.__name__!r} transaction")
                self.db.execute("begin")
                result = method(self, *args, **kwargs)
        except Exception as err:
            self.log_debug(f"failed {method.__name__!r} transaction {err}")
            if not isinstance(err, sqlite3.OperationalError):
                raise
            if re.match(r"table \w+ has no column named \w+", err.args[0]):
                err.add_note("SBY status database can be reset with --statusreset")
                raise
        else:
            self.log_debug(f"comitted {method.__name__!r} transaction")
            return result

        try:
            with self.con:
                self.log_debug(
                    f"retrying {method.__name__!r} transaction once in immediate mode"
                )
                self.db.execute("begin immediate")
                result = method(self, *args, **kwargs)
        except Exception as err:
            self.log_debug(f"failed {method.__name__!r} transaction {err}")
            raise
        else:
            self.log_debug(f"comitted {method.__name__!r} transaction")
            return result

    return wrapper  # type: ignore

class FileInUseError(Exception):
    def __init__(self, *args, file: Path|str = "file"):
        super().__init__(f"Found {file}, try again later", *args)


class SbyStatusDb:
    def __init__(self, path: Path, task, timeout: float = 5.0, live_formats = []):
        self.debug = False
        self.task = task
        self.live_formats = live_formats

        self.con = sqlite3.connect(path, isolation_level=None, timeout=timeout)
        self.db = self.con.cursor()
        self.db.row_factory = sqlite3.Row
        err_count = 0
        err_max = 3
        while True:
            try:
                self.db.execute("PRAGMA journal_mode=WAL")
                self.db.execute("PRAGMA synchronous=0")
                self.db.execute("PRAGMA foreign_keys=ON")
            except sqlite3.OperationalError as err:
                if "database is locked" not in err.args[0]:
                    raise
                err_count += 1
                if err_count > err_max:
                    err.add_note(f"Failed to acquire lock after {err_count} attempts, aborting")
                    raise
                backoff = err_count / 10.0
                self.log_debug(f"Database locked, retrying in {backoff}s")
                time.sleep(backoff)
            else:
                break

        self._setup()

        if task is not None:
            self.start_time = time.time()
            self.task_id = self.create_task(workdir=task.workdir, name=task.name, mode=task.opt_mode, now=self.start_time)

    def log_debug(self, *args):
        if self.debug:
            if self.task:
                self.task.log(" ".join(str(arg) for arg in args))
            else:
                print(*args)

    @transaction
    def _setup(self):
        for statement in SQLSCRIPT.split(";\n"):
            statement = statement.strip().replace("CREATE TABLE", "CREATE TABLE IF NOT EXISTS")
            if statement:
                self.db.execute(statement)

    def test_schema(self) -> bool:
        schema = self.db.execute("SELECT sql FROM sqlite_master;").fetchall()
        schema_script = '\n'.join(str(sql[0] + ';') for sql in schema)
        self._tables = re.findall(r"CREATE TABLE (\w+) \(", schema_script)
        return schema_script != SQLSCRIPT

    @transaction
    def create_task(self, workdir: str, name: str, mode: str, now:float) -> int:
        return self.db.execute(
            """
                INSERT INTO task (workdir, name, mode, created)
                VALUES (:workdir, :name, :mode, :now)
            """,
            dict(workdir=workdir, name=name, mode=mode, now=now),
        ).lastrowid

    @transaction
    def create_task_properties(
        self, properties: Iterable[SbyProperty], *, task_id: Optional[int] = None
    ):
        if task_id is None:
            task_id = self.task_id
        now = time.time()
        self.db.executemany(
            """
                INSERT INTO task_property (name, src, hdlname, task, kind, created)
                VALUES (:name, :src, :hdlname, :task, :kind, :now)
            """,
            [
                dict(
                    name=json.dumps(prop.path),
                    src=prop.location or "",
                    hdlname=prop.hdlname,
                    task=task_id,
                    kind=prop.kind,
                    now=now,
                )
                for prop in properties
            ],
        )

    @transaction
    def set_task_status(
        self,
        status: Optional[str] = None,
        data: Any = None,
    ):
        if status is None:
            status = property.status

        now = time.time()
        self.db.execute(
            """
                INSERT INTO task_status (
                    task, status, data, created
                )
                VALUES (
                    :task, :status, :data, :now
                )
            """,
            dict(
                task=self.task_id,
                status=status,
                data=json.dumps(data),
                now=now,
            ),
        )

    @transaction
    def set_task_property_status(
        self,
        property: SbyProperty,
        trace_id: Optional[int] = None,
        data: Any = None,
    ):
        now = time.time()
        self.db.execute(
            """
                INSERT INTO task_property_status (
                    task_property, task_trace, status, data, created
                )
                VALUES (
                    (SELECT id FROM task_property WHERE task = :task AND name = :name),
                    :trace_id, :status, :data, :now
                )
            """,
            dict(
                task=self.task_id,
                trace_id=trace_id,
                name=json.dumps(property.path),
                status=property.status,
                data=json.dumps(data),
                now=now,
            ),
        )

        if self.live_formats:
            row = self.get_status_data_joined(self.db.lastrowid)
            for fmt in self.live_formats:
                fmtline = format_status_data_fmtline(row, fmt)
                self.task.log(f"{click.style(fmt, fg='yellow')}: {fmtline}")
        
    @transaction
    def add_task_trace(
        self,
        trace: str,
        path: str,
        kind: str,
        engine_case: Optional[str] = None,
        task_id: Optional[int] = None,
    ):
        if task_id is None:
            task_id = self.task_id
        now = time.time()
        return self.db.execute(
            """
                INSERT INTO task_trace (
                    trace, task, path, engine_case, kind, created
                )
                VALUES (
                    :trace, :task, :path, :engine_case, :kind, :now
                )
            """,
            dict(
                trace=trace,
                task=task_id,
                path=path,
                engine_case=engine_case,
                kind=kind,
                now=now
            )
        ).lastrowid

    def all_tasks(self):
        rows = self.db.execute(
            """
                SELECT id, workdir, created FROM task
            """
        ).fetchall()

        return {row["id"]: dict(row) for row in rows}

    def all_tasks_status(self):
        rows = self.db.execute(
            """
                SELECT task.id, task.name, task.created,
                task_status.status, task_status.created as 'status_created'
                FROM task
                LEFT JOIN task_status ON task_status.task=task.id
            """
        ).fetchall()

        return {row["id"]: dict(row) for row in rows}

    def all_task_properties(self):
        rows = self.db.execute(
            """
                SELECT id, task, src, name, created FROM task_property
            """
        ).fetchall()

        def get_result(row):
            row = dict(row)
            row["name"] = tuple(json.loads(row.get("name", "[]")))
            return row

        return {row["id"]: get_result(row) for row in rows}

    def all_task_property_statuses(self):
        rows = self.db.execute(
            """
                SELECT id, task_property, status, data, created
                FROM task_property_status
            """
        ).fetchall()

        def get_result(row):
            row = dict(row)
            row["data"] = json.loads(row.get("data", "null"))
            return row

        return {row["id"]: get_result(row) for row in rows}

    def all_status_data(self):
        return (
            self.all_tasks(),
            self.all_task_properties(),
            self.all_task_property_statuses(),
        )

    @transaction
    def _reset(self):
        hard_reset = self.test_schema()
        # table names can't be parameters, so we need to use f-strings
        # but it is safe to use here because it comes from the regex "\w+"
        for table in self._tables:
            if hard_reset:
                self.log_debug(f"dropping {table}")
                self.db.execute(f"DROP TABLE {table}")
            else:
                self.log_debug(f"clearing {table}")
                self.db.execute(f"DELETE FROM {table}")
        if hard_reset:
            self._setup()

    def reset(self):
        self.db.execute("PRAGMA foreign_keys=OFF")
        self._reset()
        self.db.execute("PRAGMA foreign_keys=ON")

    def print_status_summary(self, latest: bool):
        tasks, task_properties, task_property_statuses = self.all_status_data()
        latest_task_ids = filter_latest_task_ids(tasks)
        properties = defaultdict(set)

        uniquify_paths = defaultdict(dict)

        def add_status(task_property, status):
            if latest and task_property["task"] not in latest_task_ids:
                return

            display_name = task_property["name"]
            if display_name[-1].startswith("$"):
                counters = uniquify_paths[task_property["src"]]
                counter = counters.setdefault(display_name[-1], len(counters) + 1)
                if task_property["src"]:
                    if counter < 2:
                        path_based = f"<unnamed at {task_property['src']}>"
                    else:
                        path_based = f"<unnamed #{counter} at {task_property['src']}>"
                else:
                    path_based = f"<unnamed #{counter}>"
                display_name = (*display_name[:-1], path_based)

            properties[display_name].add(status)

        for task_property in task_properties.values():
            add_status(task_property, "UNKNOWN")

        for status in task_property_statuses.values():
            task_property = task_properties[status["task_property"]]
            add_status(task_property, status["status"])

        for display_name, statuses in sorted(properties.items()):
            print(pretty_path(display_name), combine_statuses(statuses))

    def print_task_summary(self):
        tasks = self.all_tasks_status()
        task_status = defaultdict(set)
        for task in tasks.values():
            task_status[task["name"]].add(task["status"] or "UNKNOWN")
        for task_name, statuses in sorted(task_status.items()):
            print(task_name, combine_statuses(statuses))

    def get_status_data_joined(self, status_id: int):
        row = self.db.execute(
            """
                SELECT task.name as 'task_name', task.mode, task.workdir, task.created, task_property.kind,
                task_property.src as 'location', task_property.name, task_property.hdlname, task_property_status.status,
                task_property_status.data, task_property_status.created as 'status_created',
                task_property_status.id, task_trace.path, task_trace.kind as trace_kind
                FROM task
                INNER JOIN task_property ON task_property.task=task.id
                INNER JOIN task_property_status ON task_property_status.task_property=task_property.id
                LEFT JOIN task_trace ON task_property_status.task_trace=task_trace.id
                WHERE task_property_status.id=:status_id;
            """,
            dict(status_id=status_id)
        ).fetchone()
        return parse_status_data_row(row)

    def all_status_data_joined(self):
        rows = self.db.execute(
            """
                SELECT task.id as 'task_id', task.name as 'task_name', task.mode, task.workdir, task.created, task_property.kind,
                task_property.src as 'location', task_property.name, task_property.hdlname, task_property_status.status,
                task_property_status.data, task_property_status.created as 'status_created',
                task_property_status.id, task_trace.path, task_trace.kind as trace_kind
                FROM task
                INNER JOIN task_property ON task_property.task=task.id
                INNER JOIN task_property_status ON task_property_status.task_property=task_property.id
                LEFT JOIN task_trace ON task_property_status.task_trace=task_trace.id;
            """
        ).fetchall()

        return {row["id"]: parse_status_data_row(row) for row in rows}

    def print_status_summary_fmt(self, tasknames: list[str], status_format: str, latest: bool):
        # get all statuses
        all_properties = self.all_status_data_joined()
        latest_task_ids = filter_latest_task_ids(self.all_tasks())

        # print header
        header = format_status_data_fmtline(None, status_format)
        if header:
            print(header)

        # find summary for each task/property combo
        prop_map: dict[(str, str, str), dict[str, (int, int)]] = {}
        for row, prop_status in all_properties.items():
            if tasknames and prop_status['task_name'] not in tasknames:
                continue
            if latest and prop_status['task_id'] not in latest_task_ids:
                continue
            status = prop_status['status']
            this_depth = prop_status['data'].get('step')
            this_kind = prop_status['trace_kind']
            key = (prop_status['task_name'], prop_status['hdlname'])
            try:
                prop_status_map = prop_map[key]
            except KeyError:
                prop_map[key] = prop_status_map = {}

            try:
                current_depth, _, current_kind = prop_status_map[status]
            except KeyError:
                prop_status_map[status] = (this_depth, row, this_kind)
                continue

            update_map = False
            if current_depth is None and current_kind is None:
                # no depth or kind to compare, just take latest data
                update_map = True
            elif this_depth is not None and this_depth != current_depth:
                if current_depth is None:
                    # always prefer a known depth to an unknown
                    update_map = True
                elif status == 'FAIL' and this_depth < current_depth:
                    # earliest fail
                    update_map = True
                elif status != 'FAIL' and this_depth > current_depth:
                    # latest non-FAIL
                    update_map = True
            elif this_kind in ['fst', 'vcd']:
                # prefer traces over witness files
                update_map = True
            if update_map:
                prop_status_map[status] = (this_depth, row, this_kind)

        for prop in prop_map.values():
            # ignore UNKNOWNs if there are other statuses
            if len(prop) > 1 and "UNKNOWN" in prop:
                del prop["UNKNOWN"]

            for _, row, _ in prop.values():
                line = format_status_data_fmtline(all_properties[row], status_format)
                print(line)

def combine_statuses(statuses):
    statuses = set(statuses)

    if len(statuses) > 1:
        statuses.discard("UNKNOWN")

    return ",".join(sorted(statuses))

def parse_status_data_row(raw: sqlite3.Row):
    row_dict = dict(raw)    
    row_dict["name"] = json.loads(row_dict.get("name", "null"))
    row_dict["data"] = json.loads(row_dict.get("data") or "{}")
    return row_dict

fmtline_columns = [
    "time",
    "task_name",
    "mode",
    "engine",
    "name",
    "location",
    "kind",
    "status",
    "trace",
    "depth",
]

def format_status_data_fmtline(row: dict|None, fmt: str = "csv") -> str:
    if row is None:
        data = None
    else:
        engine = row['data'].get('engine', row['data'].get('source'))
        name = row['hdlname']
        depth = row['data'].get('step')

        data = {
            "task_name": row['task_name'],
            "mode": row['mode'],
            "engine": engine,
            "name": name or pretty_path(row['name']),
            "location": row['location'],
            "kind": row['kind'],
            "status": row['status'] or "UNKNOWN",
            "depth": depth,
        }
        try:
            data["trace"] = str(Path(row['workdir']) / row['path'])
        except TypeError:
            pass
        try:
            data['time'] = round(row['status_created'] - row['created'], 2)
        except TypeError:
            pass
    if fmt == "csv":
        if data is None:
            csv_line = fmtline_columns
        else:
            csv_line = [data.get(column) for column in fmtline_columns]
        def csv_field(value):
            if value is None:
                return ""
            value = str(value).replace('"', '""')
            if any(c in value for c in '",\n'):
                value = f'"{value}"'
            return value
        return ','.join(map(csv_field, csv_line))
    elif fmt == "jsonl":
        if data is None:
            return ""
        # field order
        data = {column: data[column] for column in fmtline_columns if data.get(column)}
        return json.dumps(data)

def filter_latest_task_ids(all_tasks: dict[int, dict[str]]):
    latest: dict[str, int] = {}
    for task_id, task_dict in all_tasks.items():
        latest[task_dict["workdir"]] = task_id
    return list(latest.values())

def remove_db(path):
    path = Path(path)
    lock_exts = [".sqlite-wal", ".sqlite-shm"]
    maybe_locked = False
    for lock_file in [path.with_suffix(ext) for ext in lock_exts]:
        if lock_file.exists():
            # lock file may be a false positive if it wasn't cleaned up
            maybe_locked = True
            break

    if not maybe_locked:
        # safe to delete
        os.remove(path)
        return

    # test database directly
    with sqlite3.connect(path, isolation_level="EXCLUSIVE", timeout=1) as con:
        cur = con.cursor()
        # single result rows
        cur.row_factory = lambda _, r: r[0]

        # changing journal_mode is disallowed if there are multiple connections
        try:
            cur.execute("PRAGMA journal_mode=DELETE")
        except sqlite3.OperationalError as err:
            if "database is locked" in err.args[0]:
                raise FileInUseError(file=path)
            else:
                raise

        # no other connections, delete all tables
        drop_script = cur.execute("SELECT name FROM sqlite_master WHERE type = 'table';").fetchall()
        for table in drop_script:
            cur.execute(f"DROP TABLE {table}")
