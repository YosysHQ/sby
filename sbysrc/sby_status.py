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
    created REAL,
    FOREIGN KEY(task) REFERENCES task(id)
);
CREATE TABLE task_property_status (
    id INTEGER PRIMARY KEY,
    task_property INTEGER,
    status TEXT,
    data TEXT,
    created REAL,
    FOREIGN KEY(task_property) REFERENCES task_property(id)
);
CREATE TABLE task_property_data (
    id INTEGER PRIMARY KEY,
    task_property INTEGER,
    kind TEXT,
    data TEXT,
    created REAL,
    FOREIGN KEY(task_property) REFERENCES task_property(id)
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


class SbyStatusDb:
    def __init__(self, path: Path, task, timeout: float = 5.0, live_csv = False):
        self.debug = False
        self.task = task
        self.live_csv = live_csv

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
                INSERT INTO task_property (name, src, hdlname, task, created)
                VALUES (:name, :src, :hdlname, :task, :now)
            """,
            [
                dict(
                    name=json.dumps(prop.path),
                    src=prop.location or "",
                    hdlname=prop.hdlname,
                    task=task_id,
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
        status: Optional[str] = None,
        data: Any = None,
    ):
        if status is None:
            status = property.status

        now = time.time()
        self.db.execute(
            """
                INSERT INTO task_property_status (
                    task_property, status, data, created
                )
                VALUES (
                    (SELECT id FROM task_property WHERE task = :task AND name = :name),
                    :status, :data, :now
                )
            """,
            dict(
                task=self.task_id,
                name=json.dumps(property.path),
                status=status,
                data=json.dumps(data),
                now=now,
            ),
        )

        if self.live_csv:
            csv = [
                round(now - self.start_time, 2),
                self.task.name,
                self.task.opt_mode,
                data.get("engine", data["source"]),
                property.hdlname,
                property.location,
                property.status,
                data.get("step", "DEPTH?"),
            ]
            self.task.log(f"{click.style('csv', fg='yellow')}: {','.join(str(v) for v in csv)}")

    @transaction
    def add_task_property_data(self, property: SbyProperty, kind: str, data: Any):
        now = time.time()
        self.db.execute(
            """
                INSERT INTO task_property_data (
                    task_property, kind, data, created
                )
                VALUES (
                    (SELECT id FROM task_property WHERE task = :task AND name = :name),
                    :kind, :data, :now
                )
            """,
            dict(
                task=self.task_id,
                name=json.dumps(property.path),
                kind=kind,
                data=json.dumps(data),
                now=now,
            ),
        )

    def all_tasks(self):
        rows = self.db.execute(
            """
                SELECT id, workdir, created FROM task
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
            row["data"] = json.loads(row.get("data", "null"))
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

    def print_status_summary(self):
        tasks, task_properties, task_property_statuses = self.all_status_data()
        properties = defaultdict(set)

        uniquify_paths = defaultdict(dict)

        def add_status(task_property, status):

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

    @transaction
    def all_status_data_joined(self):
        rows = self.db.execute(
            """
                SELECT task.name as 'task_name', task.mode, task.created,
                task_property.src as 'location', task_property.hdlname, task_property_status.status,
                task_property_status.data, task_property_status.created as 'status_created',
                task_property_status.id
                FROM task
                INNER JOIN task_property ON task_property.task=task.id
                INNER JOIN task_property_status ON task_property_status.task_property=task_property.id;
            """
        ).fetchall()
        
        def get_result(row):
            row = dict(row)
            row["data"] = json.loads(row.get("data", "null"))
            return row

        return {row["id"]: get_result(row) for row in rows}

    def print_status_summary_csv(self):
        # get all statuses
        all_properties = self.all_status_data_joined()
        
        # print csv header
        csv_header = [
            "time",
            "task_name",
            "mode",
            "engine",
            "name",
            "location",
            "status",
            "depth",
        ]
        print(','.join(csv_header))

        # find summary for each task/property combo
        prop_map: dict[(str, str), dict[str, (int, int)]] = {}
        for row, prop_status in all_properties.items():
            status = prop_status['status']
            this_depth = prop_status['data'].get('step')
            key = (prop_status['task_name'], prop_status['hdlname'])
            try:
                prop_status_map = prop_map[key]
            except KeyError:
                prop_map[key] = prop_status_map = {}

            # get earliest FAIL, or latest non-FAIL
            current_depth = prop_status_map.get(status, (None,))[0]
            if (current_depth is None or this_depth is not None and
                ((status == 'FAIL' and this_depth < current_depth) or
                 (status != 'FAIL' and this_depth > current_depth))):
                prop_status_map[status] = (this_depth, row)

        for prop in prop_map.values():
            # ignore UNKNOWNs if there are other statuses
            if len(prop) > 1:
                del prop["UNKNOWN"]

            for status, (depth, row) in prop.items():
                prop_status = all_properties[row]
                engine = prop_status['data'].get('engine', prop_status['data']['source'])
                time = prop_status['status_created'] - prop_status['created']
                name = prop_status['hdlname']
                
                # print as csv
                csv_line = [
                    round(time, 2),
                    prop_status['task_name'],
                    prop_status['mode'],
                    engine,
                    name,
                    prop_status['location'],
                    status,
                    depth,
                ]
                print(','.join(str(v) for v in csv_line))


def combine_statuses(statuses):
    statuses = set(statuses)

    if len(statuses) > 1:
        statuses.discard("UNKNOWN")

    return ",".join(sorted(statuses))
