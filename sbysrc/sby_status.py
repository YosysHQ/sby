from __future__ import annotations

import sqlite3
import os
import time
import json
from collections import defaultdict
from functools import wraps
from pathlib import Path
from typing import Any, Callable, TypeVar, Optional, Iterable
from sby_design import SbyProperty, pretty_path


Fn = TypeVar("Fn", bound=Callable[..., Any])


def transaction(method: Fn) -> Fn:
    @wraps(method)
    def wrapper(self: SbyStatusDb, *args: Any, **kwargs: Any) -> Any:
        if self._transaction_active:
            return method(self, *args, **kwargs)

        try:
            self.log_debug(f"begin {method.__name__!r} transaction")
            self.db.execute("begin")
            self._transaction_active = True
            result = method(self, *args, **kwargs)
            self.db.execute("commit")
            self._transaction_active = False
            self.log_debug(f"comitted {method.__name__!r} transaction")
            return result
        except sqlite3.OperationalError as err:
            self.log_debug(f"failed {method.__name__!r} transaction {err}")
            self.db.rollback()
            self._transaction_active = False
        except Exception as err:
            self.log_debug(f"failed {method.__name__!r} transaction {err}")
            self.db.rollback()
            self._transaction_active = False
            raise
        try:
            self.log_debug(
                f"retrying {method.__name__!r} transaction once in immediate mode"
            )
            self.db.execute("begin immediate")
            self._transaction_active = True
            result = method(self, *args, **kwargs)
            self.db.execute("commit")
            self._transaction_active = False
            self.log_debug(f"comitted {method.__name__!r} transaction")
            return result
        except Exception as err:
            self.log_debug(f"failed {method.__name__!r} transaction {err}")
            self.db.rollback()
            self._transaction_active = False
            raise

    return wrapper  # type: ignore


class SbyStatusDb:
    def __init__(self, path: Path, task, timeout: float = 5.0):
        self.debug = False
        self.task = task
        self._transaction_active = False

        setup = not os.path.exists(path)

        self.db = sqlite3.connect(path, isolation_level=None, timeout=timeout)
        self.db.row_factory = sqlite3.Row
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=0")

        if setup:
            self._setup()

        if task is not None:
            self.task_id = self.create_task(workdir=task.workdir, mode=task.opt_mode)

    def log_debug(self, *args):
        if self.debug:
            if self.task:
                self.task.log(" ".join(str(arg) for arg in args))
            else:
                print(*args)

    @transaction
    def _setup(self):
        script = """
                CREATE TABLE task (
                    id INTEGER PRIMARY KEY,
                    workdir TEXT,
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
                );
            """
        for statement in script.split(";\n"):
            statement = statement.strip()
            if statement:
                self.db.execute(statement)

    @transaction
    def create_task(self, workdir: str, mode: str) -> int:
        return self.db.execute(
            """
                INSERT INTO task (workdir, mode, created)
                VALUES (:workdir, :mode, :now)
            """,
            dict(workdir=workdir, mode=mode, now=time.time()),
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
                INSERT INTO task_property (name, src, task, created)
                VALUES (:name, :src, :task, :now)
            """,
            [
                dict(
                    name=json.dumps(prop.path),
                    src=prop.location or "",
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

    @transaction
    def all_tasks(self):
        rows = self.db.execute(
            """
                SELECT id, workdir, created FROM task
            """
        ).fetchall()

        return {row["id"]: dict(row) for row in rows}

    @transaction
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

    @transaction
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

    @transaction
    def all_status_data(self):
        return (
            self.all_tasks(),
            self.all_task_properties(),
            self.all_task_property_statuses(),
        )

    @transaction
    def reset(self):
        self.db.execute("""DELETE FROM task_property_status""")
        self.db.execute("""DELETE FROM task_property_data""")
        self.db.execute("""DELETE FROM task_property""")
        self.db.execute("""DELETE FROM task_status""")
        self.db.execute("""DELETE FROM task""")

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


def combine_statuses(statuses):
    statuses = set(statuses)

    if len(statuses) > 1:
        statuses.discard("UNKNOWN")

    return ",".join(sorted(statuses))
