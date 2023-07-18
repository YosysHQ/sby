#
# SymbiYosys (sby) -- Front-end for Yosys-based formal verification flows
#
# Copyright (C) 2022  Jannis Harder <jix@yosyshq.com> <me@jix.one>
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#

import atexit
import os
import select
import shlex
import subprocess
import sys
import weakref
import signal

if os.name == "posix":
    import fcntl

inherited_jobcount = None
inherited_jobserver_auth = None
inherited_jobserver_auth_present = None

def process_jobserver_environment():
    """Process the environment looking for a make jobserver. This should be called
    early (when only inherited fds are present) to reliably detect whether the jobserver
    specified in the environment is accessible."""
    global inherited_jobcount
    global inherited_jobserver_auth
    global inherited_jobserver_auth_present

    if len(sys.argv) >= 2 and sys.argv[1] == '--jobserver-helper':
        jobserver_helper(*map(int, sys.argv[2:]))
        exit(0)

    inherited_jobserver_auth_present = False

    for flag in shlex.split(os.environ.get("MAKEFLAGS", "")):
        if flag.startswith("-j"):
            if flag == "-j":
                inherited_jobcount = 0
            else:
                try:
                    inherited_jobcount = int(flag[2:])
                except ValueError:
                    pass
        elif flag.startswith("--jobserver-auth=") or flag.startswith("--jobserver-fds="):
            inherited_jobserver_auth_present = True
            if os.name == "posix":
                arg = flag.split("=", 1)[1]
                if arg.startswith("fifo:"):
                    try:
                        fd = os.open(arg[5:], os.O_RDWR)
                    except FileNotFoundError:
                        pass
                    else:
                        inherited_jobserver_auth = fd, fd
                else:
                    arg = arg.split(",")
                    try:
                        jobserver_fds = int(arg[0]), int(arg[1])
                        for fd in jobserver_fds:
                            fcntl.fcntl(fd, fcntl.F_GETFD)
                    except (ValueError, OSError):
                        pass
                    else:
                        inherited_jobserver_auth = jobserver_fds


def jobserver_helper(jobserver_read_fd, jobserver_write_fd, request_fd, response_fd):
    """Helper process to handle blocking jobserver pipes."""
    def handle_sigusr1(*args):
        # Since Python doesn't allow user code to handle EINTR anymore, we replace the
        # jobserver fd with an fd at EOF to interrupt a blocking read in a way that
        # cannot lose any read data
        r, w = os.pipe()
        os.close(w)
        os.dup2(r, jobserver_read_fd)
        os.close(r)
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    signal.signal(signal.SIGUSR1, handle_sigusr1)
    pending = 0
    while True:
        try:
            new_pending = len(os.read(request_fd, 1024))
            if new_pending == 0:
                pending = 0
                break
            else:
                pending += new_pending
                continue
        except BlockingIOError:
            if pending == 0:
                select.select([request_fd], [], [])
                continue

        if pending > 0:
            try:
                # Depending on the make version (4.3 vs 4.2) this is blocking or
                # non-blocking. As this is an attribute of the pipe not the fd, we
                # cannot change it without affecting other processes. Older versions of
                # gnu make require this to be blocking, and produce errors if it is
                # non-blocking. Newer versions of gnu make set this non-blocking, both,
                # as client and as server. The documentation still says it is blocking.
                # This leaves us no choice but to handle both cases, which is the reason
                # we have this helper process in the first place.
                token = os.read(jobserver_read_fd, 1)
            except BlockingIOError:
                select.select([jobserver_read_fd], [], [])
                continue
            if not token:
                break

            pending -= 1

            try:
                os.write(response_fd, token)
            except:
                os.write(jobserver_write_fd, token)
                raise
    os.close(jobserver_write_fd)


class SbyJobLease:
    def __init__(self, client):
        self.client = client
        self.is_ready = False
        self.is_done = False

    def done(self):
        if self.is_ready and not self.is_done:
            self.client.return_lease()

        self.is_done = True

    def __repr__(self):
        return f"is_ready={self.is_ready} is_done={self.is_done}"

    def __del__(self):
        self.done()


class SbyJobServer:
    def __init__(self, jobcount):
        assert jobcount >= 1
        # TODO support unlimited parallelism?
        self.jobcount = jobcount
        if jobcount == 1:
            self.read_fd, self.write_fd = None, None
            self.makeflags = None
        elif jobcount > 1:
            self.read_fd, self.write_fd = os.pipe()
            if os.getenv('SBY_BLOCKING_JOBSERVER') != '1':
                os.set_blocking(self.read_fd, False)
            os.write(self.write_fd, b"*" * (jobcount - 1))
            self.makeflags = f"-j{jobcount} --jobserver-auth={self.read_fd},{self.write_fd} --jobserver-fds={self.read_fd},{self.write_fd}"


class SbyJobClient:
    def __init__(self, fallback_jobcount=None):
        self.jobcount = None
        self.read_fd = self.write_fd = None
        self.helper_process = None

        self.local_slots = 1
        self.acquired_slots = []
        self.pending_leases = []

        assert inherited_jobserver_auth_present is not None, "process_jobserver_environment was not called"

        have_jobserver = inherited_jobserver_auth_present

        if os.name == "nt" and inherited_jobserver_auth_present:
            # There are even more incompatible variants of the make jobserver on
            # windows, none of them are supported for now.
            print("WARNING: Found jobserver in MAKEFLAGS, this is not supported on windows.")
            have_jobserver = False

        if have_jobserver and inherited_jobserver_auth is None:
            print("WARNING: Could not connect to jobserver specified in MAKEFLAGS, disabling parallel execution.")
            have_jobserver = False
            fallback_jobcount = 1

        if have_jobserver:
            jobcount = inherited_jobcount
        elif fallback_jobcount is not None:
            jobcount = fallback_jobcount
        elif inherited_jobcount is not None and inherited_jobcount > 0:
            jobcount = inherited_jobcount
        else:
            try:
                jobcount = len(os.sched_getaffinity(0))
            except AttributeError:
                jobcount = os.cpu_count()

        if have_jobserver:
            self.read_fd, self.write_fd = inherited_jobserver_auth
        elif os.name == "nt":
            # On Windows, without a jobserver, use only local slots
            self.local_slots = jobcount
        else:
            self.sby_jobserver = SbyJobServer(jobcount)
            self.read_fd = self.sby_jobserver.read_fd
            self.write_fd = self.sby_jobserver.write_fd

        self.jobcount = jobcount

        if self.read_fd is not None:
            if os.get_blocking(self.read_fd):
                request_read_fd, self.request_write_fd = os.pipe()
                self.response_read_fd, response_write_fd = os.pipe()
                os.set_blocking(self.response_read_fd, False)
                os.set_blocking(request_read_fd, False)

                pass_fds = [self.read_fd, self.write_fd, request_read_fd, response_write_fd]

                self.helper_process = subprocess.Popen(
                    [sys.executable, sys.modules['__main__'].__file__, '--jobserver-helper', *map(str, pass_fds)],
                    stdin=subprocess.DEVNULL,
                    pass_fds=pass_fds,
                )

                os.close(request_read_fd)
                os.close(response_write_fd)

                atexit.register(self.atexit_blocking)
            else:
                atexit.register(self.atexit_nonblocking)

    def atexit_nonblocking(self):
        while self.acquired_slots:
            os.write(self.write_fd, self.acquired_slots.pop())

    def atexit_blocking(self):
        # Return all slot tokens we are currently holding
        while self.acquired_slots:
            os.write(self.write_fd, self.acquired_slots.pop())

        if self.helper_process:
            # Closing the request pipe singals the helper that we want to exit
            os.close(self.request_write_fd)

            # Additionally we send a signal to interrupt a blocking read within the
            # helper
            self.helper_process.send_signal(signal.SIGUSR1)

            # The helper might have been in the process of sending us some tokens, which
            # we still need to return
            while True:
                try:
                    token = os.read(self.response_read_fd, 1)
                except BlockingIOError:
                    select.select([self.response_read_fd], [], [])
                    continue
                if not token:
                    break
                os.write(self.write_fd, token)
            os.close(self.response_read_fd)

            # Wait for the helper to exit, should be immediate at this point
            self.helper_process.wait()

    def request_lease(self):
        pending = SbyJobLease(self)

        if self.local_slots > 0:
            self.local_slots -= 1
            pending.is_ready = True
        else:
            self.pending_leases.append(weakref.ref(pending))
            if self.helper_process:
                os.write(self.request_write_fd, b"!")

        return pending

    def return_lease(self):
        if self.acquired_slots:
            os.write(self.write_fd, self.acquired_slots.pop())
            return

        if self.activate_pending_lease():
            return

        self.local_slots += 1

    def activate_pending_lease(self):
        while self.pending_leases:
            pending = self.pending_leases.pop(0)()
            if pending is None:
                continue
            pending.is_ready = True
            return True
        return False

    def has_pending_leases(self):
        while self.pending_leases and not self.pending_leases[-1]():
            self.pending_leases.pop()
        return bool(self.pending_leases)

    def poll_fds(self):
        if self.helper_process:
            return [self.response_read_fd]
        elif self.read_fd is not None and self.has_pending_leases():
            return [self.read_fd]
        else:
            return []

    def poll(self):
        read_fd = self.response_read_fd if self.helper_process else self.read_fd
        if read_fd is None:
            return

        while self.helper_process or self.has_pending_leases():
            try:
                token = os.read(read_fd, 1)
            except BlockingIOError:
                break

            self.got_token(token)

    def got_token(self, token):
        self.acquired_slots.append(token)

        if self.activate_pending_lease():
            return

        self.return_lease()
