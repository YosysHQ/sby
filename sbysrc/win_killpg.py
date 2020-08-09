from ctypes import sizeof, windll
from ctypes.wintypes import DWORD, LONG, ULONG
from ctypes import Structure, c_char, pointer, POINTER
import os

# relevant WinAPI references:
# https://docs.microsoft.com/en-us/windows/win32/api/tlhelp32/nf-tlhelp32-createtoolhelp32snapshot
# https://docs.microsoft.com/en-us/windows/win32/api/tlhelp32/ns-tlhelp32-processentry32
# https://docs.microsoft.com/en-us/windows/win32/api/tlhelp32/nf-tlhelp32-process32first
# https://docs.microsoft.com/en-us/windows/win32/api/tlhelp32/nf-tlhelp32-process32next

TH32CS_SNAPPROCESS = 0x00000002
INVALID_HANDLE_VALUE = -1


class PROCESSENTRY32(Structure):
    _fields_ = [
        ("dwSize", DWORD),
        ("cntUsage", DWORD),
        ("th32ProcessID", DWORD),
        ("th32DefaultHeapID", POINTER(ULONG)),
        ("th32ModuleID", DWORD),
        ("cntThreads", DWORD),
        ("th32ParentProcessID", DWORD),
        ("pcPriClassBase", LONG),
        ("dwFlags", DWORD),
        ("szExeFile", c_char * 260),
    ]


def _visit_all_children(pid, lookup, visited):
    if pid not in visited:
        visited.add(pid)
        if pid in lookup:
            for c in lookup[pid]:
                _visit_all_children(c, lookup, visited)


def _update_lookup(pid_lookup, pe):
    cpid = pe.contents.th32ProcessID
    ppid = pe.contents.th32ParentProcessID
    # pid 0 should be the only one that is its own parent.
    # don't add this entry to the graph to avoid an unwanted cycle
    if ppid == 0 and cpid == 0:
        return
    assert (
        cpid != ppid
    ), "Internal error listing windows processes - process is its own parent"
    if ppid not in pid_lookup:
        pid_lookup[ppid] = []
    pid_lookup[ppid].append(cpid)


def _create_process_lookup():
    handle = windll.kernel32.CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0)
    if handle == INVALID_HANDLE_VALUE:
        raise RuntimeError(
            "Could not snapshot running processes - invalid handle returned"
        )
    pe = pointer(PROCESSENTRY32())
    pe.contents.dwSize = sizeof(PROCESSENTRY32)
    pid_lookup = {}
    if windll.kernel32.Process32First(handle, pe) != 0:
        _update_lookup(pid_lookup, pe)
        while windll.kernel32.Process32Next(handle, pe) != 0:
            _update_lookup(pid_lookup, pe)

    return pid_lookup


def win_killpg(pid):
    """
    Approximate the behaviour of os.killpg(pid, signal.SIGKILL) on Windows.

    Windows processes appear to keep track of their parent rather than their
    children, so it is necessary to build a graph of all running processes
    first and use this to derive a list of child processes to be killed.
    """
    pid_lookup = _create_process_lookup()
    to_kill = set()
    _visit_all_children(pid, pid_lookup, to_kill)
    for p in to_kill:
        try:
            # "Any other value for sig will cause the process to be
            # unconditionally killed by the TerminateProcess API"
            os.kill(p, -1)
        except (PermissionError, OSError) as e:
            print("WARNING: error while killing pid {}: {}".format(p, e))
