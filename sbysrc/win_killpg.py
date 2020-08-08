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


def _all_children(pid, lookup, visited):
    if pid in lookup and pid not in visited:
        visited.add(pid)
        for c in lookup[pid]:
            if c not in visited:
                visited.add(c)
                visited |= _all_children(c, lookup, visited)
        return visited
    else:
        return set()


def _update_lookup(pid_lookup, pe):
    cpid = pe.contents.th32ProcessID
    ppid = pe.contents.th32ParentProcessID
    # pid 0 should be the only one that is its own parent
    assert (
        cpid == 0 or cpid != ppid
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
    if windll.kernel32. (handle, pe) != 0:
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
    to_kill = _all_children(pid, pid_lookup, set())
    for p in to_kill:
        try:
            # "Any other value for sig will cause the process to be
            # unconditionally killed by the TerminateProcess API"
            os.kill(p, sig=-1)
        except PermissionError as pe:
            print("WARNING: error while killing pid {}: {}".format(p, pe))
