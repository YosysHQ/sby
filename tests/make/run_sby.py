import os
import sys
prog = os.environ.get("SBY_CMD", "sby")
os.execvp(prog, [prog, *sys.argv[1:]])
