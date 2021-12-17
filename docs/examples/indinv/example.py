from collections import defaultdict
import inspect

N = 32
f = lambda x: (2*x-1) ^ (x&7)

table = [f(i) & (N-1) for i in range(N)]
rtable = [table.count(i) for i in range(N)]

def getPath(v):
    if table[v] is None:
        return [v]
    bak = table[v]
    table[v] = None
    r = [v] + getPath(bak)
    table[v] = bak
    return r

def getPaths():
    visited = set()
    paths = list()
    for i in range(N):
        if rtable[i] == 0:
            paths.append(getPath(i))
    for path in paths:
        for i in path:
            visited.add(i)
    for i in range(N):
        if i not in visited:
            paths.append(getPath(i))
            for j in paths[-1]:
                visited.add(j)
    return paths

pathsByLidx = defaultdict(set)
loopsByIdx = dict()
loopsByLidx = dict()

for path in getPaths():
    i = path.index(path[-1])+1
    head, loop, lidx = tuple(path[:i]), tuple(path[i:]), max(path[i:])
    pathsByLidx[lidx].add((head, loop))

print()
print("The %d-bit function f(x) produces %d loops:" % (N.bit_length()-1, len(pathsByLidx)))
print("  ", inspect.getsource(f).strip())

for lidx, paths in pathsByLidx.items():
    loop = None
    for path in paths:
        for i in path[0] + path[1]:
            loopsByIdx[i] = lidx
        if loop is None or path[1][0] > loop[0]:
            loop = path[1]

    loopsByLidx[lidx] = loop
    
    print()
    print("%d-Element Loop:" % len(loop))
    print("  ", " ->- ".join(["%2d" % i for i in loop + (loop[0],)]))

    lines = []
    lastPath = []
    for path in sorted([tuple(reversed(p[0])) for p in paths]):
        line = ""
        for i in range(len(path)):
            if i < len(lastPath) and lastPath[i] == path[i]:
                line += " %s   " % (" " if i == 0 else "|  ")
            else:
                line += " %s %2d" % (" " if i == 0 else "`<-" if len(lastPath) else "-<-", path[i])
                lastPath = []
        lastPath = path
        lines.append(line)

    for i in range(len(lines)-1, -1, -1):
        line, nextline = list(lines[i]), "" if i == len(lines)-1 else lines[i+1]
        if len(nextline) < len(line): nextline = nextline.ljust(len(line))

        for k in range(len(line)):
            if line[k] == "|" and nextline[k] in " -":
                line[k] = " "

        lines[i] = "".join(line)

    print("%d Lead-Ins:" % len(lines))
    for line in lines:
        print(line)

print()
print("Loop Membership:")
for lidx in pathsByLidx:
    print("%18s |" % (loopsByLidx[lidx],), end="")
    for i in range(N):
        print("*" if loopsByIdx[i] == lidx else ".", end="")
    print("|")
print()
