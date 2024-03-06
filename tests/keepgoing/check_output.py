import re


def line_ref(dir, filename, pattern):
    with open(dir + "/src/" + filename) as file:
        if isinstance(pattern, str):
            pattern_re = re.compile(re.escape(pattern))
        else:
            pattern_re = pattern
            pattern = pattern.pattern

        for number, line in enumerate(file, 1):
            if pattern_re.search(line):
                # Needs to match source locations for both verilog frontends
                return fr"{filename}:(?:{number}|\d+\.\d+-{number}\.\d+)"

        raise RuntimeError("%s: pattern `%s` not found" % (filename, pattern))
