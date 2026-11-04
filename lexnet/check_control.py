#!/usr/bin/env python3
"""Accept a negative-control run only if exactly two prerequisite compiles exited 0, the target compile exited 1,
and its log holds exactly one error, at the frozen location lean/Bwd.lean:57:6, whose message is Lean's `decide`
reporting a false proposition.  Linter warnings are allowed; any other nonblank text outside a diagnostic block
fails.  usage: check_control.py PREREQ_EXIT PREREQ_EXIT -- TARGET_EXIT TARGET_LOG"""
import re, sys
DIAG = re.compile(r"^(\S+?):(\d+):(\d+): (error|warning)(?:\([^)]*\))?:(.*)$")
LOCATION = ("lean/Bwd.lean", 57, 6)

def check(prereq_exits, target_exit, log):
    if len(prereq_exits) != 2 or any(e != 0 for e in prereq_exits):
        return False, "need exactly two successful prerequisite compiles"
    if target_exit != 1:
        return False, f"target exit was {target_exit}, expected 1"
    blocks = []
    for line in log.splitlines():
        m = DIAG.match(line)
        if m:
            blocks.append([m.group(1), int(m.group(2)), int(m.group(3)), m.group(4), [m.group(5)]])
        elif blocks:
            blocks[-1][4].append(line)
        elif line.strip():
            return False, f"unexpected text before any diagnostic: {line[:80]!r}"
    errors = [b for b in blocks if b[3] == "error"]
    if len(errors) != 1:
        return False, f"expected exactly one error, found {len(errors)}"
    f, l, c, _, body = errors[0]
    if (f, l, c) != LOCATION:
        return False, f"error at {f}:{l}:{c}, expected {LOCATION[0]}:{LOCATION[1]}:{LOCATION[2]}"
    text = "\n".join(body)
    if "Tactic `decide` proved that the proposition" not in text or not re.search(r"^is false$", text, re.M):
        return False, "the error is not the `decide ... is false` diagnostic"
    return True, "exactly one error at the frozen location, the false-proposition diagnostic, after two successful prerequisites"

if __name__ == "__main__":
    i = sys.argv.index("--")
    ok, msg = check([int(x) for x in sys.argv[1:i]], int(sys.argv[i + 1]), open(sys.argv[i + 2], encoding="utf-8").read())
    print(("control OK: " if ok else "control FAIL: ") + msg)
    sys.exit(0 if ok else 1)
