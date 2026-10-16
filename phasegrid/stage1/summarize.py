"""Condense the rounding.py logs into one table."""
import re, sys, glob
rows = []
for f in sorted(glob.glob(sys.argv[1] + "/stage1_p*.log")):
    txt = open(f).read()
    for block in txt.split("\n[")[1:]:
        head, *rest = block.split("\n")
        m = re.match(r"(.*?)\] p=(\d+) S=(.*?) \|S\|=(\d+) H=(\d+) g\(S\)=([\d.e+-]+) 24\|S\|/g=([\d.e+-]+)", head)
        if not m: continue
        label, p, S, n, H, g, bound = m.groups()
        above = re.search(r"M=(\d+) \(just above\): wrong=(\d+) ties=(\d+) min margin=(-?\d+)", block)
        below = re.search(r"M=(\d+) \(just below\): wrong=(\d+) ties=(\d+) min margin=(-?\d+)", block)
        scan = re.search(r"scan M=1\.\.(\d+): failing M \(wrong, ties\) = (.*?); smallest M with no wrong answer and no tie = (.*)", block)
        rows.append((int(p), label, S if len(S) < 30 else S, n, g, bound,
                     f"M={above[1]}: wrong={above[2]} ties={above[3]} margin={above[4]}" if above else "-",
                     f"M={below[1]}: wrong={below[2]} ties={below[3]} margin={below[4]}" if below else "-",
                     f"scan 1..{scan[1]}: smallest passing M = {scan[3]}; failing M count = {0 if scan[2] == 'none' else scan[2].count('(')}" if scan else "-"))
for r in sorted(rows):
    print(f"p={r[0]:5d} | {r[1]:<32} | S={r[2]:<28} |S|={r[3]:>3} g={float(r[4]):9.5g} bound={float(r[5]):9.5g}\n"
          f"        above: {r[6]}\n        below: {r[7]}\n        {r[8]}")
