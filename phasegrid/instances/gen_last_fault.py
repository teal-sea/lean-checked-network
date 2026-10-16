"""Two planted faults that only the LAST pair of a row can expose, so the kernel cannot short-circuit
on an early pair. Both were prepared by the second reviewer (2026-10-16) and are regenerated here from
the committed tables by text substitution (no numpy, no floating point):

  P7LastFault    = P7Full    with E2 row 6 replaced by E2 row 5     (column b = 6 wrong on every row)
  P113LastFault  = P113Full  with E2_112 replaced by E2_111        (column b = 112 wrong on every row)

Writes PhaseGridInstances/{P7LastFault,P113LastFault}/{Weights,Table}.lean (git-ignored; 2 MB at
p = 113). expected_fail/P7LastRow.lean and expected_fail/P113LastChunk.lean, committed, must then be
REJECTED by the kernel; kernel_reject_last.lean shows the kernel's own verdicts through `addDecl`.
See check_last_fault.sh."""
import re
from pathlib import Path

here = Path(__file__).resolve().parent
src = here / "PhaseGridInstances"


def rename(text, old, new):
    return text.replace(f"PhaseGridInstances.{old}", f"PhaseGridInstances.{new}")


def write(name, weights, table):
    out = src / name
    out.mkdir(exist_ok=True)
    (out / "Weights.lean").write_text(weights)
    (out / "Table.lean").write_text(table)
    print(f"wrote PhaseGridInstances/{name}/Weights.lean ({len(weights)} bytes) and Table.lean")


# p = 7: the tables are single list literals, one row per line
w = (src / "P7Full" / "Weights.lean").read_text()
head = "def E2 : List (List Int) := [\n"
i = w.index(head) + len(head)
j = w.index("]\n", i)          # the list's closing bracket (the row before it ends with its own ']')
rows = w[i:j].split(",\n")
assert len(rows) == 7, len(rows)
assert rows[6] != rows[5]
rows[6] = rows[5]
w7 = w[:i] + ",\n".join(rows) + w[j:]
w7 = rename(w7, "P7Full", "P7LastFault").replace(
    "# Weights of", "# PLANTED FAULT, last column: E2 row 6 replaced by E2 row 5 (the reviewer's fault of 2026-10-16). Weights of", 1)
t7 = rename((src / "P7Full" / "Table.lean").read_text(), "P7Full", "P7LastFault")
write("P7LastFault", w7, t7)

# p = 113: the tables are 113 row definitions each
w = (src / "P113Full" / "Weights.lean").read_text()
m111 = re.search(r"^def E2_111 : List Int := (.*)$", w, re.M)
m112 = re.search(r"^def E2_112 : List Int := (.*)$", w, re.M)
assert m111 and m112 and m111.group(1) != m112.group(1)
w113 = w[:m112.start(1)] + m111.group(1) + w[m112.end(1):]
w113 = rename(w113, "P113Full", "P113LastFault").replace(
    "# Weights of", "# PLANTED FAULT, last column: E2_112 replaced by E2_111 (the reviewer's fault of 2026-10-16). Weights of", 1)
t113 = rename((src / "P113Full" / "Table.lean").read_text(), "P113Full", "P113LastFault")
write("P113LastFault", w113, t113)
