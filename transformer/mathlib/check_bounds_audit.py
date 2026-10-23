#!/usr/bin/env python3
"""Fail closed on missing, duplicated, unexpected, or nonstandard axiom audit records."""
from pathlib import Path
import re
import sys

EXPECTED = (
    'TransformerBridge.absBnd_nth',
    'TransformerBridge.vecOk_abs_nth',
    'TransformerBridge.natAbs_cast',
    'TransformerBridge.colAbsSum_eq_sum_range',
    'TransformerBridge.sum_fin_eq_colAbsSum',
    'TransformerBridge.bounded_of_core',
    'TransformerBridge.frozen_tables_bounded',
    'TransformerCore.Net.tables_ok',
    'TransformerCore.Net.G_length',
    'TransformerCore.Net.colSums_ok',
)
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def check(text):
    found = []
    for line in text.splitlines():
        match = re.fullmatch(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", line)
        if not match:
            raise ValueError(f'unexpected audit output: {line!r}')
        name, _, axioms = match.groups()
        if axioms is not None and (not axioms or not set(axioms.split(', ')) <= STANDARD):
            raise ValueError(f'nonstandard axioms: {line}')
        found.append(name)
    if tuple(found) != EXPECTED or len(EXPECTED) != 10:
        raise ValueError(f'selected audit mismatch: {len(found)} records, expected 10 in exact order')
    return len(found)


if __name__ == '__main__':
    count = check(Path(sys.argv[1]).read_text())
    print(f'selected-declarations={count}/10 status=OK (standard axioms or none)')
