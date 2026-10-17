#!/usr/bin/env python3
"""Require all six transitive axiom audits and reject any additional axiom."""
from pathlib import Path
import json
import re
import sys

names = ['CalabiFC.small_energy_singularity', 'CalabiFC.small_calabi_energy',
         'Calabi.mainTheorem', 'Calabi.mainTheoremEnergy',
         'Calabi.exists_profile', 'Calabi.Weighted.localizedCorrection']
text = Path(sys.argv[1]).read_text()
records = {}
for name in names:
    matches = re.findall("'" + re.escape(name) + r"' depends on axioms: \[(.*?)\]", text, re.S)
    if len(matches) != 1:
        raise SystemExit('Missing or duplicate axiom receipt: ' + name)
    axioms = [a.strip() for a in matches[0].split(',') if a.strip()]
    if set(axioms) - {'propext', 'Classical.choice', 'Quot.sound'}:
        raise SystemExit('Unexpected axiom: ' + name)
    records[name] = axioms
if 'sorryAx' in text or 'error:' in text:
    raise SystemExit('Failed axiom audit')
Path(sys.argv[2]).write_text(json.dumps({'status': 'PASS', 'targets': records}, indent=2) + '\n')
print('PASS: all six audited declarations use only the three permitted axioms.')
