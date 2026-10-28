#!/usr/bin/env python3
"""Compile the single-file FC draft and kernel-check the seven-dimensional implication.

Run from lean/ using: lake env python3 comparator/check-fc-draft.py
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import runpy
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
TEMPLATE = ROOT / 'lean/comparator/fc-draft-equivalence.lean.in'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt-dir', type=Path, required=True)
    args = parser.parse_args()
    receipt = args.receipt_dir.resolve()
    receipt.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    record = {'status': 'NOT_RUN', 'method': 'Lean kernel proof: independent small-energy reference implies the CP7 counterexample and projective extension failure',
              'axioms': {}, 'steps': []}
    sources = ['FClikelean/CalabiSmallEnergy.lean', 'lean/Challenge.lean',
               'lean/FCTargetDefinitions.lean', 'lean/comparator/check-fc-draft.py',
               'lean/comparator/fc-draft-equivalence.lean.in', 'FClikelean/vendor-lock.json',
               'FClikelean/vendor/FormalConjecturesUtil/Answer/Syntax.lean',
               'FClikelean/vendor/FormalConjecturesUtil/Answer.lean',
               'FClikelean/vendor/FormalConjecturesUtil/Attributes/AMS.lean',
               'FClikelean/vendor/FormalConjecturesUtil/Attributes/Basic.lean',
               'FClikelean/vendor/FormalConjecturesUtil.lean']
    record['files_sha256'] = {
        name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in sources}

    def run(name, command, env=None):
        result = subprocess.run(command, cwd=ROOT / 'lean', env=env,
                                capture_output=True, text=True)
        output = result.stdout + result.stderr
        (receipt / (name + '.log')).write_text(output)
        record['steps'].append({'name': name, 'exit_code': result.returncode})
        if result.returncode:
            raise RuntimeError(name + ' failed; see ' + str(receipt / (name + '.log')))
        return output

    try:
        if not os.environ.get('LEAN_PATH'):
            raise RuntimeError('Run this script under lake env from lean/')
        parse = runpy.run_path(str(ROOT / 'lean/comparator/check-inputs.py'))['declarations']
        draft = dict(parse((ROOT / sources[0]).read_text()))
        reference = dict(parse((ROOT / sources[1]).read_text()))
        names = ['calabi_flow', 'calabi_flow.variants.dimension_seven']
        if set(draft) != set(names) or set(reference) != {'small_energy_singularity', 'small_calabi_energy'}:
            raise RuntimeError('Unexpected theorem list')
        record['fc_draft_targets'] = ['CalabiFC.' + name for name in names]
        record['verified_targets'] = ['CalabiFC.calabi_flow.variants.dimension_seven']
        record['verified_corollaries'] = ['Not every CPn satisfies CalabiFlowConjecture n']
        record['unverified_targets'] = {
            'CalabiFC.calabi_flow':
                'Statement only; OpenAI source proof is not included in this verification.'}
        proof = (TEMPLATE.read_text()
                 .replace('__DRAFT_TEN_TYPE__', draft['calabi_flow'])
                 .replace('__DRAFT_SEVEN_TYPE__', draft['calabi_flow.variants.dimension_seven'])
                 .replace('__REFERENCE_MAIN_TYPE__', reference['small_energy_singularity']))
        if re.search(r'__[A-Z_]+__', proof):
            raise RuntimeError('Unresolved implication template marker')
        (receipt / 'FCDraftImplication.lean').write_text(proof)
        run('reference-build', ['lake', 'build', 'FCTargetDefinitions'])
        with tempfile.TemporaryDirectory(prefix='calabi-fc-draft-') as temporary:
            temporary = Path(temporary)
            env = os.environ.copy()
            env['LEAN_PATH'] = str(temporary) + os.pathsep + env['LEAN_PATH']
            vendor = ROOT / 'FClikelean/vendor'
            for name, module in [('answer-syntax', 'Answer/Syntax'), ('answer', 'Answer'),
                                 ('AMS', 'Attributes/AMS'), ('Basic', 'Attributes/Basic')]:
                relative = Path('FormalConjecturesUtil') / (module + '.lean')
                output_path = temporary / relative.with_suffix('.olean')
                output_path.parent.mkdir(parents=True, exist_ok=True)
                run('fc-metadata-' + name, ['lean', '--root=' + str(vendor),
                    '-o', str(output_path), str(vendor / relative)], env)
            run('fc-entrypoint', ['lean', '--root=' + str(vendor),
                '-o', str(temporary / 'FormalConjecturesUtil.olean'),
                str(vendor / 'FormalConjecturesUtil.lean')], env)
            run('draft-build', ['lean', '--root=' + str(ROOT / 'FClikelean'),
                               '-o', str(temporary / 'CalabiSmallEnergy.olean'),
                               str(ROOT / sources[0])], env)
            output = run('implication', ['lean', str(receipt / 'FCDraftImplication.lean')], env)
        found = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S))
        for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
            found[name] = ''
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        for name in ['negative_answer_iff', 'flow_iff', 'flow_from_reference', 'flow_to_reference', 'reference_implies_seven', 'reference_implies_projective_failure']:
            target = 'CalabiFCDraftCheck.' + name
            if target not in found:
                raise RuntimeError('Missing implication axiom report: ' + target)
            axioms = [value.strip() for value in found[target].split(',') if value.strip()]
            if not set(axioms).issubset(allowed):
                raise RuntimeError('Unpermitted axiom: ' + target)
            record['axioms'][target] = axioms
        record['status'] = 'PASS'
        record['scope'] = 'Both statements compile. The CP7 variant and projective extension corollary follow from the reference. The main CP10 theorem is statement only; the OpenAI proof is not included.'
    except Exception as error:
        record['status'] = 'FAIL'
        record['error'] = str(error)
    finally:
        record['seconds'] = round(time.monotonic() - started, 2)
        (receipt / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
        print(json.dumps(record))
    if record['status'] != 'PASS':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
