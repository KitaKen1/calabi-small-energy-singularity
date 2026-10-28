#!/usr/bin/env python3
"""Check pinned inputs, independent targets, and the two identical proof copies."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def declarations(text):
    return re.findall(r"^theorem ([\w.]+)\s*:(.*?) :=(?: by\n|\n)", text, re.M | re.S)


def lean_code(text):
    """Ignore documentation while retaining exact nonblank Lean code lines."""
    code = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                code.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif in_string:
            code.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                code.append(text[i + 1])
                i += 2
                continue
            if text[i] == '"':
                in_string = False
            i += 1
        elif text.startswith('/-', i):
            code.append(' ')
            depth = 1
            i += 2
        elif text.startswith('--', i):
            code.append(' ')
            while i < len(text) and text[i] != '\n':
                i += 1
        else:
            code.append(text[i])
            in_string = text[i] == '"'
            i += 1
    require(depth == 0 and not in_string, 'Unclosed Lean comment or string')
    return '\n'.join(line.rstrip() for line in ''.join(code).splitlines() if line.strip())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt-dir', type=Path)
    args = parser.parse_args()
    pins = json.loads((ROOT / 'lean/comparator/pins.json').read_text())
    config = json.loads((ROOT / 'lean/comparator.json').read_text())
    require(config['theorem_names'] == pins['targets'], 'Target list changed')
    require(config['challenge_module'] == 'Challenge' and config['solution_module'] == 'FCSolution',
            'Unexpected reference or solution')
    require(set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'},
            'Axiom permissions changed')
    for name, expected in pins['files_sha256'].items():
        require((ROOT / name).is_file() and digest(ROOT / name) == expected,
                'Pinned verification input changed: ' + name)
    original = json.loads((ROOT / 'lean/comparator/proof-source-manifest.json').read_text())
    for name, expected in original['files_sha256'].items():
        require(digest(ROOT / 'lean' / name) == expected, 'Proof source changed: ' + name)
    shared = json.loads((ROOT / 'lean/comparator/shared-proof-sources.json').read_text())
    excluded = {'lakefile.lean', 'Challenge.lean', 'FCTargetDefinitions.lean', 'FCAudit.lean'}
    def sources(folder):
        return {p.relative_to(ROOT / folder).as_posix() for p in (ROOT / folder).rglob('*.lean')
                if '.lake' not in p.parts and 'comparator' not in p.relative_to(ROOT / folder).parts
                and p.name not in excluded}
    expected_sources = set(shared['files_sha256'])
    require(sources('lean') == sources('leanWithoutComparator') == expected_sources,
            'Missing or extra shared Lean source')
    for name, expected in shared['files_sha256'].items():
        for folder in ['lean', 'leanWithoutComparator']:
            file = ROOT / folder / name
            require(digest(file) == expected, 'Shared source differs: ' + folder + '/' + name)
            text = file.read_text()
            require(not re.search(r'\b(?:sorry|admit|native_decide|unsafe|implemented_by)\b|^\s*axiom\b', text, re.M),
                    'Unreviewed proof escape or hole: ' + name)
            require(not re.search(r'^\s*import (?:Challenge|FCTargetDefinitions)\b', text, re.M),
                    'Proof imports reference: ' + name)
    for folder in ['leanWithoutComparator', 'FClikelean']:
        for filename in ['lean-toolchain', 'lake-manifest.json']:
            require((ROOT / folder / filename).read_bytes() == (ROOT / 'lean' / filename).read_bytes(),
                    'Dependency or toolchain mismatch: ' + folder)
    require((ROOT / 'lean/lean-toolchain').read_text().strip() == pins['lean_toolchain'], 'Wrong Lean')
    deps = {p['name']: p['rev'] for p in json.loads((ROOT / 'lean/lake-manifest.json').read_text())['packages']}
    require(deps['mathlib'] == pins['mathlib_commit'], 'Wrong Mathlib')
    challenge = (ROOT / 'lean/Challenge.lean').read_text()
    solution = (ROOT / 'lean/FCSolution.lean').read_text()
    require(declarations(challenge) == declarations(solution) and len(declarations(solution)) == 2,
            'Challenge and solution statements differ')
    require(challenge.count('  sorry\n') == 2, 'Unexpected reference holes')
    defs = (ROOT / 'lean/FCTargetDefinitions.lean').read_text()
    original_defs = (ROOT / 'lean/Calabi/Geometry/Statement.lean').read_text()
    original_defs = original_defs[:original_defs.index('/-- No smooth Calabi flow on a longer interval')]
    require(defs == original_defs + 'end Calabi.Geometry\n', 'Reference geometry differs from reviewed definitions')
    require(all(i.startswith('Mathlib.') for i in re.findall(r'^import (\S+)', defs, re.M)),
            'Reference imports a submitted proof')
    require(not re.search(r'\b(?:sorry|admit)\b|^\s*axiom\b', defs, re.M), 'Hole in fixed definitions')
    draft = (ROOT / 'FClikelean/CalabiSmallEnergy.lean').read_text()
    draft_sources = {p.relative_to(ROOT / 'FClikelean').as_posix()
                     for p in (ROOT / 'FClikelean').rglob('*.lean')
                     if '.lake' not in p.parts and 'vendor' not in p.relative_to(ROOT / 'FClikelean').parts
                     and p.name != 'lakefile.lean'}
    require(draft_sources == {'CalabiSmallEnergy.lean'}, 'FC-style draft must be a single file')
    draft_imports = re.findall(r'^(?:public )?import (\S+)', draft, re.M)
    require(draft_imports == ['FormalConjecturesUtil'],
            'FC-style statement imports a mathematical local module or submitted proof')
    metadata = json.loads((ROOT / 'FClikelean/vendor-lock.json').read_text())
    metadata_files = {p.relative_to(ROOT / 'FClikelean/vendor').as_posix()
                      for p in (ROOT / 'FClikelean/vendor').rglob('*.lean')}
    require(metadata_files == set(metadata['files_sha256']) | set(metadata['local_files_sha256']),
            'Unexpected FC metadata source')
    for name, expected in {**metadata['files_sha256'], **metadata['local_files_sha256']}.items():
        require(digest(ROOT / 'FClikelean/vendor' / name) == expected,
                'Official FC metadata source changed: ' + name)
    require(draft.count('@[category research solved, AMS 53 58]') == 2,
            'Expected the OpenAI counterexample and one variant')
    require([name for name, _ in declarations(draft)] == ['calabi_flow', 'calabi_flow.variants.dimension_seven'],
            'FC-style target list changed')
    require(pins['fc_draft_targets'] == ['CalabiFC.calabi_flow', 'CalabiFC.calabi_flow.variants.dimension_seven'],
            'Pinned FC-style target list changed')
    require(draft.count('  sorry\n') == 2, 'Unexpected FC-style holes')
    draft_code = lean_code(draft).replace('  sorry\n', '')
    require(not re.search(r'\b(?:sorry|admit|native_decide|unsafe|implemented_by)\b|^\s*axiom\b',
                          draft_code, re.M), 'Unreviewed FC-style hole or proof escape')
    # check-fc-draft.py proves the CP7 target and the projective extension corollary.
    # The main CP10 theorem is explicitly statement only.
    # Hash the actual closure in the exact format used by the original clean audit.
    closure = json.loads((ROOT / 'verification/original-audit/clean-rebuild.json').read_text())
    state = hashlib.sha256()
    for module in sorted(closure['modules']):
        base = ROOT / 'lean/vendor' if module.startswith('OAI.') else ROOT / 'lean'
        data = (base / (module.replace('.', '/') + '.lean')).read_bytes()
        state.update(module.encode() + b'\0' + hashlib.sha256(data).digest())
    old_status = json.loads((ROOT / 'verification/original-audit/status.json').read_text())
    require(state.hexdigest() == old_status['main_theorem']['closure_source_digest']['sha256'],
            'Original checked 448-module closure has changed')
    vendor = json.loads((ROOT / 'lean/vendor-lock.json').read_text())
    for module, expected in vendor['sha256'].items():
        require(digest(ROOT / 'lean/vendor' / (module.replace('.', '/') + '.lean')) == expected,
                'Vendored upstream source differs: ' + module)
    commit = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], capture_output=True, text=True)
    result = {'status': 'PASS', 'tested_commit': commit.stdout.strip() if commit.returncode == 0 else None,
              'targets': pins['targets'], 'original_closure_modules': 448,
              'original_closure_digest': state.hexdigest(), 'identical_shared_sources': len(expected_sources),
              'fixed_reference_definitions': True, 'fc_draft_source_pinned': True,
              'fc_draft_implication_check': 'Run check-fc-draft.py under lake env; the main CP10 theorem is statement only'}
    result['fc_draft_single_file'] = True
    result['fc_draft_targets'] = pins['fc_draft_targets']
    if args.receipt_dir:
        args.receipt_dir.mkdir(parents=True, exist_ok=True)
        (args.receipt_dir / 'input-check.json').write_text(json.dumps(
            {**result, 'pins': pins, 'config': config}, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
