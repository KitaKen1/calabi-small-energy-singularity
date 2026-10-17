#!/usr/bin/env bash
set -euo pipefail
CALABI_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
: "${COMPARATOR_TOOLS:?Run install-tools.sh first}"
CALABI_RECEIPT="$CALABI_ROOT/comparator-receipt"
mkdir -p "$CALABI_RECEIPT"
printf 'NOT_RUN\n' > "$CALABI_RECEIPT/status.txt"
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > "$CALABI_RECEIPT/status.txt"; fi' EXIT
test "$(uname -s)" = Linux
python3 "$CALABI_ROOT/lean/comparator/check-inputs.py" --receipt-dir "$CALABI_RECEIPT/before"
python3 - "$COMPARATOR_TOOLS" "$CALABI_ROOT/lean/comparator/pins.json" "$CALABI_RECEIPT/tools.json" <<'PY'
from pathlib import Path
import hashlib,json,re,subprocess,sys
root=Path(sys.argv[1]);p=json.load(open(sys.argv[2]));records={}
for tool in ['comparator','lean4export','landrun']:
    actual=subprocess.check_output(['git','-C',str(root/tool),'rev-parse','HEAD'],text=True).strip()
    if actual!=p[tool+'_commit']:raise SystemExit('Wrong tool revision: '+tool)
    changes=subprocess.check_output(['git','-C',str(root/tool),'diff','--name-only'],text=True).splitlines()
    if changes!=(['lean-toolchain'] if tool!='landrun' else []):raise SystemExit('Unexpected checker changes: '+tool)
    if tool!='landrun' and (root/tool/'lean-toolchain').read_text().strip()!=p['lean_toolchain']:
        raise SystemExit('Wrong checker toolchain')
    records[tool]={'commit':actual,'changed_files':changes}
versions={}
for tool,directory in [('proof',Path.cwd()/'lean'),('comparator',root/'comparator'),('lean4export',root/'lean4export')]:
    version=subprocess.check_output(['lake','env','lean','--version'],cwd=directory,text=True).strip()
    if not re.search(r'Lean \(version 4\.34\.1(?:,|\))',version):raise SystemExit('Wrong runtime compiler: '+tool)
    versions[tool]=version
binaries={tool:hashlib.sha256((root/tool/'.lake/build/bin'/tool).read_bytes()).hexdigest()
          for tool in ['comparator','lean4export']}
Path(sys.argv[3]).write_text(json.dumps({'status':'PASS','required_version':'4.34.1',
    'source_revisions':records,'compiler_versions':versions,'binary_sha256':binaries},indent=2)+'\n')
PY
{
  printf 'repository=%s\ncommit=%s\nrun_id=%s\nattempt=%s\n' "${GITHUB_REPOSITORY:-local}" "${GITHUB_SHA:-local}" "${GITHUB_RUN_ID:-local}" "${GITHUB_RUN_ATTEMPT:-local}"
  date -u +started_utc=%FT%TZ
  (cd "$CALABI_ROOT/lean" && lake env lean --version)
  id
} > "$CALABI_RECEIPT/environment.txt"
sudo systemd-run --wait --collect --pipe \
  --uid="$(id -u)" --gid="$(id -g)" \
  --property='RestrictAddressFamilies=~AF_UNIX' --property=NoNewPrivileges=yes \
  --property=RuntimeMaxSec=240min --working-directory="$CALABI_ROOT/lean" \
  --setenv="PATH=$PATH" --setenv="HOME=$HOME" --setenv=LEAN_NUM_THREADS=2 \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_TOOLS/bin/landrun" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export" \
  -- "$HOME/.elan/bin/lake" env "$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator" comparator.json \
  2>&1 | tee "$CALABI_RECEIPT/comparator.log"
grep -Fxq 'Lean default kernel accepts the solution' "$CALABI_RECEIPT/comparator.log"
grep -Fxq 'Your solution is okay!' "$CALABI_RECEIPT/comparator.log"
(cd "$CALABI_ROOT/lean" && lake env lean FCAudit.lean) > "$CALABI_RECEIPT/axioms.log" 2>&1
python3 "$CALABI_ROOT/lean/comparator/check-axioms.py" "$CALABI_RECEIPT/axioms.log" "$CALABI_RECEIPT/axioms.json"
python3 "$CALABI_ROOT/lean/comparator/check-inputs.py" --receipt-dir "$CALABI_RECEIPT/after"
printf 'PASS\n' > "$CALABI_RECEIPT/status.txt"
