#!/usr/bin/env bash
set -euo pipefail
mkdir -p ../build-receipt
printf 'NOT_RUN\n' > ../build-receipt/status.txt
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > ../build-receipt/status.txt; fi' EXIT
lake build FCSolution FCAudit Calabi 2>&1 | tee ../build-receipt/build.log
lake env lean FCAudit.lean > ../build-receipt/axioms.log 2>&1
python3 comparator/check-axioms.py ../build-receipt/axioms.log ../build-receipt/axioms.json
printf 'PASS\n' > ../build-receipt/status.txt
