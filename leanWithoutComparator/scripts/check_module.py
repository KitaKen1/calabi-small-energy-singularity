"""Check an independent local module and publish its complete artifact atomically."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from run_lean import ROOT, LEAN, env

module = sys.argv[1]
if not re.fullmatch(r"Calabi(?:\.[A-Za-z0-9_]+)+", module):
    raise SystemExit("Expected a Calabi module name.")
source = ROOT / (module.replace(".", "/") + ".lean")
before = hashlib.sha256(source.read_bytes()).hexdigest()
staging = ROOT / "audit/staging" / (module.replace(".", "_") + ".olean")
staging.parent.mkdir(parents=True, exist_ok=True)
log = ROOT / "audit" / ("independent-" + module.replace(".", "_") + ".log")
start = time.monotonic()
with log.open("w") as handle:
    result = subprocess.run([str(LEAN), "-j1", "-DautoImplicit=false", "-R", str(ROOT),
                             "-o", str(staging), str(source)], cwd=ROOT, env=env,
                            stdout=handle, stderr=subprocess.STDOUT)
status = {"module": module, "source_sha256": before,
          "seconds": round(time.monotonic() - start, 3), "exit_code": result.returncode}
if result.returncode == 0:
    if hashlib.sha256(source.read_bytes()).hexdigest() != before:
        status["source_changed"] = True
    else:
        dest = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        os.replace(staging, dest)
        status["published"] = True
(ROOT / "audit" / ("independent-" + module.replace(".", "_") + ".json")).write_text(
    json.dumps(status, indent=2) + "\n")
print(log.read_text(), end="")
print(json.dumps(status))
raise SystemExit(result.returncode)
