"""Compile a source dependency closure with one Lean process at a time.

Mathlib's cache must already be present. This supplements ordinary lake build
when repeated Lake configuration loading or concurrent builds are expensive.
"""
from pathlib import Path
import argparse
import json
import re
import subprocess
import time
from run_lean import ROOT, LEAN, env

BUILD = ROOT / ".lake/build/lib/lean"


def source(module):
    base = ROOT / "vendor" if module.startswith("OAI.") else ROOT
    return base, base / (module.replace(".", "/") + ".lean")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("target", choices=["Calabi", "Integration", "Calabi.Certificate.KernelChecks"])
    args = parser.parse_args()
    order, seen = [], set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        base, path = source(module)
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                for dep in line[7:].split():
                    if dep.startswith(("Calabi.", "OAI.", "Integration.")) or dep in ("Calabi", "Integration"):
                        visit(dep)
        order.append(module)

    visit(args.target)
    results = []
    failed = set()
    for i, module in enumerate(order, 1):
        base, path = source(module)
        output = BUILD / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = ROOT / "audit" / (module.replace(".", "_") + ".log")
        dependencies = []
        dependency_modules = []
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                for dep in line[7:].split():
                    if dep.startswith(("Calabi.", "OAI.", "Integration.")):
                        dependencies.append(BUILD / (dep.replace(".", "/") + ".olean"))
                        dependency_modules.append(dep)
        if any(dep in failed for dep in dependency_modules):
            failed.add(module)
            results.append({"module": module, "exit_code": None, "blocked_by_dependency": True})
            print(f"[{i}/{len(order)}] {module}: dependency failed", flush=True)
            continue
        if output.exists() and output.stat().st_mtime >= path.stat().st_mtime and all(
                dep.exists() and dep.stat().st_mtime <= output.stat().st_mtime for dep in dependencies):
            results.append({"module": module, "exit_code": 0, "seconds": 0, "cached": True})
            print(f"[{i}/{len(order)}] {module}: unchanged checked artifact", flush=True)
            continue
        start = time.monotonic()
        print(f"[{i}/{len(order)}] {module}", flush=True)
        with log.open("w") as handle:
            status = subprocess.run([str(LEAN), "-j1", "-DautoImplicit=false", "-R", str(base),
                                     "-o", str(output), str(path)], cwd=ROOT, env=env,
                                    stdout=handle, stderr=subprocess.STDOUT).returncode
        duration = round(time.monotonic() - start, 3)
        results.append({"module": module, "exit_code": status, "seconds": duration})
        print(log.read_text(), end="", flush=True)
        print(f"  {duration}s, exit {status}", flush=True)
        (ROOT / "audit" / (args.target.replace(".", "_") + "-build.json")).write_text(
            json.dumps(results, indent=2) + "\n")
        if status:
            failed.add(module)
    (ROOT / "audit" / (args.target.replace(".", "_") + "-build.json")).write_text(
        json.dumps(results, indent=2) + "\n")
    raise SystemExit(1 if failed else 0)


if __name__ == "__main__":
    main()
