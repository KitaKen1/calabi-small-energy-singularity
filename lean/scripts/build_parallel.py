"""Compile a local dependency closure with a bounded number of Lean processes.

Same pinned Lean and dependency paths as build_local.py. A module is compiled
only after every local import has a current artifact; artifacts are written to
a temporary file and renamed, so an interrupted run never leaves a partial
.olean in the build directory. Mathlib's cache must already be present.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import argparse
import json
import os
import subprocess
import threading
import time
from run_lean import ROOT, LEAN, env

BUILD = ROOT / ".lake/build/lib/lean"
LOCAL = ("Calabi", "OAI", "Integration")


def is_local(name):
    return name in LOCAL or name.startswith(tuple(p + "." for p in LOCAL))


def source(module):
    base = ROOT / "vendor" if module.startswith("OAI.") else ROOT
    return base, base / (module.replace(".", "/") + ".lean")


def olean(module):
    return BUILD / (module.replace(".", "/") + ".olean")


def local_imports(path):
    deps = []
    for line in path.read_text().splitlines():
        if line.startswith("import "):
            deps += [dep for dep in line[7:].split() if is_local(dep)]
    return deps


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("targets", nargs="+")
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--log-dir", default="audit/build")
    parser.add_argument("--summary", default=None)
    args = parser.parse_args()
    log_dir = ROOT / args.log_dir
    log_dir.mkdir(parents=True, exist_ok=True)
    summary = ROOT / (args.summary or f"audit/{args.targets[0].replace('.', '_')}-parallel-build.json")

    deps = {}
    stack = list(args.targets)
    while stack:
        module = stack.pop()
        if module in deps:
            continue
        deps[module] = local_imports(source(module)[1])
        stack += deps[module]

    results = {}
    lock = threading.Lock()

    def current(module):
        out, src = olean(module), source(module)[1]
        if not out.exists() or out.stat().st_mtime < src.stat().st_mtime:
            return False
        return all(olean(d).exists() and olean(d).stat().st_mtime <= out.stat().st_mtime
                   for d in deps[module])

    def compile_one(module):
        base, path = source(module)
        out = olean(module)
        out.parent.mkdir(parents=True, exist_ok=True)
        tmp = out.with_suffix(f".olean.tmp{os.getpid()}")
        log = log_dir / (module.replace(".", "_") + ".log")
        start = time.monotonic()
        with log.open("w") as handle:
            code = subprocess.run([str(LEAN), "-j1", "-DautoImplicit=false", "-R", str(base),
                                   "-o", str(tmp), str(path)], cwd=ROOT, env=env,
                                  stdout=handle, stderr=subprocess.STDOUT).returncode
        if code == 0:
            os.replace(tmp, out)
        elif tmp.exists():
            tmp.unlink()
        return module, code, round(time.monotonic() - start, 3)

    def record(module, entry):
        with lock:
            results[module] = entry
            summary.write_text(json.dumps(
                {"targets": args.targets, "total": len(deps), "modules": results}, indent=2) + "\n")

    pending = set(deps)
    running = {}
    failed = set()
    started = time.monotonic()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            progressed = False
            for module in sorted(pending):
                if any(d in failed for d in deps[module]):
                    pending.discard(module)
                    failed.add(module)
                    record(module, {"exit_code": None, "blocked_by_dependency": True})
                    progressed = True
                elif all(d in results and results[d].get("exit_code") == 0 for d in deps[module]):
                    if current(module):
                        pending.discard(module)
                        record(module, {"exit_code": 0, "seconds": 0, "cached": True})
                        progressed = True
                    elif len(running) < args.jobs:
                        pending.discard(module)
                        running[pool.submit(compile_one, module)] = module
                        progressed = True
            if running and not progressed:
                done, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in done:
                    running.pop(future)
                    module, code, seconds = future.result()
                    record(module, {"exit_code": code, "seconds": seconds})
                    if code:
                        failed.add(module)
                    ok = sum(1 for r in results.values() if r.get("exit_code") == 0)
                    print(f"[{ok}/{len(deps)}] {module}: exit {code}, {seconds}s, "
                          f"elapsed {round(time.monotonic() - started)}s", flush=True)
            elif not running and not progressed and pending:
                raise RuntimeError(f"Import cycle or missing module among: {sorted(pending)[:5]}")
    print(f"done: {len(deps) - len(failed)} ok, {len(failed)} failed or blocked", flush=True)
    raise SystemExit(1 if failed else 0)


if __name__ == "__main__":
    main()
