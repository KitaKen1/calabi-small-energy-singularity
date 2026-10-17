"""Run the pinned Lean with the already-fetched local dependency paths."""
from pathlib import Path
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PACKAGES = ROOT / ".lake/packages"
LEAN = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))) / \
    "toolchains/leanprover--lean4---v4.34.1/bin/lean"
paths = [ROOT / ".lake/build/lib/lean"]
paths += [p / ".lake/build/lib/lean" for p in sorted(PACKAGES.iterdir()) if p.is_dir()]
env = dict(os.environ)
env["LEAN_PATH"] = ":".join(map(str, paths))
env["LEAN_NUM_THREADS"] = "2"
if __name__ == "__main__":
    sys.exit(subprocess.run([str(LEAN), *sys.argv[1:]], cwd=ROOT, env=env).returncode)
