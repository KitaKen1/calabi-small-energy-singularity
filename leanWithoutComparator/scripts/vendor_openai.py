"""Extract only the transitive OAI imports from a fixed OpenAI revision.

The extraction copies source verbatim. The lock records every source hash.
Run from the Lean directory. A local source cache is optional.
"""
from pathlib import Path
import argparse
import hashlib
import json
import urllib.request

REV = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
ROOTS = [
    "OAI.Analysis.AncientFlat.Weighted.ExactWeightedInverse",
    "OAI.Analysis.AncientFlat.Regularity.InitialSchauder",
    "OAI.Analysis.AncientFlat.Regularity.ShortHolder",
    "OAI.Analysis.SphereIsometry.CompactConvexFixedPoint",
]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    lock_path = root / "vendor-lock.json"
    expected = json.loads(lock_path.read_text())["sha256"] if lock_path.exists() else {}
    seen = {}

    def visit(module):
        if module in seen:
            return
        rel = Path(module.replace(".", "/") + ".lean")
        cached = args.cache / rel if args.cache else None
        existing = root / "vendor" / rel
        if cached is not None and cached.exists():
            data = cached.read_bytes()
        elif existing.exists():
            data = existing.read_bytes()
        else:
            url = f"https://raw.githubusercontent.com/openai/math/{REV}/lean/{rel}"
            with urllib.request.urlopen(url, timeout=60) as response:
                data = response.read()
        text = data.decode("utf-8")
        digest = hashlib.sha256(data).hexdigest()
        if module in expected and digest != expected[module]:
            raise RuntimeError(f"{module} differs from the locked source; leaving the lock unchanged.")
        seen[module] = digest
        dest = root / "vendor" / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        for line in text.splitlines():
            if line.startswith("import "):
                for dep in line[7:].split():
                    if dep.startswith("OAI."):
                        visit(dep)

    for module in ROOTS:
        visit(module)
    lock = {"repository": "https://github.com/openai/math", "revision": REV,
            "roots": ROOTS, "sha256": dict(sorted(seen.items()))}
    (root / "vendor-lock.json").write_text(json.dumps(lock, indent=2) + "\n")
    print(f"Extracted {len(seen)} unchanged OAI modules at {REV}.")


if __name__ == "__main__":
    main()
