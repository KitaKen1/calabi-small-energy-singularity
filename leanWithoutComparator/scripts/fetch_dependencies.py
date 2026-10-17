"""Fetch only the revisions in lake-manifest.json, without fetching all tags."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def fetch(package):
    dest = ROOT / ".lake/packages" / package["name"]
    dest.mkdir(parents=True, exist_ok=True)
    if not (dest / ".git").exists():
        subprocess.run(["git", "init", "-q", str(dest)], check=True)
        subprocess.run(["git", "-C", str(dest), "remote", "add", "origin", package["url"]],
                       check=True)
    head = subprocess.run(["git", "-C", str(dest), "rev-parse", "HEAD"],
                          capture_output=True, text=True)
    if head.returncode == 0:
        if head.stdout.strip() != package["rev"]:
            raise RuntimeError(f"Existing {dest} has a different revision; leaving it unchanged.")
        return package["name"] + ": already pinned"
    subprocess.run(["git", "-C", str(dest), "fetch", "-q", "--depth", "1", "origin",
                    package["rev"]], check=True, timeout=300)
    subprocess.run(["git", "-C", str(dest), "checkout", "-q", "--detach", package["rev"]],
                   check=True)
    return package["name"] + ": fetched"


if __name__ == "__main__":
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    with ThreadPoolExecutor(max_workers=4) as executor:
        for result in executor.map(fetch, packages):
            print(result, flush=True)
