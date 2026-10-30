#!/usr/bin/env python3
"""Check the installed compiler and every Git dependency against the lockfile."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.32.0"
EXPECTED_MATHLIB = "81a5d257c8e410db227a6665ed08f64fea08e997"


def run(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


if (ROOT / "lean-toolchain").read_text().strip() != EXPECTED_TOOLCHAIN:
    raise SystemExit("Unexpected Lean toolchain; update the approved version deliberately.")
version = run("lake", "env", "lean", "--version")
if not re.search(r"Lean \(version 4\.32\.0(?:,|\))", version):
    raise SystemExit(f"Wrong running compiler: {version}")
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
packages = manifest["packages"]
for package in packages:
    name, revision = package["name"], package["rev"]
    if package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise SystemExit(f"Dependency {name} is not pinned to a Git commit.")
    if name == "mathlib" and revision != EXPECTED_MATHLIB:
        raise SystemExit("mathlib does not match the approved v4.32.0 revision.")
    path = ROOT / manifest["packagesDir"] / name
    if not path.is_dir():
        raise SystemExit(f"Missing dependency {name}; fetch the pinned Lake dependencies first.")
    if run("git", "rev-parse", "HEAD", cwd=path) != revision:
        raise SystemExit(f"Dependency {name} HEAD differs from lake-manifest.json.")
    if run("git", "status", "--porcelain", "--untracked-files=no", cwd=path):
        raise SystemExit(f"Dependency {name} has modified tracked source files.")
print(f"Dependency audit passed: {version}; {len(packages)} exact clean Git revisions.")
