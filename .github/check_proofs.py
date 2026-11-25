"""Check the frozen statement, Lake configuration, kernel proofs, and axioms."""

import argparse
import json
import re
import subprocess
import tomllib
from pathlib import Path

LIBRARY = "BlowupFormalization"
AUDITOR = Path(".github/CheckAxioms.lean")
SPECIFICATION_TAG = "nls-blowup-spec-v1"
SPECIFICATION_COMMIT = "1a95801e84b28b23d7ab9b51cb60fe9cbb95db9d"
FROZEN_FILES = (
    "BlowupFormalization/Specification.lean",
    "BlowupFormalization/Defs.lean",
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
)


def check_frozen_specification():
    ref = f"refs/tags/{SPECIFICATION_TAG}^{{commit}}"
    try:
        commit = subprocess.check_output(
            ["git", "rev-parse", "--verify", "--quiet", ref], text=True,
        ).strip()
    except subprocess.CalledProcessError:
        raise SystemExit(
            f"Fetch the frozen specification with git fetch origin tag {SPECIFICATION_TAG}"
        ) from None
    if commit != SPECIFICATION_COMMIT:
        raise SystemExit(f"{SPECIFICATION_TAG} must point to {SPECIFICATION_COMMIT}, found {commit}.")

    changes = subprocess.check_output([
        "git", "diff", "--name-only", "--no-ext-diff", "--no-textconv",
        commit, "--", *FROZEN_FILES,
    ], text=True).splitlines()
    if changes:
        raise SystemExit(f"Files differ from frozen {SPECIFICATION_TAG}: {', '.join(changes)}")
    print(f"Specification matches {SPECIFICATION_TAG} ({commit}).", flush=True)


def project_modules():
    files = subprocess.check_output([
        "git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.lean",
    ]).decode().split("\0")
    modules = set()
    for path in map(Path, filter(None, files)):
        if path == AUDITOR or not path.exists():
            continue
        if path != Path(f"{LIBRARY}.lean") and path.parts[0] != LIBRARY:
            raise SystemExit(f"Lean source is outside the checked library: {path}")
        modules.add(".".join(path.with_suffix("").parts))
    if LIBRARY not in modules:
        raise SystemExit(f"Missing library root: {LIBRARY}.lean")
    return sorted(modules)


def check_lake_configuration():
    config = tomllib.loads(Path("lakefile.toml").read_text())
    if config.get("defaultTargets") != [LIBRARY] or config.get("lean_lib") != [
        {"name": LIBRARY, "globs": [f"{LIBRARY}.*"]},
    ]:
        raise SystemExit("The default library must build its root and every submodule.")
    dependencies = config.get("require", [])
    if len(dependencies) != 1 or any(
        dependencies[0].get(key) != value
        for key, value in {"name": "mathlib", "scope": "leanprover-community"}.items()
    ):
        raise SystemExit("Mathlib must be the only direct Lake dependency.")

    manifest = json.loads(Path("lake-manifest.json").read_text())
    direct = [package for package in manifest["packages"] if not package["inherited"]]
    if len(direct) != 1 or direct[0]["name"] != "mathlib" or (
        direct[0]["url"] != "https://github.com/leanprover-community/mathlib4"
        or direct[0]["type"] != "git"
        or not re.fullmatch(r"[0-9a-f]{40}", direct[0]["rev"])
    ):
        raise SystemExit("The Lake manifest must pin the upstream Mathlib repository.")
    return manifest


def check_inherited_packages(manifest):
    mathlib_manifest = Path(manifest["packagesDir"]) / "mathlib/lake-manifest.json"
    inherited = [package for package in manifest["packages"] if package["inherited"]]
    upstream = json.loads(mathlib_manifest.read_text())["packages"]

    def source(packages):
        return sorted((p["name"], p["url"], p["rev"]) for p in packages)

    if source(inherited) != source(upstream):
        raise SystemExit("The transitive pins must match the pinned Mathlib manifest.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--get-mathlib-cache", action="store_true")
    args = parser.parse_args()
    check_frozen_specification()
    modules = project_modules()
    manifest = check_lake_configuration()
    subprocess.run(["lake", "resolve-deps"], check=True)
    check_inherited_packages(manifest)
    if args.get_mathlib_cache:
        subprocess.run(["lake", "exe", "cache", "get"], check=True)
    subprocess.run(["lake", "build"], check=True)
    subprocess.run(["lake", "env", "lean", "--run", str(AUDITOR), *modules], check=True)
    # The root repeats the entire library as a prefix. Replay proof modules separately
    # so the checker releases each Mathlib environment before loading the next one.
    for module in modules:
        if module != LIBRARY:
            subprocess.run(["lake", "env", "leanchecker", "-v", module], check=True)


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from None
