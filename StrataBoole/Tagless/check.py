#!/usr/bin/env python3
"""Check these modules using an existing Strata-Boole dependency installation.

No dependency checkout, toolchain, or source file outside Tagless is modified.
Set STRATA_BOOLE_REPO to the checkout whose pinned dependencies should be used.
Build products stay in Tagless/.build and can be removed at any time.
"""
from pathlib import Path
import os
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DEFAULT_REPO = ROOT if (ROOT / "lean-toolchain").is_file() else Path.home() / "Documents/Strata-Boole"
REPO = Path(os.environ.get("STRATA_BOOLE_REPO", DEFAULT_REPO))
BUILD = HERE / ".build"
MODULES = [
    "Interface", "Embed", "Hoare/Interpretation", "Hoare/Rules",
    "Hoare/Certificate", "Hoare/Guarantees/CoreState", "Hoare/Guarantees/Soundness",
    "Hoare/Guarantees/EntryAdmission", "Tests", "Hoare/Examples", "Hoare/Regression", "Hoare/Audit",
]

def main():
    toolchain = (REPO / "lean-toolchain").read_text().strip()
    prefix = Path(subprocess.check_output(["lean", f"+{toolchain}", "--print-prefix"], text=True).strip())
    paths = [BUILD, REPO / ".lake/build/lib/lean", prefix / "lib/lean"]
    paths += sorted((REPO / ".lake/packages").glob("*/.lake/build/lib/lean"))
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    native_paths = [str(p.parent) for p in paths[1:]]
    env["DYLD_LIBRARY_PATH"] = os.pathsep.join(native_paths)
    # Lean resolves a module namespace through one root. Mirror installed Strata
    # artifacts into the local overlay before adding missing semantic modules.
    for installed in paths[1:]:
        namespace = installed / "Strata"
        if namespace.is_dir():
            for artifact in namespace.rglob("*"):
                if artifact.is_file():
                    local = BUILD / artifact.relative_to(installed)
                    local.parent.mkdir(parents=True, exist_ok=True)
                    if not local.exists():
                        local.symlink_to(artifact)
    wanted = sys.argv[1:] or MODULES
    # Reuse Stephanie's existing front end; build its modules in our local cache.
    frontend = ["Deep/Lang", "Deep/Exec", "Deep/Triple", "Deep/Delab", "Deep/Reflect"]
    targets = [(f"StrataBoole/{module}", REPO) for module in frontend] if "Hoare/Examples" in wanted else []
    targets += [(f"StrataBoole/Tagless/{module}", ROOT) for module in wanted]
    if not sys.argv[1:]:
        targets.append(("StrataBooleTest/tagless", ROOT))
    source_roots = [ROOT, REPO] + sorted((REPO / ".lake/packages").glob("*"))
    checked = set()
    def compile_module(module, source_root):
        if module in checked:
            return
        checked.add(module)
        source = source_root / f"{module}.lean"
        # Build missing semantic dependencies locally, without lake or updates.
        for imported in re.findall(r"^(?:public )?import (?:all )?([A-Za-z0-9_.]+)",
                                   source.read_text(), re.MULTILINE):
            relative = imported.replace(".", "/")
            if any((path / f"{relative}.olean").is_file() for path in paths):
                continue
            dependency_root = next((root for root in source_roots
                                    if (root / f"{relative}.lean").is_file()), None)
            if dependency_root is None:
                raise RuntimeError(f"Missing dependency source: {imported}")
            compile_module(relative, dependency_root)
        output = BUILD / f"{module}.olean"
        output.parent.mkdir(parents=True, exist_ok=True)
        print(f"Checking {module.replace('/', '.')}", flush=True)
        result = subprocess.run([
            "lean", f"+{toolchain}", "--tstack=32768", "-R", str(source_root),
            "-o", str(output), str(source),
        ], env=env, cwd=source_root)
        if result.returncode:
            raise subprocess.CalledProcessError(result.returncode, result.args)
    try:
        for module, source_root in targets:
            compile_module(module, source_root)
    except subprocess.CalledProcessError as error:
        return error.returncode
    return 0

if __name__ == "__main__":
    sys.exit(main())
