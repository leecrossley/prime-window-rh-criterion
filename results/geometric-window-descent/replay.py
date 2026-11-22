"""Build the geometric window specialization from the sources in this directory."""
import argparse
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
LEAN_REV = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
STRICT_IMPLICITS = {
    "PrincipalArchivedWindow", "PrincipalConductorMinus", "PrincipalCountWindow",
    "PrincipalJointWindow", "PrincipalMinusField", "PrincipalMinusResidues",
    "PrincipalMinusSum", "PrincipalTowerFields",
}
TARGETS = {
    "rank": ("AuditDescent", "DyadicHostBound"),
    "proof": ("AuditGeometricRH",),
    "compare": ("AuditGeometricRH", "AuditPrevious", "AuditPublished"),
    "mizusawa-residues": ("AuditMizusawaResidue",),
    "mizusawa-units": ("AuditMizusawaUnits",),
    "mizusawa-rank": ("AuditMizusawaTower", "MizusawaSelector", "AuditDescent"),
    "mizusawa": ("AuditMizusawaTower", "MizusawaSelector", "AuditDescent", "AuditMizusawaRH",
                 "AuditMizusawaControl", "AuditGeometricRH"),
}
AUDITS = {
    "AuditDescent": "rank-names.txt",
    "AuditGeometricRH": "second-rh-names.txt",
    "AuditPrevious": "previous-rh-names.txt",
    "AuditPublished": "published-rh-names.txt",
    "AuditMizusawaResidue": "root-of-unity-names.txt",
    "AuditMizusawaUnits": "unit-parity-names.txt",
    "AuditMizusawaTower": "mizusawa-rank-names.txt",
    "AuditMizusawaRH": "mizusawa-rh-names.txt",
    "AuditMizusawaControl": "mizusawa-control-names.txt",
}
MIZUSAWA_MODULES = ("MizusawaCharacters", "MizusawaHostField", "MizusawaGenusField",
                    "MizusawaTower", "MizusawaSelector")
CHECK = {
    "rank": ("QuadraticSchreier", "QuadraticGenus", "BiquadraticDescent",
             "OrdinaryRayDescent", "NineIntegralTower", "DyadicHostBound"),
    "proof": ("QuadraticSchreier", "QuadraticGenus", "BiquadraticDescent",
              "OrdinaryRayDescent", "NineIntegralTower", "CaseTwoAutomorphy",
              "SecondSeedCount", "SecondSeedWindow", "FiniteFrameRH", "SecondSeedRH"),
    "mizusawa-residues": ("MizusawaUnitResidue",),
    "mizusawa-units": ("MizusawaUnitParity",),
    "mizusawa-rank": MIZUSAWA_MODULES,
    "mizusawa": (*MIZUSAWA_MODULES, "MizusawaWindowRH", "MizusawaNineControl", "SecondSeedRH"),
}
CORE_IMPORT = re.compile(r"^(?:public )?import\s+([\w.]+)\s*(?:--.*)?$")

def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(2 ** 20), b""):
            value.update(block)
    return value.hexdigest()

def ordered_sources(roots):
    sources = {}
    for folder in (HERE / "upstream", HERE / "lean"):
        for path in folder.rglob("*.lean"):
            name = ".".join(path.relative_to(folder).with_suffix("").parts)
            if name in sources:
                raise ValueError("Duplicate module: " + name)
            sources[name] = (folder, path)
    ordered = {}
    def visit(name):
        if name in ordered:
            return
        folder, path = sources[name]
        for line in path.read_text().splitlines():
            if line.startswith(("import ", "public import ")):
                match = CORE_IMPORT.fullmatch(line.strip())
                if not match:
                    raise ValueError(f"Unsupported import in {path.name}: {line}")
                if match[1] in sources:
                    visit(match[1])
        ordered[name] = (folder, path)
    for root in roots:
        visit(root)
    return ordered

def check_inputs(bins, mathlib, archives, sources, env):
    version = subprocess.check_output([bins / "lean", "--version"], text=True, env=env)
    if LEAN_REV not in version:
        raise ValueError("Expected Lean 4.33.1 at " + LEAN_REV)
    print(version.strip(), flush=True)
    with gzip.open(HERE / "evidence/mathlib-sources.sha256.gz", "rt") as checks:
        for line in checks:
            expected, rel = line.rstrip("\n").split("  ", 1)
            if digest(mathlib / rel) != expected:
                raise ValueError("Mathlib source differs: " + rel)
    if not all(path.is_dir() for path in archives):
        raise ValueError("Each archive path must be an extracted Lean library directory")
    # Bind the directly imported archive modules to the upstream object manifest.
    # The compressed archive itself is authenticated before extraction in REPLAY.md.
    imports = {name.replace(".", "/") + ".olean" for _, path in sources.values()
               for name in re.findall(r"^(?:public )?import\s+([\w.]+)", path.read_text(), re.MULTILINE)}
    for line in (HERE / "evidence/archive-imports.sha256").read_text().splitlines():
        expected, rel = line.split("  ", 1)
        if rel not in imports:
            continue
        paths = [path / rel for path in archives if (path / rel).is_file()]
        if not paths or digest(paths[0]) != expected:
            raise ValueError("Archive object is missing or differs: " + rel)

def checked_run(args, work, env, label):
    print(datetime.now(timezone.utc).isoformat(), label, flush=True)
    started = time.monotonic()
    subprocess.run(args, cwd=work, env=env, check=True)
    print(f"Passed {label} in {time.monotonic() - started:.1f}s", flush=True)

def check_audit(name, work, evidence):
    path = work / AUDITS[name]
    names = path.read_text().splitlines()
    if name == "AuditDescent":
        if len(names) != 77321:
            raise ValueError(f"Unexpected arithmetic dependency count: {len(names)}")
        return
    if name.startswith("AuditMizusawa"):
        filename, key = {
            "AuditMizusawaResidue": ("residues.json", "root_of_unity"),
            "AuditMizusawaUnits": ("units.json", "unit_parity"),
            "AuditMizusawaTower": ("arithmetic.json", "arithmetic_three"),
            "AuditMizusawaRH": ("comparison.json", "literature_three"),
            "AuditMizusawaControl": ("comparison.json", "literature_nine"),
        }[name]
        graph = json.loads((HERE / "mizusawa/evidence" / filename).read_text())["graphs"][key]
        count, expected = graph["count"], graph["sorted_sha256"]
    else:
        groups = evidence["comparisons"]
        count, expected = {
            "AuditGeometricRH": (evidence["candidate_count"], evidence["candidate_sorted_sha256"]),
            "AuditPrevious": (groups["single_inertia"]["count"], groups["single_inertia"]["sorted_sha256"]),
            "AuditPublished": (groups["published_principal"]["count"], groups["published_principal"]["sorted_sha256"]),
        }[name]
    actual = hashlib.sha256(("\n".join(sorted(names)) + "\n").encode()).hexdigest()
    if len(names) != count or actual != expected:
        raise ValueError(f"{name}: {len(names)} names, SHA-256 {actual}")
    print(f"{name}: {count:,} names, sorted SHA-256 {actual}", flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=TARGETS)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--archive", type=Path, action="append", default=[],
                        help="extracted .lake/build/lib/lean, repeat for a split local cache")
    parser.add_argument("--work", type=Path, help="parent directory for a fresh build and its audit reports")
    parser.add_argument("--list", action="store_true", help="list the local source closure without building")
    args = parser.parse_args()
    sources = ordered_sources(TARGETS[args.target])
    if args.list:
        for folder, path in sources.values():
            print(path.relative_to(HERE))
        return
    if not all((args.lean_bin, args.mathlib, args.work)):
        parser.error("supply --lean-bin, --mathlib and --work")
    if args.target != "mizusawa-residues" and not args.archive:
        parser.error("this target also needs the geometric proof --archive")
    bins, mathlib = args.lean_bin.resolve(), args.mathlib.resolve()
    archives = [path.resolve() for path in args.archive]
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(key, None)
    env["PATH"] = str(bins) + os.pathsep + env["PATH"]
    env["LEAN_NUM_THREADS"] = "1"
    check_inputs(bins, mathlib, archives, sources, env)
    args.work.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix=args.target + "-", dir=args.work.resolve()))
    print("Replay directory:", work, flush=True)
    built = work / "objects"
    built.mkdir()
    base = subprocess.check_output([bins / "lake", "env", "printenv", "LEAN_PATH"],
                                   cwd=mathlib, env=env, text=True).strip()
    packages = [(mathlib / path).resolve() for path in base.split(os.pathsep) if path]
    env["LEAN_PATH"] = os.pathsep.join(map(str, [built, *archives, *packages]))
    flags = ["--trust=0", "-j1", "-DwarningAsError=true", "-DmaxRecDepth=100000",
             "-DmaxHeartbeats=6000000", "-DsynthInstance.maxHeartbeats=200000"]
    audits = {}
    for name, (folder, path) in sources.items():
        cmd = [bins / "lean", *flags, "--root=" + str(folder)]
        if name in STRICT_IMPLICITS:
            cmd.append("-DautoImplicit=false")
        if name in AUDITS:
            audits[name] = [*cmd, path]
            continue
        obj = built / path.relative_to(folder).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        checked_run([*cmd, "-o", obj, path], work, env, "build " + name)
    modules = CHECK["proof" if args.target == "compare" else args.target]
    checked_run([bins / "leanchecker", "-v", *modules], work, env, "kernel " + ", ".join(modules))
    if args.target == "compare":
        # These endpoints have alternative implementations of the same upstream declarations.
        for name in ("SingleInertiaRH", "CheckAlpogePrincipalArchivedGeometryRH"):
            checked_run([bins / "leanchecker", "-v", name], work, env, "kernel " + name)
    evidence = json.loads((HERE / "evidence/comparison.json").read_text())
    for name, cmd in audits.items():
        checked_run(cmd, work, env, "audit " + name)
        check_audit(name, work, evidence)
    if args.target in ("mizusawa", "mizusawa-rank"):
        options = ["--arithmetic-only"] if args.target == "mizusawa-rank" else []
        checked_run([sys.executable, HERE / "mizusawa/compare.py", work, work / "comparison",
                     "--check", HERE / "mizusawa/evidence", *options], work, env, "compare rank-three dependencies")
    if args.target == "compare":
        checked_run([sys.executable, HERE / "compare.py", work / AUDITS["AuditPublished"],
                     work / AUDITS["AuditPrevious"], work / AUDITS["AuditGeometricRH"],
                     work / "comparison"], work, env, "compare dependency sets")
        if json.loads((work / "comparison/comparison.json").read_text()) != evidence:
            raise ValueError("Dependency comparison differs from the recorded evidence")
        for reference in sorted((HERE / "evidence").glob("*-*.txt.gz")):
            with gzip.open(reference, "rb") as old, gzip.open(work / "comparison" / reference.name, "rb") as new:
                if old.read() != new.read():
                    raise ValueError("Declaration difference changed: " + reference.name)

if __name__ == "__main__":
    main()
