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
    "window": ("AuditSecondSeedWindow",),
    "proof": ("AuditGeometricRH",),
    "compare": ("AuditGeometricRH", "AuditSecondSeedWindow", "AuditPrevious", "AuditPublished"),
    "real-unit-rows": ("AuditRealUnitRows",),
    "tame-eight": ("AuditTameEight",),
    "tame-eight-rh": ("AuditTameEightRH",),
    "mizusawa-residues": ("AuditMizusawaResidue",),
    "mizusawa-units": ("AuditMizusawaUnits",),
    "mizusawa-rank": ("AuditMizusawaTower", "MizusawaSelector", "AuditDescent"),
    "mizusawa": ("AuditMizusawaTower", "MizusawaSelector", "AuditDescent", "AuditMizusawaRH",
                 "AuditMizusawaControl", "AuditGeometricRH"),
}
AUDITS = {
    "AuditDescent": "rank-names.txt",
    "AuditSecondSeedWindow": "window-names.txt",
    "AuditGeometricRH": "second-rh-names.txt",
    "AuditPrevious": "previous-rh-names.txt",
    "AuditPublished": "published-rh-names.txt",
    "AuditRealUnitRows": "real-unit-row-names.txt",
    "AuditTameEight": "tame-eight-names.txt",
    "AuditTameEightRH": "tame-eight-rh-names.txt",
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
    "window": ("CaseTwoAutomorphy", "SecondSeedCount", "SecondSeedWindow"),
    "proof": ("QuadraticSchreier", "QuadraticGenus", "BiquadraticDescent",
              "OrdinaryRayDescent", "NineIntegralTower", "CaseTwoAutomorphy",
              "SecondSeedCount", "SecondSeedWindow", "FiniteFrameRH", "SecondSeedRH"),
    "tame-eight-rh": ("CyclotomicEight", "TameEightWindowRH"),
    "real-unit-rows": ("RealCyclotomicUnit", "RealUnitFrobenius", "RealUnitResidueSigns",
                       "RealUnitPrimeSigns", "RealUnitSignRows"),
    "tame-eight": ("RealCyclotomicUnit", "RealUnitFrobenius", "RealUnitResidueSigns",
                   "RealUnitPrimeSigns", "RealUnitSignRows", "RaySignPlaces", "LocalTameUnitSigns",
                   "FiniteRayCharacter", "FiniteTameParity", "CofinalRayLayers", "TameUnitRelations",
                   "RayLayerSites", "TameRayBound", "CyclotomicEight"),
    "mizusawa-residues": ("MizusawaUnitResidue",),
    "mizusawa-units": ("MizusawaUnitParity",),
    "mizusawa-rank": MIZUSAWA_MODULES,
    "mizusawa": (*MIZUSAWA_MODULES, "MizusawaWindowRH", "MizusawaNineControl", "SecondSeedRH"),
}
ENDPOINTS = {
    "candidate": ("SecondSeedRH", "AuditGeometricRH"),
    "previous": ("SingleInertiaRH", "AuditPrevious"),
    "published": ("CheckAlpogePrincipalArchivedGeometryRH", "AuditPublished"),
    "window": (None, "AuditSecondSeedWindow"),
}
IMPORT = re.compile(r"^(?:(?:public|meta)\s+)*import\s+([\w.']+)\s*(?:--.*)?$")

def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(2 ** 20), b""):
            value.update(block)
    return value.hexdigest()

def direct_imports(path):
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if re.match(r"^(?:(?:public|meta)\s+)*import\b", line):
            match = IMPORT.fullmatch(line)
            if not match:
                raise ValueError(f"Unsupported import in {path.name}: {line}")
            yield match[1]

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
        for module in direct_imports(path):
            if module in sources:
                visit(module)
        ordered[name] = (folder, path)
    for root in roots:
        visit(root)
    return ordered

def check_archive_imports(sources, archives, packages, manifest):
    hashes = {}
    for line in manifest.read_text().splitlines():
        expected, rel = line.split("  ", 1)
        if rel in hashes or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError("Invalid or duplicate archive hash: " + rel)
        hashes[rel] = expected
    external = {module for _, path in sources.values() for module in direct_imports(path)} - sources.keys()
    search_path = [*archives, *packages]
    for module in sorted(external):
        rel = module.replace(".", "/") + ".olean"
        package = module.split(".")[0]
        # Lean 4.33 chooses the first directory containing the package root, even if the requested file is missing there.
        base = next((path for path in search_path
                     if (path / package).is_dir() or (path / (package + ".olean")).exists()), None)
        if base is None or not (base / rel).is_file():
            raise ValueError("Missing imported object: " + rel)
        if base in archives:
            if rel not in hashes:
                raise ValueError("Missing archive hash: " + rel)
            if digest(base / rel) != hashes[rel]:
                raise ValueError("Archive object differs: " + rel)
        elif rel in hashes:
            raise ValueError("Expected an archive object: " + rel)

def check_inputs(bins, mathlib, archives, env):
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
    if name == "AuditSecondSeedWindow":
        if len(names) != 390211 or len(set(names)) != len(names):
            raise ValueError(f"Unexpected window dependency list: {len(names)} entries")
        return
    if name in ("AuditRealUnitRows", "AuditTameEight", "AuditTameEightRH"):
        graph = json.loads((HERE / "mizusawa/tame-signs/evidence/dependencies.json").read_text())[name]
        count, expected = graph["count"], graph["sorted_sha256"]
    elif name.startswith("AuditMizusawa"):
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

def compare_dependencies(work, evidence, env):
    checked_run([sys.executable, HERE / "compare.py", work / AUDITS["AuditPublished"],
                 work / AUDITS["AuditPrevious"], work / AUDITS["AuditGeometricRH"],
                 work / "comparison"], work, env, "compare dependency sets")
    if json.loads((work / "comparison/comparison.json").read_text()) != evidence:
        raise ValueError("Dependency comparison differs from the recorded evidence")
    for reference in sorted((HERE / "evidence").glob("*-*.txt.gz")):
        with gzip.open(reference, "rb") as old, gzip.open(work / "comparison" / reference.name, "rb") as new:
            if old.read() != new.read():
                raise ValueError("Declaration difference changed: " + reference.name)

def comparison_stage(stage, sources, built):
    """Select the work for one hosted job and check the modules it received."""
    terminals = {name for name, _ in ENDPOINTS.values() if name}
    objects = set(sources) - AUDITS.keys()
    common = objects - terminals
    if not terminals <= objects:
        raise ValueError("Missing comparison endpoint")
    for name in objects:
        path = sources[name][1]
        if terminals.intersection(direct_imports(path)):
            raise ValueError(f"{name} imports a comparison endpoint")
    available = {".".join(f.relative_to(built).with_suffix("").parts) for f in built.rglob("*.olean")}
    if stage == "common":
        if available:
            raise ValueError("The common build needs an empty object directory")
        return common, (), set()
    checkpoints = comparison_checkpoints(sources)
    if stage in checkpoints:
        required, builds = checkpoints[stage]
        if available != required:
            raise ValueError(f"{stage} received different modules: {sorted(available ^ required)}")
        return builds, (), set()
    operation, endpoint = stage.split("-", 1)
    terminal, audit = ENDPOINTS[endpoint]
    required = common if operation == "build" or not terminal else common | {terminal}
    if available != required:
        raise ValueError(f"{stage} received different modules: {sorted(available ^ required)}")
    if operation == "build" and terminal:
        return {terminal}, (), set()
    if operation == "kernel" and terminal:
        modules = CHECK["proof"] if endpoint == "candidate" else (terminal,)
        return set(), (modules,), set()
    if operation == "audit":
        return set(), (), {audit}
    raise ValueError("Unknown comparison stage: " + stage)

RANK_ENDPOINTS = {
    "three": ("MizusawaWindowRH", "AuditMizusawaRH"),
    "control": ("MizusawaNineControl", "AuditMizusawaControl"),
    "closed": ("SecondSeedRH", "AuditGeometricRH"),
}


def geometry_checkpoints(*arithmetic_roots):
    """Divide the window and frame builds at their shared imports."""
    def closure(*roots):
        return set(ordered_sources(roots))

    arithmetic = closure(*arithmetic_roots, "NineIntegralTower", "AuditSlopeGraph")
    window = closure("SecondSeedWindow")
    frame = closure("FiniteFrameRH")
    basis = arithmetic | (window & frame)
    counts = basis | closure("SecondSeedCount")
    suppliers = basis | closure("CheckAlpogePrincipalArchivedRowSelection", "CheckAlpogeLocalThetaSupplier")
    window |= basis
    frame |= basis
    frame_inputs = frame - {"FiniteFrameRH"}
    if not counts <= window or not suppliers <= frame_inputs:
        raise ValueError("The window or frame checkpoint is missing imports")
    plan = {
        "build-basis": (set(), basis),
        "build-counts": (basis, counts - basis),
        "build-window": (counts, window - counts),
        "build-suppliers": (basis, suppliers - basis),
        "build-frame-inputs": (suppliers, frame_inputs - suppliers),
        "build-frame": (frame_inputs, frame - frame_inputs),
    }
    return plan, window, frame


def comparison_checkpoints(sources):
    plan, window, frame = geometry_checkpoints()
    previous = set(ordered_sources(("SingleInertiaWindow",))) - window
    plan["build-single-window"] = (window, previous)
    terminals = {module for module, _ in ENDPOINTS.values() if module}
    objects = sources.keys() - AUDITS.keys()
    common = window | frame | previous
    if common | terminals != objects or common & terminals or previous & frame:
        raise ValueError("The comparison checkpoints differ from the local source closure")
    return plan


def rank_plan(sources):
    """List the compiled inputs, new objects, kernel roots and audits for each rank job."""
    checkpoints, window, frame = geometry_checkpoints(*MIZUSAWA_MODULES)
    shared = window | frame
    terminals = {module for module, _ in RANK_ENDPOINTS.values()}
    if shared | terminals != sources.keys() - AUDITS.keys() or shared & terminals:
        raise ValueError("The rank stages differ from the local source closure")
    plan = {name: (required, builds, (), set()) for name, (required, builds) in checkpoints.items()}
    required, basis = checkpoints["build-basis"]
    plan["build-basis"] = (required, basis, (MIZUSAWA_MODULES,), {"AuditMizusawaTower", "AuditDescent"})
    for endpoint, (module, audit) in RANK_ENDPOINTS.items():
        ready = shared | {module}
        plan["build-" + endpoint] = (shared, {module}, (), set())
        plan["kernel-" + endpoint] = (ready, set(), ((module,),), set())
        plan["audit-" + endpoint] = (ready, set(), (), {audit})
    return plan


def rank_stage(stage, sources, built):
    required, builds, kernels, audits = rank_plan(sources)[stage]
    available = {".".join(f.relative_to(built).with_suffix("").parts) for f in built.rglob("*.olean")}
    if available != required:
        raise ValueError(f"{stage} received different modules: {sorted(available ^ required)}")
    return builds, kernels, audits


def unit_checkpoints(sources):
    plan, window, frame = geometry_checkpoints("CyclotomicEight")
    shared = window | frame
    terminal = "TameEightWindowRH"
    if shared | {terminal} != sources.keys() - AUDITS.keys() or terminal in shared:
        raise ValueError("The cyclotomic unit checkpoints differ from the local source closure")
    plan["build-unit-proof"] = (shared, {terminal})
    return plan


def unit_stage(stage, sources, built):
    objects = sources.keys() - AUDITS.keys()
    available = {".".join(f.relative_to(built).with_suffix("").parts) for f in built.rglob("*.olean")}
    if stage in ("build-inputs", "build-endpoint"):
        inputs = set(ordered_sources(("CyclotomicEight", "SecondSeedWindow")))
        required, builds = (set(), inputs) if stage == "build-inputs" else (inputs, objects - inputs)
        kernels, audits = (), set()
    elif stage == "kernel-endpoint":
        required, builds, kernels, audits = objects, set(), (CHECK["tame-eight-rh"],), set()
    elif stage == "audit-endpoint":
        required, builds, kernels, audits = objects, set(), (), {"AuditTameEightRH"}
    else:
        plan = unit_checkpoints(sources)
        if stage not in plan:
            raise ValueError("Unknown unit proof stage: " + stage)
        required, builds = plan[stage]
        kernels, audits = (), set()
    if available != required:
        raise ValueError(f"{stage} received different modules: {sorted(available ^ required)}")
    return builds, kernels, audits

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=TARGETS)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--archive", type=Path, action="append", default=[],
                        help="extracted .lake/build/lib/lean, repeat for a split local cache")
    parser.add_argument("--work", type=Path, help="parent directory for a fresh build and its audit reports")
    parser.add_argument("--stage", help="run one stage of a hosted proof replay")
    parser.add_argument("--stage-objects", type=Path, help="object directory for that stage")
    parser.add_argument("--list", action="store_true", help="list the local source closure without building")
    args = parser.parse_args()
    if bool(args.stage) != bool(args.stage_objects) or (args.stage and args.target not in ("compare", "tame-eight-rh", "mizusawa")):
        parser.error("--stage and --stage-objects require compare, tame-eight-rh or mizusawa")
    sources = ordered_sources(TARGETS[args.target])
    if args.list:
        for folder, path in sources.values():
            print(path.relative_to(HERE))
        return
    if not all((args.lean_bin, args.mathlib, args.work)):
        parser.error("supply --lean-bin, --mathlib and --work")
    if args.target not in ("mizusawa-residues", "real-unit-rows") and not args.archive:
        parser.error("this target also needs the geometric proof --archive")
    bins, mathlib = args.lean_bin.resolve(), args.mathlib.resolve()
    archives = [path.resolve() for path in args.archive]
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(key, None)
    env["PATH"] = str(bins) + os.pathsep + env["PATH"]
    env["LEAN_NUM_THREADS"] = "1"
    check_inputs(bins, mathlib, archives, env)
    base = subprocess.check_output([bins / "lake", "env", "printenv", "LEAN_PATH"],
                                   cwd=mathlib, env=env, text=True).strip()
    packages = [(mathlib / path).resolve() for path in base.split(os.pathsep) if path]
    core = subprocess.check_output([bins / "lean", "--print-libdir"], env=env, text=True).strip()
    check_archive_imports(sources, archives, [*packages, Path(core)], HERE / "evidence/archive-imports.sha256")
    args.work.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix=args.target + "-", dir=args.work.resolve()))
    print("Replay directory:", work, flush=True)
    built = args.stage_objects.resolve() if args.stage else work / "objects"
    built.mkdir(parents=True, exist_ok=bool(args.stage))
    if args.stage and args.target == "mizusawa":
        build_names, kernel_groups, audit_names = rank_stage(args.stage, sources, built)
    elif args.stage and args.target == "tame-eight-rh":
        build_names, kernel_groups, audit_names = unit_stage(args.stage, sources, built)
    elif args.stage:
        build_names, kernel_groups, audit_names = comparison_stage(args.stage, sources, built)
    else:
        build_names, audit_names = sources.keys() - AUDITS.keys(), sources.keys() & AUDITS.keys()
        kernel_groups = [CHECK["proof" if args.target == "compare" else args.target]]
        if args.target == "compare":
            # These endpoints have alternative implementations of the same upstream declarations.
            kernel_groups += [("SingleInertiaRH",), ("CheckAlpogePrincipalArchivedGeometryRH",)]
    env["LEAN_PATH"] = os.pathsep.join(map(str, [built, *archives, *packages]))
    flags = ["--trust=0", "-j1", "-DwarningAsError=true", "-DmaxRecDepth=100000",
             "-DmaxHeartbeats=6000000", "-DsynthInstance.maxHeartbeats=200000"]
    audits = {}
    for name, (folder, path) in sources.items():
        cmd = [bins / "lean", *flags, "--root=" + str(folder)]
        if name in STRICT_IMPLICITS:
            cmd.append("-DautoImplicit=false")
        if name in audit_names:
            audits[name] = [*cmd, path]
        if name not in build_names:
            continue
        obj = built / path.relative_to(folder).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        checked_run([*cmd, "-o", obj, path], work, env, "build " + name)
    for modules in kernel_groups:
        checked_run([bins / "leanchecker", "-v", *modules], work, env, "kernel " + ", ".join(modules))
    evidence = json.loads((HERE / "evidence/comparison.json").read_text())
    for name, cmd in audits.items():
        checked_run(cmd, work, env, "audit " + name)
        check_audit(name, work, evidence)
    if args.target in ("mizusawa", "mizusawa-rank") and not args.stage:
        options = ["--arithmetic-only"] if args.target == "mizusawa-rank" else []
        checked_run([sys.executable, HERE / "mizusawa/compare.py", work, work / "comparison",
                     "--check", HERE / "mizusawa/evidence", *options], work, env, "compare rank-three dependencies")
    if args.target == "compare" and not args.stage:
        compare_dependencies(work, evidence, env)

if __name__ == "__main__":
    main()
