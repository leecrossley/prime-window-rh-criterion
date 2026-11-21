"""Build the signed Möbius and cutoff proofs from source in the pinned Mathlib environment."""

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from graphlib import TopologicalSorter
from hashlib import sha256
import os
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
POWER = HERE.parent.parent
COMPILER = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
AUDITS = ("FourthSignedAudit", "FiniteQuarticAudit", "CutoffAudit")
KERNEL = ("FourthPowerSpacing", "FourthSignExcursions", "FourthSignedCriterion",
          "EarlyBandQuadrature", "EarlySmallDivisors", "EarlySquareError",
          "FiniteQuarticBudget", "FiniteHundredBlocks", "CutoffVariation", "BalancedCutoffs")
PACKAGES = {"Mathlib", "Lean", "Std", "Batteries", "Aesop", "Init", "Qq",
            "Lake", "Plausible", "ProofWidgets", "ImportGraph"}
IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)\s+)*import[ \t]+([\w.]+(?:[ \t]+[\w.]+)*)", re.M)


def proof_graph(upstream):
    pins = {}
    for manifest in (POWER/"evidence/upstream.sha256", HERE/"upstream.sha256"):
        for line in manifest.read_text().splitlines():
            name, digest = line.split()
            if name in pins:
                raise ValueError(f"duplicate upstream pin for {name}")
            pins[name] = digest
    sources, imports = {}, {}

    def visit(name):
        if name in sources:
            return
        relative = Path(*name.split(".")).with_suffix(".lean")
        if name in pins:
            base = upstream
        else:
            base = HERE/"lean" if (HERE/"lean"/relative).is_file() else POWER/"lean"
        path = base/relative
        data = path.read_bytes()
        if name in pins and sha256(data).hexdigest() != pins[name]:
            raise ValueError(f"upstream checksum mismatch for {name}")
        sources[name] = (base, path)
        imports[name] = {dep for group in IMPORT.findall(data.decode()) for dep in group.split()
                         if dep.split(".")[0] not in PACKAGES}
        for dep in imports[name]:
            visit(dep)

    for name in AUDITS:
        visit(name)
    return sources, imports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path, help="pinned upstream lean/src directory")
    parser.add_argument("out", type=Path, help="empty directory for newly built objects")
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    compiler = subprocess.check_output(["lean", "--version"], text=True).strip()
    if COMPILER not in compiler:
        raise ValueError(f"unexpected compiler: {compiler}")
    upstream, out = args.upstream.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        raise ValueError(f"use an empty output directory: {out}")
    sources, imports = proof_graph(upstream)
    nup = sum(base == upstream for base, path in sources.values())
    print(compiler, flush=True)
    print(f"Verified {nup} upstream hashes; building {len(sources)-nup} project modules.", flush=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(out), env.get("LEAN_PATH", "")])

    def compile_module(name):
        base, path = sources[name]
        output = (out/Path(*name.split("."))).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        opts = ["--tstack=400000", "-j2", "-DautoImplicit=false", "-DmaxHeartbeats=4000000"]
        if base == upstream:
            opts += ["-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true"]
            if name.startswith(("GroundTheory.LocalFields.", "GroundTheory.GlobalFields.")):
                opts += ["-DsynthInstance.maxHeartbeats=400000"]
        subprocess.run(["lean", *opts, "-R", str(base), "-o", str(output), str(path)],
                       env=env, check=True)
        print(f"Built {name}", flush=True)

    order = TopologicalSorter(imports)
    order.prepare()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = {}
        while order.is_active():
            for name in order.get_ready():
                pending[pool.submit(compile_module, name)] = name
            finished, _ = wait(pending, return_when=FIRST_COMPLETED)
            for job in finished:
                job.result()
                order.done(pending.pop(job))
    subprocess.run(["leanchecker", "-v", *KERNEL], env=env, check=True)
    print(f"Kernel replay passed for {len(KERNEL)} result modules and all three declaration audits.", flush=True)


if __name__ == "__main__":
    main()
