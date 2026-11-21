"""Replay the local theorems and their pinned upstream dependencies under lake env."""
import argparse
import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path, help="extracted, pinned lean/src directory")
    args = parser.parse_args()
    source = args.upstream.resolve()
    root = Path(__file__).resolve().parent
    local = root / "lean"
    compiler = subprocess.check_output(["lean", "--version"], text=True).strip()
    if "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" not in compiler:
        raise ValueError("expected Lean 4.33.1, commit 819816b2")
    sources = {}
    pins = dict(line.split() for line in (root/"evidence"/"upstream.sha256").read_text().splitlines())

    def visit(name):
        if name in sources or name.startswith(("Mathlib.", "Lean.", "Init.")) or name == "Mathlib":
            return
        rel = Path(*name.split(".")).with_suffix(".lean")
        src = local/rel
        if not src.is_file():
            src = source/rel
            expected = pins.get(name)
            if not expected or hashlib.sha256(src.read_bytes()).hexdigest() != expected:
                raise ValueError(f"unexpected upstream source for {name}")
        for line in src.read_text().splitlines():
            if line.startswith("import "):
                for dep in line.split()[1:]:
                    visit(dep)
        sources[name] = src

    visit("FifthWindows")
    visit("PowerSamples")
    with tempfile.TemporaryDirectory() as scratch:
        build = Path(scratch)
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join((scratch, env.get("LEAN_PATH", "")))
        for name, src in sources.items():
            out = (build/Path(*name.split("."))).with_suffix(".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            base = local if src.is_relative_to(local) else source
            print("Checking", name, flush=True)
            subprocess.run(["lean","-j2","--tstack=400000","-DautoImplicit=false",
                            "-DrelaxedAutoImplicit=false","-DmaxHeartbeats=4000000",
                            "-R",str(base),"-o",str(out),str(src)], env=env, check=True)
        subprocess.run(["leanchecker", "-v", *sources], env=env, check=True)
        names = ["RiemannReduction.PrimeGrid.rh_of_square_sqrt_windows",
                 "RiemannReduction.PrimeGrid.rh_of_doubled_prime_sqrt_windows",
                 "PowerSamples.right_edge", "PowerSamples.window_excludes",
                 "PowerSamples.term_increment", "PowerSamples.rh_of_power_samples_of_increment"]
        audit = build/"Audit.lean"
        audit.write_text("import FifthWindows\nimport PowerSamples\n"+
                         "".join(f"#print axioms {name}\n" for name in names))
        output = subprocess.check_output(["lean",str(audit)],env=env,text=True)
        for name in names:
            matched = re.search(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]", output)
            if not matched or set(matched[1].replace(" ","").split(",")) - {"propext","Classical.choice","Quot.sound"}:
                raise ValueError(f"axiom audit failed for {name}")
        print(output.strip())
    print(f"Kernel replay passed for {len(sources)} modules.")
    print(compiler)


if __name__ == "__main__":
    main()
