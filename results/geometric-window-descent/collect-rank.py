"""Collect all five declaration lists from the hosted rank comparison."""
import argparse
import gzip
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

from replay import AUDITS, HERE, TARGETS, check_audit, ordered_sources, rank_plan


def collect(parts, output, revision):
    sources = ordered_sources(TARGETS["mizusawa"])
    plan = rank_plan(sources)
    evidence = json.loads((HERE / "evidence/comparison.json").read_text())
    output.mkdir(parents=True, exist_ok=True)
    replayed = set()
    with tempfile.TemporaryDirectory() as folder, (output / "replay.log").open("w") as log:
        work = Path(folder)
        for stage, (_, builds, kernels, audits) in plan.items():
            part = parts / f"geometric-part-{stage}-{revision}"
            transcript = (part / "replay.log").read_text()
            lines = transcript.splitlines()
            completed = [line[7:].rsplit(" in ", 1)[0] for line in lines if line.startswith("Passed ")]
            expected = [f"build {name}" for name in builds]
            expected.extend("kernel " + ", ".join(group) for group in kernels)
            expected.extend(f"audit {name}" for name in audits)
            if revision not in lines or sorted(completed) != sorted(expected):
                raise ValueError(f"Incomplete or unexpected work in {stage}")
            log.write(f"\n[{stage}]\n{transcript}\n")
            for audit in audits:
                filename = AUDITS[audit]
                archive = part / (filename + ".gz")
                with gzip.open(archive, "rb") as src, (work / filename).open("wb") as dst:
                    shutil.copyfileobj(src, dst)
                check_audit(audit, work, evidence)
                shutil.copyfile(archive, output / archive.name)
                replayed.add(audit)
        if replayed != (sources.keys() & AUDITS.keys()):
            raise ValueError("Missing a rank comparison audit")
        log.flush()
        start = time.monotonic()
        subprocess.run([sys.executable, HERE / "mizusawa/compare.py", work, work / "comparison",
                        "--check", HERE / "mizusawa/evidence"], check=True, stdout=log)
        log.write(f"Passed compare rank-three dependencies in {time.monotonic() - start:.1f}s\n")
        shutil.copytree(work / "comparison", output / "comparison")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parts", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("revision")
    args = parser.parse_args()
    collect(args.parts, args.output, args.revision)
