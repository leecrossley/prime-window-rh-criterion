"""Collect the four audited lists produced by one hosted comparison."""
import argparse
from contextlib import redirect_stdout
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile

from replay import AUDITS, CHECK, ENDPOINTS, HERE, TARGETS, check_audit, compare_dependencies, comparison_checkpoints, ordered_sources


def collect(parts, output, revision):
    evidence = json.loads((HERE / "evidence/comparison.json").read_text())
    sources = ordered_sources(TARGETS["compare"])
    checkpoints = comparison_checkpoints(sources)
    stages = {stage: ["build " + name for name in builds] for stage, (_, builds) in checkpoints.items()}
    if (parts / f"geometric-part-common-{revision}").is_dir():
        if any((parts / f"geometric-part-{name}-{revision}").is_dir() for name in stages):
            raise ValueError("Found both the single and split common builds")
        stages = {"common": [label for labels in stages.values() for label in labels]}
    for endpoint, (terminal, audit) in ENDPOINTS.items():
        if terminal:
            stages["build-" + endpoint] = ["build " + terminal]
            modules = CHECK["proof"] if endpoint == "candidate" else (terminal,)
            stages["kernel-" + endpoint] = ["kernel " + ", ".join(modules)]
        stages["audit-" + endpoint] = ["audit " + audit]
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as temp, (output / "replay.log").open("w") as log:
        work = Path(temp)
        for stage, labels in stages.items():
            folder = parts / f"geometric-part-{stage}-{revision}"
            transcript = (folder / "replay.log").read_text()
            lines = transcript.splitlines()
            completed = [line[7:].rsplit(" in ", 1)[0] for line in lines if line.startswith("Passed ")]
            if revision not in lines or sorted(completed) != sorted(labels):
                raise ValueError(f"Incomplete or unexpected work in {stage}")
            log.write(f"\n[{stage}]\n{transcript}\n")
            if stage.startswith("audit-"):
                name = ENDPOINTS[stage.removeprefix("audit-")][1]
                filename = AUDITS[name]
                archive = folder / (filename + ".gz")
                with gzip.open(archive, "rb") as source, (work / filename).open("wb") as dest:
                    shutil.copyfileobj(source, dest)
                check_audit(name, work, evidence)
                if name == "AuditSecondSeedWindow":
                    names = sorted((work / filename).read_bytes().splitlines())
                    actual = hashlib.sha256(b"\n".join(names) + b"\n").hexdigest()
                    if actual != "bd7b33add74d45a7d62f265018d38b110fd655b1253b8aa27ca7ad02fd2b6bd7":
                        raise ValueError("The window differs from the published Linux replay")
                shutil.copyfile(archive, output / archive.name)
        with redirect_stdout(log):
            compare_dependencies(work, evidence, os.environ)
        shutil.copytree(work / "comparison", output / "comparison")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parts", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("revision")
    args = parser.parse_args()
    collect(args.parts, args.output, args.revision)
