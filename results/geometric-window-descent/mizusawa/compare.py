"""Compare the closed nine-generator endpoint and two literature-input endpoints."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

FILES = {
    "closed_nine": "second-rh-names.txt",
    "literature_three": "mizusawa-rh-names.txt",
    "literature_nine": "mizusawa-control-names.txt",
    "arithmetic_three": "mizusawa-rank-names.txt",
    "arithmetic_nine": "rank-names.txt",
}

def read_names(path):
    with path.open(encoding="utf-8") as source:
        names = set()
        for line in source:
            name = line.rstrip("\n")
            if not name or name in names:
                raise ValueError(f"Empty or repeated declaration in {path}: {name!r}")
            names.add(name)
    return names

def canonical(names):
    return "".join(name + "\n" for name in sorted(names)).encode("utf-8")

def record(names):
    return {"count": len(names), "sorted_sha256": hashlib.sha256(canonical(names)).hexdigest()}

def tower_overlap(inputs, closed, candidate):
    old_tower = read_names(inputs / FILES["arithmetic_nine"])
    new_tower = read_names(inputs / FILES["arithmetic_three"])
    if not old_tower <= closed or not new_tower <= candidate:
        raise ValueError("A tower dependency is missing from its full endpoint")
    removed, added = old_tower - new_tower, new_tower - old_tower
    return {
        "tower_removals_still_reachable": len(removed & candidate),
        "tower_removals_absent_from_full_endpoint": len(removed - candidate),
        "tower_additions_already_reachable": len(added & closed),
        "tower_additions_new_to_full_endpoint": len(added - closed),
    }

def compare(inputs, output, target, baselines, filename):
    output.mkdir(parents=True, exist_ok=True)
    candidate = read_names(inputs / FILES[target])
    report = {"graphs": {target: record(candidate)}, "comparisons": {}}
    for label in baselines:
        reference = read_names(inputs / FILES[label])
        report["graphs"][label] = record(reference)
        if label == "closed_nine":
            report["arithmetic_overlap"] = tower_overlap(inputs, reference, candidate)
        dropped, added = reference - candidate, candidate - reference
        report["comparisons"][label] = {
            "dropped": len(dropped), "added": len(added),
            "net_fewer": len(reference) - len(candidate),
        }
        for side, names in (("dropped", dropped), ("added", added)):
            path = output / f"{label}-{side}.txt.gz"
            path.write_bytes(gzip.compress(canonical(names), mtime=0))
    (output / filename).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report

def check(output, evidence, baselines, filename):
    if json.loads((output / filename).read_text()) != json.loads((evidence / filename).read_text()):
        raise ValueError("The dependency counts or hashes differ from the published comparison")
    for label in baselines:
        for side in ("added", "dropped"):
            name = f"{label}-{side}.txt.gz"
            with gzip.open(output / name, "rb") as current, gzip.open(evidence / name, "rb") as published:
                if current.read() != published.read():
                    raise ValueError(f"The declaration list differs from the published {name}")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("audit_directory", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--check", type=Path, metavar="EVIDENCE")
    parser.add_argument("--arithmetic-only", action="store_true")
    args = parser.parse_args()
    comparisons = [("arithmetic_three", ("arithmetic_nine",), "arithmetic.json")]
    if not args.arithmetic_only:
        comparisons.append(("literature_three", ("closed_nine", "literature_nine"), "comparison.json"))
    for target, baselines, filename in comparisons:
        report = compare(args.audit_directory, args.output, target, baselines, filename)
        if args.check:
            check(args.output, args.check, baselines, filename)
        print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
