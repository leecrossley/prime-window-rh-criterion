"""Compare the tower and full theorem with the closed nine-generator proofs."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path


def canonical(names):
    return ("\n".join(sorted(names)) + "\n").encode("utf-8") if names else b""


def declarations(path, expected):
    names = set()
    with path.open(encoding="utf-8") as source:
        for line in source:
            name = line.rstrip("\n")
            if not name or name in names:
                raise ValueError(f"Empty or repeated declaration in {path}")
            names.add(name)
    digest = hashlib.sha256(canonical(names)).hexdigest()
    if len(names) != expected["count"] or digest != expected["sorted_sha256"]:
        raise ValueError(f"Unexpected declaration list in {path}")
    return names


def compare(before, after, label, output):
    added, removed = after - before, before - after
    if output is not None:
        output.mkdir(parents=True, exist_ok=True)
        for side, names in (("added", added), ("removed", removed)):
            path = output / f"{label}-{side}.txt.gz"
            path.write_bytes(gzip.compress(canonical(names), mtime=0))
    return {
        "nine": len(before), "three_from_units": len(after),
        "added": len(added), "removed": len(removed),
        "net_change": len(after) - len(before),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nine-tower", required=True, type=Path)
    parser.add_argument("--unit-tower", required=True, type=Path)
    parser.add_argument("--nine-rh", required=True, type=Path)
    parser.add_argument("--unit-rh", required=True, type=Path)
    parser.add_argument("--differences", type=Path, help="write the four sorted difference lists here")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    new = json.loads((here / "evidence/dependencies.json").read_text())
    old_tower = json.loads((here.parent / "evidence/arithmetic.json").read_text())["graphs"]
    old_rh = json.loads((here.parent / "evidence/comparison.json").read_text())["graphs"]
    tower = compare(declarations(args.nine_tower, old_tower["arithmetic_nine"]),
                    declarations(args.unit_tower, new["AuditTameEight"]), "tower", args.differences)
    rh = compare(declarations(args.nine_rh, old_rh["closed_nine"]),
                 declarations(args.unit_rh, new["AuditTameEightRH"]), "rh", args.differences)
    print(json.dumps({"tower": tower, "geometric_rh": rh}, indent=2))


if __name__ == "__main__":
    main()
