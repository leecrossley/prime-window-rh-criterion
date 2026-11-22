"""Compare complete Lean proof-term and type dependencies for ordinary RH."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

NAMED = [
    "UpperTheory.V.HV.DescentVanishingReductions.sp4In0_alt",
    "UpperTheory.V.Cu.main4_alt",
    "UpperTheory.V.Cu.modularity_rank_four_of_promodularity_case_three",
    "UpperTheory.V.Cu.promodularity_case_three_of_chain_reduction",
    "UpperTheory.V.Cu.chainIV_alt",
    "UpperTheory.V.Z.Win.Birth.fourth_initial_of_prints_h",
    "UpperTheory.V.Two.baseRk",
    "UpperTheory.V.Two.quadStep",
    "UpperTheory.V.Two.idxTwo",
    "UpperTheory.V.Ws.proMod_of_pmEx_of_ctx2_of_kPair_of_star",
    "UpperTheory.V.Ws.exists_iwasawaRank_bound_of_ferreroWashington",
    "UpperTheory.V.FW.ferreroWashington",
    "UpperTheory.V.Win.partA",
    "GlobalTheory.T.even_theta_chain_spanned_params_of_value_independent",
    "GlobalTheory.T.theta_chain_last_step_intertwines_matched_hecke",
    "GlobalTheory.T.theta_chain_occurring_params_norm_half_rank_bound",
    "RiemannReduction.GaussianTower.host_tower_nine",
    "RiemannReduction.QuadraticDescent.quadratic_genus_bound",
    "RiemannReduction.QuadraticDescent.rank_le_twice_sub_one",
    "RiemannReduction.SymplecticTwo.automorphy_of_second_seed",
]

def canonical(names):
    return ("\n".join(sorted(names)) + "\n").encode()

def read_names(path):
    with path.open() as source:
        return {line.rstrip("\n") for line in source}

def digest(names):
    return hashlib.sha256(canonical(names)).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("published", type=Path)
    parser.add_argument("single_inertia", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    candidate = read_names(args.candidate)
    report = {
        "candidate_count": len(candidate),
        "candidate_sorted_sha256": digest(candidate),
        "comparisons": {},
        "named_dependencies": {name: {"candidate": name in candidate} for name in NAMED},
    }
    for label, path in (("published_principal", args.published), ("single_inertia", args.single_inertia)):
        baseline = read_names(path)
        for name in NAMED:
            report["named_dependencies"][name][label] = name in baseline
        dropped, added = baseline - candidate, candidate - baseline
        report["comparisons"][label] = {
            "count": len(baseline), "added": len(added), "dropped": len(dropped),
            "net_fewer": len(baseline) - len(candidate), "sorted_sha256": digest(baseline)
        }
        for kind, group in (("added", added), ("dropped", dropped)):
            (args.output / f"{label}-{kind}.txt.gz").write_bytes(gzip.compress(canonical(group), mtime=0))
    (args.output / "comparison.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
