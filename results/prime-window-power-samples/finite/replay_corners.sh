#!/bin/sh
set -eu
case "$(lean --version)" in
    *819816b2e0a3bf405af45ae5c7af2491d8f5bee6*) ;;
    *) echo "Use Lean 4.33.1 from the pinned Mathlib environment." >&2; exit 1 ;;
esac
src=$(cd "$(dirname "$0")" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
export LEAN_PATH="$scratch${LEAN_PATH:+:$LEAN_PATH}"
lean -DautoImplicit=false -R "$src" -o "$scratch/QuarticCorners.olean" "$src/QuarticCorners.lean"
leanchecker -v QuarticCorners
cat > "$scratch/QuarticAudit.lean" <<'EOF'
import QuarticCorners
#print axioms QuarticCorners.tent_hinges
#print axioms QuarticCorners.hinge_remainder
#print axioms QuarticCorners.mean_hinge_gap
#print axioms QuarticCorners.middle_corner
EOF
lean "$scratch/QuarticAudit.lean" > "$scratch/axioms.txt"
cat "$scratch/axioms.txt"
python3 - "$scratch/axioms.txt" <<'EOF'
import pathlib
import re
import sys

text = pathlib.Path(sys.argv[1]).read_text()
for theorem in ("tent_hinges", "hinge_remainder", "mean_hinge_gap", "middle_corner"):
    result = re.search(r"'QuarticCorners\." + theorem + r"' depends on axioms:\s*\[([^\]]*)\]", text)
    if result is None or set(result[1].replace(" ", "").split(",")) - {"propext", "Classical.choice", "Quot.sound"}:
        raise SystemExit(f"Axiom check failed for {theorem}")
print("Four corner theorems passed the kernel and axiom checks.")
EOF
