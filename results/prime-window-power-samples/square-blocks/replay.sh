#!/bin/sh
set -eu
cd "$(dirname "$0")"
python_bin=${PYTHON:-python3}
"$python_bin" -B -c 'import sys; sys.exit(0 if __debug__ else "Square-block certificates require Python assertions. Disable optimisation.")'
for bits in 160 256; do
    "$python_bin" -B check_discrepancy.py --bits "$bits"
    "$python_bin" -B check_shift_parity.py --bits "$bits"
done
for bits in 160 224; do
    "$python_bin" -B check_surviving_zeros.py --bits "$bits"
done
for bits in 128 192; do
    "$python_bin" -B check_short_arithmetic.py --bits "$bits"
    "$python_bin" -B check_median_exceptions.py --bits "$bits"
done
