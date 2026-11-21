# A delayed-difference window criterion for Dirichlet families

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24410862.svg)](https://doi.org/10.5281/zenodo.24410862)

This is a Lean proof of a reusable step. Take the observable $g$ attached to a family of Dirichlet $L$-functions and form the delayed difference $-g(u)+3g(u-\log2)-2g(u-2\log2)$. The proof shows that this keeps every pole the upstream Landau-type criterion relies on. For $0<\theta<1$, a one-sided bound of exponent $\theta$ for the difference on suitable windows then rules out zeros with real part above $\theta$ for every member of the family.

The delayed difference is what a compactly supported tent weight looks like in log coordinates, so this is the step that lets the criterion be applied to such a weight. The specialization to a sum over ordinary primes is in a companion repository.

## Statement

For an admissible Dirichlet family $F$, applying the delayed difference $-g(u)+3g(u-\log2)-2g(u-2\log2)$ with zero-extended delays preserves the relevant pole data. For $0<\theta<1$ and $\delta>0$, the upstream one-sided window hypothesis on that difference implies zero-freeness of every member for $\Re s>\theta$.

In Lean these are `ThetaTransfer.compactDifference_poleData` and `ThetaTransfer.compactDifference_zeroFree` in [DelayedPole.lean](DelayedPole.lean). The family observable is `gm F`, and the proof uses the family's `PoleData` and `WindowHypU` as defined in the pinned source. [Window and pole definitions](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean)

## How the proof goes

1. Delay a function by $a$ and set the delayed function to zero for $u\le a$. The difference then multiplies the unilateral Laplace transform by $m(s)=(1-2^{-s})(2\cdot 2^{-s}-1)$.
2. For $0<\Re s<1$, $1/2<|2^{-s}|<1$, so every pole survives. For real $s$ in that interval $m(s)>0$, as required by the original `PoleData` structure.
3. An analytic, nonvanishing multiplier preserves a simple pole with residue multiplied by $m(\rho)$. A finite initial interval has no effect on the window hypothesis.

For zeta and $u>2\log2$, the difference is the prime-power deficit of the dyadic tent at $e^u/4$. That calculation is in [PROOF.md](PROOF.md).

## Verification

The generic pole transfer and its Dirichlet-family application are both checked. The window bound is a hypothesis on the transformed observable. [Alpöge's note](https://alpo.ge/remark.pdf), [Andrew Sutherland's source and verification record](https://math.mit.edu/~drew/grh/)

For a fresh build on x86-64 Linux with Git, curl, tar, zstd and Python 3.9 or later, run

```sh
bash verify-linux.sh
```

This checks the [SHA-256 manifest](SHA256SUMS), downloads the pinned dependencies and compares the resulting kernel and axiom summary with the [recorded run](evidence/check.txt). The environment is fixed by Lean 4.33.1, a pinned Mathlib commit and a pinned source archive. Exact versions, hashes and the route for an existing installation are in [PROOF.md](PROOF.md#reproducing-the-lean-check). [Latest release](https://github.com/leecrossley/dirichlet-window-transfer/releases/latest)

## Related result

[Specialization to a sum of ordinary rational primes](https://github.com/leecrossley/prime-window-rh-criterion/tree/v1.0.1)
