# Proof: a delayed-difference window criterion for Dirichlet families

This is the written argument behind the [summary](README.md). The Lean file is the checked version.

## Why the poles survive

The original ramp is $R(y)=\sum_n\Lambda(n)(y/n-1)_+$. If $G(y)=R(y)-y\log y+(1+\gamma)y$, direct subtraction gives

$$
 A(y)=R(4y)-3R(2y)+2R(y),\qquad
 D_\Lambda(y):=2y\log 2-A(y)=-G(4y)+3G(2y)-2G(y).
$$

Both the linear term and every contribution from $n\le y$ cancel. With $g(u)=G(e^u)$, $c=\log2$, delay a function by $a$ and set the delayed function to zero for $u\le a$. The transformed difference $-g(u)+3g(u-c)-2g(u-2c)$, with these cutoffs, equals $D_\Lambda(e^u/4)$ for $u>2c$. Its unilateral Laplace transform is the old transform times

$$
  m(s)=(1-2^{-s})(2\cdot 2^{-s}-1).
$$

For $0<\Re s<1$, $1/2<|2^{-s}|<1$, so every pole survives. For real $s$ in that interval $m(s)>0$, as required by the original `PoleData` structure. An analytic, nonvanishing multiplier preserves a simple pole with residue multiplied by $m(\rho)$. A finite initial interval has no effect on the window hypothesis. These observations transfer the archive's criterion to each admissible positive-weight Dirichlet family. [Original pole data](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean#L15), [Transfer proof](DelayedPole.lean)


The family observable is `gm F`. The ramp calculation above describes its zeta specialization. In general the proof uses the family's `PoleData` and `WindowHypU` as defined in the pinned source. [Window and pole definitions](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean)

## Reproducing the Lean check

The recorded run used Lean 4.33.1 on arm64 macOS. It freshly elaborated this repository's modules, used compiled dependencies from the pinned sources, replayed each local module with `leanchecker`, and inspected the named declarations' axioms. The receipt records the module counts and axiom lists. Compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` fix the environment. [Lean release](https://github.com/leanprover/lean4/releases/tag/v4.33.1), [Mathlib revision](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)

The source archive for the transitive upstream modules is pinned by SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. [Source release](https://github.com/CocoSgt/riemann-hypothesis-lean/releases/tag/v2026-11-20), [Readable source mirror](https://github.com/Deicyde/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005)

For a fresh build on x86-64 Linux with Git, curl, tar, zstd and Python 3.9 or later, run

```sh
bash verify-linux.sh
```

With the pinned toolchain and Mathlib cache already installed, use

```sh
cd /path/to/pinned/mathlib4
lake env python3 /path/to/repository/verify.py /path/to/upstream/lean/src /path/to/build
```

The build directory can begin empty. Reusing a dependency cache requires the same sources and compiler. A successful run ends with the kernel and axiom summary recorded in [evidence/check.txt](evidence/check.txt).

The Linux entry point checks the SHA-256 manifest before downloading the pinned dependencies and compares the resulting kernel and axiom summary with the recorded run.
