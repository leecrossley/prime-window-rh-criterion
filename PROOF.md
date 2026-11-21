# Proof: an ordinary-prime window criterion for the Riemann hypothesis

This is the written argument behind the [summary](README.md). The Lean files are the checked version.

For real $y>0$, set

$$
 W(t)=
 \begin{cases}
 2(1-1/t) & 1 \lt t\le2,\\
 4/t-1 & 2 \lt t \lt 4,\\
 0 & \text{otherwise},
 \end{cases}
 \qquad
 P(y)=\sum_{y \lt p \lt 4y}(\log p)W(p/y).
$$

Write $A(y)=\sum_n\Lambda(n)W(n/y)$ when prime powers are included.

bramble_trace's revision 24 already gives sign changes on every sufficiently late power window if RH fails and the resulting converse even when testing on squares. With $x=2y$, the present deficit is three times their ordinary-prime deficit. This note formalises the real-window converse. [Earlier proof](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24)

## Transfer to the tent weight

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

The forward direction says $P(y)<2y\log2$ under RH. For the **converse**, apply the same lemma to the *surplus* $A(y)-2y\log2$. Zeta has no real zero in the open strip, so negating the residues preserves all its pole hypotheses. The weight lies between zero and one. Hence

$$
 0\le A(y)-P(y)\le\psi(4y)-\vartheta(4y)\ll \sqrt{4y}.
$$

On any whole window with $P(y)\le 2y\log2$, the surplus is at most $C\sqrt{4y}$. For every fixed $1/2<\theta<1$, this is at most $(4y)^\theta$ eventually. In log coordinates the decaying weight cancels the pointwise majorant, leaving window length $\delta U\le e^{\eta U}$ for every fixed $\eta>0$ eventually. `landau_window` rules out a zero with real part greater than $\theta$. Taking $\theta$ between $1/2$ and a proposed zero gives the claim. The proof of this implication uses no RH assumption. [Prime-power bound](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L596), [Prime-window proof](PrimeWindow.lean)

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
