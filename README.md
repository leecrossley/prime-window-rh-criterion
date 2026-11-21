# An ordinary-prime window criterion for the Riemann hypothesis

This is a Lean proof that the Riemann hypothesis (RH) follows from a one-sided inequality about ordinary primes. If the weighted sum of primes between $y$ and $4y$ stays at or below $2y\log2$ throughout long windows that occur arbitrarily far out, then RH holds.

The hypothesis is one-sided and involves only primes, with no prime powers or zeta zeros. It is needed only on a sparse set of windows. A companion repository proves the forward direction: under RH the inequality holds, strictly, at every scale.

## Statement

Fix any $\delta>0$. Suppose arbitrarily large $X$ satisfy $P(x/4)\le (x/2)\log 2$ for every real $x\in[X,X^{1+\delta}]$. Then the Riemann hypothesis holds. A single fixed positive $\delta$ suffices.

For real $y>0$, set

$$
 W(t)=
 \begin{cases}
 2(1-1/t) & 1 < t\le2,\\
 4/t-1 & 2 < t < 4,\\
 0 & \text{otherwise},
 \end{cases}
 \qquad
 P(y)=\sum_{y < p < 4y}(\log p)W(p/y).
$$

Only actual primes enter $P$. A prime at $2y$ has weight one. Both exterior endpoints have weight zero. For example, using the primes from 101 through 397 gives $P(100)\approx131.3471$, compared with $200\log2\approx138.6294$.

In Lean the theorem is `ThetaTransfer.rh_of_prime_sign_windows` in [PrimeWindow.lean](PrimeWindow.lean). It concludes Mathlib's `RiemannHypothesis`, and no theorem asserting RH is used as an input.

## How the proof goes

1. With prime powers included, the weighted sum is a three-term difference of the ramp $R(y)=\sum_n\Lambda(n)(y/n-1)_+$ at $y$, $2y$ and $4y$.
2. In log coordinates that difference multiplies the Laplace transform by $m(s)=(1-2^{-s})(2\cdot 2^{-s}-1)$, which has no zero for $0<\Re s<1$. Every pole coming from a zeta zero therefore survives, and the source release's Landau window criterion still applies. [Transfer proof](DelayedPole.lean)
3. Passing from prime powers to primes costs at most $\psi(4y)-\vartheta(4y)\ll\sqrt{4y}$, which the criterion absorbs. A zero with real part above $1/2$ would then contradict the window hypothesis.

The argument is written out in [PROOF.md](PROOF.md).

## Verification

The proof applies the source release's Landau window criterion and proves the premise of the functional-equation reduction. [Alpöge's note](https://alpo.ge/remark.pdf), [Andrew Sutherland's source and verification record](https://math.mit.edu/~drew/grh/)

For a fresh build on x86-64 Linux with Git, curl, tar, zstd and Python 3.9 or later, run

```sh
bash verify-linux.sh
```

This checks the [SHA-256 manifest](SHA256SUMS), downloads the pinned dependencies and compares the resulting kernel and axiom summary with the [recorded run](evidence/check.txt). The environment is fixed by Lean 4.33.1, a pinned Mathlib commit and a pinned source archive. Exact versions, hashes and the route for an existing installation are in [PROOF.md](PROOF.md#reproducing-the-lean-check). [Tagged publication](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/v1.0.1)

## Related work

- Daniel R. Johnston proves an RH criterion using the sign of the integral of the Chebyshev error from 2 to $x$ (Theorem 1.2). [Johnston](https://arxiv.org/abs/2201.06184)
- Masatoshi Suzuki gives one-sided criteria for other weighted von Mangoldt sums. [Suzuki](https://arxiv.org/abs/2411.07436)
- Dudek, Grenié and Molteni take an additive second difference of an integrated Chebyshev function to obtain a triangular weight in their work on prime gaps. The weight here uses a multiplicative interval $(y,4y)$. [Dudek, Grenié and Molteni](https://sites.unimi.it/molteni/research/papers-pdf/36-molteni-Primes_in_explicit_short_intervals_on_RH.pdf)
- Pedro Caceres has also studied rigorous finite-range verification for a cumulative weighted sum over prime powers. [Caceres](https://hexagonmath.org/2610.00661v2)

## Related result

[The forward direction under RH, with finite certificates](https://github.com/leecrossley/dyadic-prime-deficit/tree/v1.0.1)
