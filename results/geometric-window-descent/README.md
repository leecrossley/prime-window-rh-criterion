# Quadratic descent in the geometric proof of ordinary RH

Alpöge’s geometric proof, specialised to the principal character by D. B. Sanftenberg, uses a tower of number fields to choose an interval on which several cohomology groups are controlled. The preceding Lean implementation used an upper bound of 24 generators for the tower module at the prime two. The character-transfer argument here uses nine. An earlier class-group calculation gives the sharp rank three for the ordinary class module of this tower. The second change concerns the rank-four symplectic count. Its representations satisfy the second automorphy case, so its second seed suffices. Both changes reach `RiemannReduction.ConductorOne.rh_from_second_seed`, whose type is Mathlib’s `RiemannHypothesis` with no input hypotheses. [Earlier class-group calculation](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=29) [Closing proof](lean/SecondSeedRH.lean) [Replay](REPLAY.md)

## Quadratic descent

Fix auxiliary primes $q\equiv3\pmod 8$ and $d\equiv7\pmod{16}$. Over the $2$-power cyclotomic tower, the two quadratic characters cut out the extensions obtained by adjoining $\sqrt{-q}$ and $\sqrt{-d}$. Their product cuts out the intermediate extension with $\sqrt{qd}$. The argument first descends through this intermediate field and then through the common kernel of the two characters. [Biquadratic descent](lean/BiquadraticDescent.lean) · [Application to the auxiliary primes](lean/OrdinaryRayDescent.lean)

On the cyclotomic base, the only everywhere-unramified quadratic character is the trivial one. Allowing ramification at $q,d$ gives at most six independent characters, from at most two inertia orbits above $q$ and four above $d$. Transfer across the first quadratic step saves one dimension, giving a bound of five. The disjoint odd ramification of the two quadratic characters makes the last step unramified. The index-two estimate sends a positive bound $r$ to $2r-1$, hence $2\cdot5-1=9$. This bounds the number of generators over $\mathbb Z_2$ for the tower module used in the interval calculation. [Transfer](lean/QuadraticGenus.lean) · [Index-two estimate](lean/QuadraticSchreier.lean) · [Nine-generator theorem](lean/NineIntegralTower.lean) · [Earlier 24-generator theorem](lean/DyadicHostBound.lean)

There is a concrete effect on interval selection. Its parameter is $J=2^{R+2}(2C_K C_t/\varepsilon)^R$. With the other inputs fixed, this changes the exponent of $1/\varepsilon$ from 24 to 9. [Interval selector](lean/SingleTowerGrid.lean)

## Second seed

The counting argument supplies `Ctx2` for every symplectic datum it passes to automorphy. We apply the corresponding promodularity theorem directly, then its purity and automorphy consequences. The old case-three argument and its fourth seed disappear from the dependencies of the closed RH theorem. Ferrero–Washington at odd residual primes and all three tracked theta-chain comparisons remain. [Case-two proof](lean/CaseTwoAutomorphy.lean) · [Rank-four count](lean/SecondSeedCount.lean) · [Cohomology window](lean/SecondSeedWindow.lean)

| Closed proof of ordinary RH | Distinct reachable Lean declarations |
| --- | ---: |
| Sanftenberg’s published principal-character proof | 1,477,932 |
| Intermediate version using the 24-generator tower | 1,477,680 |
| Nine-generator tower and case-two automorphy | 1,476,889 |

The audit follows types and proof terms. Against the published baseline, 1,280 declarations drop out and 237 enter. It checks the literal Mathlib conclusion, the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, and the absence of any other reachable theorem with the bare type `RiemannHypothesis`. The counts depend on this implementation. [Audit](lean/AuditGeometricRH.lean) · [Counts, hashes and named dependencies](evidence/comparison.json) · [Verification record](VERIFICATION.md)

## Direct cancellation

Let $D(x)$ be $\tfrac{x}{2}\log 2$ minus the tent-weighted von Mangoldt sum in this collection. Applying the existing implication from RH gives a square-root error bound at all sufficiently large squares. An independent arithmetic proof would have to produce one fixed $C$ with

```math
\forall M\in\mathbb N\quad \exists K\ge M\quad
\forall k\in[K,K^2]\cap\mathbb N,\qquad D(k^2)\ge-Ck.
```

The finite certificates cover every $32\le K\le5.7\cdot10^{12}$ with $C=100$. The separate argument for signed low-zero prefixes gives nonnegativity on terminal subintervals along arbitrarily late square blocks. A direct proof of the bound over whole intervals at unbounded height remains open. [Definition and finite certificates](../prime-window-power-samples/pairs/mobius/) · [Signed-prefix argument](../prime-window-power-samples/pairs/mobius/CUTOFFS.md) · [Lean implication from RH](../prime-window-power-samples/pairs/mobius/lean/SquareSignedConverse.lean)

## Prior work

- Levent Alpöge, working with Claude, supplied the geometric proof and the theta chains. The Lean and Mathlib communities verified its endpoint. D. B. Sanftenberg specialized the proof to the principal character. His published endpoint is the comparison baseline here. [Alpöge’s announcement](https://alpo.ge/remark.pdf) · [Community verification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) · [Sanftenberg’s Lean proof](https://github.com/dbsanfte/RiemannGaussian/blob/0755e6518416ac74bbb0e7f986f8610c7b7ed347/scripts/CheckAlpogePrincipalArchivedGeometryRH.lean)
- For the same congruence classes of $q,d$, `bramble_trace` identified the inverse limit of the ordinary $2$-class groups as $\mathbb Z_2^2$ over the intermediate tower with $\sqrt{qd}$ and $\mathbb Z_2^3$ over the biquadratic tower. The finite-level bound uses unit signatures and the index-two Schreier bound. The equality of ranks uses the minus Iwasawa invariant computed for the intermediate tower by Chems-Eddin and Müller, followed by Kida’s formula. Section “Sharpness in the ordinary class tower” of `ordinary_tower_windows.md` gives the argument. [Revision 29 (ZIP)](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=29) [Chems-Eddin and Müller, Theorems 3 and 4](https://arxiv.org/pdf/2002.03602v4#page=5)
- The finite-slope comparison used by this proof implements the sharp lattice estimate of `twinheterodox`. José Brox also identified the disappearance of the nontrivial odd-order host-character case for ordinary zeta. The case-two automorphy calculation above concerns the rank-four count after that character restriction. [Lattice estimate](https://github.com/twinheterodox/three-simplifications-dirichlet-grh/blob/4dc189a9aa34db3bb7e67b5ad04abe781ff12995/paper/three-simplifications-dirichlet-grh.tex) · [Brox’s Selmer reduction](https://github.com/JoseBrox/GRH_distillation/blob/af70b111d50d803b9e377835990c22d971597cb1/notes/two-primary-selmer-reduction.md)

The 31 unchanged Lean sources under `upstream/` are from Sanftenberg’s repository at commit `0755e6518416ac74bbb0e7f986f8610c7b7ed347`. The file `lean/PrincipalArchivedInputs.lean` adapts his literature and grid assembly. The Apache 2.0 license covers those sources and that adaptation. The external proof library and Mathlib are separate replay inputs. [Upstream license](upstream/LICENSE) · [Original Git blob IDs](evidence/upstream-git-blobs.txt)
