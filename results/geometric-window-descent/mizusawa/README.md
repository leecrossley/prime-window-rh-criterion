# Three generators in the dyadic window

For primes $q\equiv 3\pmod 8$ and $d\equiv 7\pmod {16}$, put $k=\mathbb Q(\sqrt{-qd})$, $K=k(\sqrt q,\sqrt d)$ and $K_\infty=K\mathbb Q_\infty$, where $\mathbb Q_\infty$ is the real cyclotomic $\mathbb Z_2$-extension. Mizusawa proved that the Galois group $X(K_\infty)$ of the maximal everywhere-unramified abelian pro-2 extension is free of rank three over $\mathbb Z_2$. His result supplies the dyadic generator bound in the principal-character specialization of Alpöge’s announced geometric proof. [Mizusawa, Lemma 4.2, p. 126](https://www.numdam.org/item/10.5802/jtnb.707.pdf#page=13) · [Geometric proof](../README.md)

The new Lean endpoint has the following type.

```lean
RiemannReduction.Mizusawa.RankThree → RiemannHypothesis
```

The premise states Mizusawa’s isomorphism on the actual genus-field tower. The classical argument invokes his published lemma. The Lean proof accepts that lemma as a parameter. The repository’s closed, nine-generator Lean theorem still gives the comparison without a literature parameter. [Premise and tower](../lean/MizusawaTower.lean) · [Rank-three endpoint](../lean/MizusawaWindowRH.lean) · [Closed rank-nine endpoint](../lean/SecondSeedRH.lean)

## Which field and which group?

1. The cyclotomic character modulo $\{1,-1\}$ cuts out $\mathbb Q_\infty$. Choose $a^2=q$, $b^2=d$, $c^2=-qd$ and $i^2=-1$. Then $c=\pm iab$. An automorphism fixing $a,b,c$ fixes $i$, and the element $-1$ of the dyadic cyclotomic Galois group sends $i$ to $-i$. This identifies Mizusawa’s tower with $\mathbb Q(\mu_{2^\infty},a,b)$. At an odd prime $p\equiv3\pmod4$, the quadratic Gauss sum shows that the square subgroup of the mod-$p$ cyclotomic character fixes a root of $-p$. Both auxiliary primes have this residue. Lean proves that the subgroup used in the geometric proof equals the subgroup fixing the genus-field tower for every choice of radicals. [Gauss-sum comparison](../lean/MizusawaHostField.lean) · [Genus-field comparison](../lean/MizusawaGenusField.lean)
2. For a Galois subgroup $U$, intersect its open normal subgroups of 2-power index whose quotients kill commutators and finite inertia. The quotient by this intersection presents the ordinary unramified abelian pro-2 Galois group. Every locally constant unramified quadratic character of $U$ factors through it. Pullback recovers the original character. On a free module $\mathbb Z_2^r$, the values of a homomorphism to $\mathbb F_2$ on the $r$ coordinate vectors determine it, because doubling is killed. Thus three generators give at most eight quadratic characters. [Quotient, factorization and count](../lean/MizusawaCharacters.lean)
3. The geometric library’s `XRk 2 1` counts precisely these characters. The existing integral-rank theorem supplies the ordinary tower bound and the quotient with splitting imposed at two. The interval selector then receives the actual witness $R=3$. [Tower input](../lean/MizusawaTower.lean) · [Use in ordinary RH](../lean/MizusawaWindowRH.lean)

## What changes in the window?

Write $B=2C_KC_t/\varepsilon$, holding $C_K$, $C_t$ and $\varepsilon$ fixed.

| Quantity in the geometric argument | Nine generators | Three generators |
| --- | ---: | ---: |
| Upper bound on ordinary quadratic characters | 512 | 8 |
| Upper bound on exceptional twist indices | 9 | 3 |
| Reference level $\lfloor\log_2 R\rfloor+3$ | 6 | 4 |
| Window parameter $J_R=2^{R+2}B^R$ | $2048B^9$ | $32B^3$ |

The selector finds $Y$ with $X^{1/J_R}\leq Y$ and $Y^2\leq X$. The smaller parameter strengthens the lower endpoint at fixed $X$ and $B\geq1$. The exact factor is $J_9/J_3=64B^6$. A numerical first height would also require estimates for the input-dependent threshold on $X$. Lean checks the reference levels, the specialized selector and the polynomial identity. [Selector calculation](../lean/MizusawaSelector.lean) · [Place where $J_R$ enters the proof](../lean/SingleTowerGrid.lean)

## Proof dependencies

| Reachable Lean declarations | Previous or control | Using three | Net fewer |
| --- | ---: | ---: | ---: |
| Standalone tower bound, closed nine vs. Mizusawa input | 77,321 | 44,073 | 33,248 |
| Full geometric argument, closed nine vs. Mizusawa input | 1,476,889 | 1,476,830 | 59 |
| Full geometric argument, same Mizusawa input at nine vs. three | 1,476,831 | 1,476,830 | 1 |

The standalone tower proof loses 33,544 names and gains 296. Its earlier proof used the six-generator ray estimate, quadratic transfer and the index-two Schreier bound. Many of their underlying declarations also occur elsewhere in the geometric proof. Against the closed nine-generator endpoint, the full argument loses 100 names and gains 41. Its count excludes the cost of formalizing Mizusawa’s paper. [Arithmetic differences](evidence/arithmetic.json) · [Full differences](evidence/comparison.json)

For an equal-premise comparison, the control uses the same field identification and rank theorem, weakens three to nine and runs the same geometric argument. Four names leave and three enter. The weakening lemmas for character cardinality and rank disappear. The three theta-chain comparisons, the second symplectic automorphy step and the odd-prime Ferrero–Washington input remain reachable. [Nine-generator control](../lean/MizusawaNineControl.lean) · [Three-generator dependency audit](../lean/AuditMizusawaRH.lean)

## Prior work

Mizusawa established the rank in 2010, including freeness. The separate rank-two statement in Lemma 4.2 concerns the intermediate tower $k_\infty(i)$. The finite-level calculation by `bramble_trace` already applies a three-generator bound to the cohomological intervals and uses the cyclotomic action to bound the number of exceptional positive twist indices by two. The generic selector audited here uses three. The file `ordinary_tower_windows.md` is identical in revisions 29 and 38. [Mizusawa](https://doi.org/10.5802/jtnb.707) · [Reading guide, revision 38](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=38)

The formal contribution here identifies the genus-field Galois subgroup and its ordinary character quotient with the archived proof’s input, then compares that route with the nine-generator calculation. The earlier repository already linked the literature and gave a separate sufficient condition on characters allowed to ramify at $q,d$. The predecessor sources and search scope are recorded below. [Previous family revision](https://github.com/leecrossley/prime-window-rh-criterion/tree/33c85d76b5b7a7989d39e2278ccce1ba8734b7ac/results/geometric-window-descent) · [Verification and source search](VERIFICATION.md)

## A finite-layer lemma independent of RH

For a finite abelian extension of a totally imaginary number field, suppose ramification is confined to a finite set of places $S$. Evaluate a quadratic character on the local Artin symbols of any global integral unit. The sum of its values over $S$ is zero in $\mathbb F_2$. Lean derives this from global reciprocity and triviality of unit symbols at unramified places. To turn this into a direct eight-character proof in Lean, the independent residue-sign vectors of suitable units at the primes over $q,d$ and their finite-layer descent still need formalization. The reading guide gives the finite-level argument on paper. This consequence of classical reciprocity is independently reusable. [Unit parity](../lean/MizusawaUnitParity.lean) · [Dependency audit](../lean/AuditMizusawaUnits.lean)

## Replay

Prepare Lean 4.33.1, the pinned Mathlib checkout and the geometric proof archive using the parent instructions. Run the commands from `results/geometric-window-descent`. The targets check the standalone tower bound, the finite-layer unit lemma, and the three RH endpoints respectively. The last target includes the control that uses Mizusawa’s result at nine. [Input versions and downloads](../REPLAY.md)

```sh
python3 replay.py mizusawa-rank --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
python3 replay.py mizusawa-units --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
python3 replay.py mizusawa --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
```

Proving `RiemannReduction.Mizusawa.RankThree` in Lean would close this route and make its complete dependency cost measurable. A shorter arithmetic proof could instead target the weaker conclusion the window actually uses, at most eight everywhere-unramified quadratic characters on every auxiliary host. [Exact input to the integral bound](../lean/NineIntegralTower.lean)
