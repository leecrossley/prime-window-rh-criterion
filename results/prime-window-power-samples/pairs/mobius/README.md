# A fourth-power criterion for the negative part of a Möbius sum

Version 1.0.0 contains the original proof. Version 1.0.1 includes the separate kernel checks for the eleven result modules. [Version 1.0.0](https://doi.org/10.5281/zenodo.24426583) [Version 1.0.1](https://doi.org/10.5281/zenodo.24428032)

For the paired Möbius remainder $`R(k)`$ defined below, add up the losses on one complete block,

```math
L_-(m)=\sum_{n=m}^{m^2}\frac{\max\{-R(n^2),0\}}{n^3}.
```

**Theorem.** RH is equivalent to the existence of one $`C\ge0`$ such that $`L_-(m)\le C(1+2\log m)`$ for arbitrarily large integers $`m`$. Equivalently, for every $`\varepsilon\gt 0`$ there are arbitrarily large $`m`$ with $`L_-(m)\le m^\varepsilon`$. The blocks in this last statement may depend on $`\varepsilon`$. Both endpoints of every block count. The tent corresponding to $`R(n^2)`$ is evaluated at the fourth power $`x=n^4`$. [Lean theorem](lean/FourthSignedCriterion.lean)

**Finite certificates.** For every integer $`10{,}000\le m\le2{,}000{,}000`$, the bound holds with $`C=2`$. The same constant works for the positive part. For the prime-power deficit $`D`$, every integer $`k\in[K,K^2]`$ satisfies $`D(k^2)\ge-100k`$ whenever $`32\le K\le5.7\cdot10^{12}`$. On the shorter range $`32\le K\le26\cdot10^9`$ the two-sided bound is $`|D(k^2)|\lt k/5`$. The estimates use Platt and Trudgian’s verified zero height. [Finite proof and certificates](FINITE.md)

An arithmetic proof of the upper bound for arbitrarily large $`m`$ remains open. The signed-prefix companion obtains a nonnegative terminal interval on arbitrarily late square blocks and identifies a sparse test for the missing full-interval bound. [Signed-prefix companion](CUTOFFS.md)

## The paired remainder

Write $`\Lambda`$ for the von Mangoldt function, $`\mu`$ for the Möbius function, $`\gamma_E`$ for Euler’s constant and $`H_j=\sum_{i=1}^j1/i`$. All logarithms are natural. The family’s compact tent and its deficit are

```math
W(t)=\begin{cases}
2-1/(2t),&1/4\le t\le1/2,
\\ 1/t-1,&1/2\lt t\le1,
\\ 0,&\text{otherwise},
\end{cases}
\qquad
D(x)=cx-\sum_{j\ge1}\Lambda(j)W(j/x),\qquad c=\tfrac12\log2 .
```

Set $`A=c(1+\gamma_E-c)`$. For $`t\ge1`$ put

```math
r(t)=ctH_{\lfloor t\rfloor}
-\sum_{1\le j\le t}(\log j)W(j/t)-A\lfloor t\rfloor .
```

Möbius inversion of $`\sum_{d\mid n}\Lambda(d)=\log n`$ gives
$`D(x)=A+\sum_{d\le x}\mu(d)r(x/d)`$ for $`x\ge1`$. At $`x=k^2`$ keep $`k\lt d\le x`$. Put

```math
\tau=\frac{2c+\log3-2A}{(\log3-c)/3},\qquad
j_0=\left\lfloor x/\tau\right\rfloor,\qquad h=k\lfloor\sqrt{k}\rfloor .
```

Let $`E_k`$ consist of the odd integers in $`(j_0,j_0+h]`$. Remove these indices and their doubles from the sum. In full,

```math
R(k)=\sum_{\substack{k\lt d\le k^2\\d\notin E_k\cup2E_k}}\mu(d)\,r(k^2/d).
```

For odd $`d`$, $`\mu(2d)=-\mu(d)`$. On the selected band the two residual weights agree at the crossing $`\tau`$ and their difference is controlled by its distance. The small-divisor estimate and the sum of these paired errors give $`|D(k^2)-R(k)|\le2k`$ for $`k\ge10^8`$. [Divisor identity](lean/DivisorBand.lean) · [Pairing](lean/MobiusPair.lean) · [Explicit discrepancy](lean/EarlySquareError.lean)

## Proof of the criterion

For $`s=-1`$ or $`+1`$ write $`L_s(m)=\sum_{m\le n\le m^2}\max(sR(n^2),0)/n^3`$. Under RH the tent’s absolutely convergent explicit formula gives $`|D(n^4)|\ll n^2`$. The two-unit discrepancy above and $`\sum_{m\le n\le m^2}1/n\le1+2\log m`$ give the logarithmic estimate for either fixed sign. Any logarithmic bound implies the stated positive-power estimates.

Conversely, suppose a nontrivial zero lies to the right of $`1/2`$. The signed excursion and interpolation estimates for $`D`$ give some $`0\lt \delta\le1/200`$ with the following property for both signs. For every sufficiently large $`m`$ there is an $`x`$ between $`m^{8-\delta}`$ and $`m^{8-\delta/2}`$ on which the excursion persists through $`[x,x+x^{1-\delta}]`$. In this interval the normalized signed deficit is at least $`x^{4\delta}`$. Take $`N=\lceil x^{1/4}\rceil`$ and $`w=\lfloor x^{1/4-2\delta}\rfloor`$. The fourth powers of all $`n`$ from $`N`$ through $`N+w`$ lie in the excursion and all these indices belong to $`[m,m^2]`$. Their number times $`x^{4\delta}`$ is at least $`m^{2+\delta}`$. [Excursion at fourth powers](lean/FourthSignExcursions.lean) · [Endpoint rounding](lean/FourthPowerSpacing.lean)

After normalization by $`n^2`$ each of those samples has weight $`1/n\ge1/m^2`$. Their contribution to the clipped deficit sum is therefore at least $`m^\delta`$. Replacing $`D(n^4)`$ by $`R(n^2)`$ costs at most $`2(1+2\log m)`$ on the whole block, since taking the positive part is 1-Lipschitz. It follows that $`L_s(m)\gt m^{\delta/2}`$ for every sufficiently large $`m`$ and either sign. This contradicts the subpower estimate with $`\varepsilon=\delta/2`$. The functional equation excludes zeros to the left once zeros on the right are excluded. [Signed criterion and dependency audit](lean/FourthSignedAudit.lean)

## Relation to earlier tests

The dyadic tent and the earlier square-sampling argument are due to `bramble_trace`. The maintained perfect-power proof records that result and Polak’s test at the first prime at or above each fourth power. Sanftenberg gives a positive-deficit mass criterion on the same ordinary-prime tent. Here the negative part is taken after forming one specified signed Möbius sum at each sample. [Family comparison](../../PROOF.md#prior-work-and-scope) · [Sanftenberg’s fourth-power criterion](https://github.com/dbsanfte/RiemannGaussian/blob/f04c60e9de9f6bbf7808b53b2edc946641b0aeb1/docs/arithmetic-proof-shortening.md)

The Omega Institute also uses the weight $`n^{-3}`$, on positive parts of the cumulative von Mangoldt remainder at $`n^4`$. Its criterion uses blocks $`[h^3,h^4]`$, and its simultaneous version, which uses the Galois input from Alpöge's proof, bounds the cumulative remainder on the corresponding real window. Brox’s scale-averaged criterion integrates a positive part over continuous multiplicative windows and allows local averaging. [Omega’s weighted criterion](https://github.com/the-omega-institute/trureturing/blob/341e3d1cf5aeb67801ba670aa685588e4beb7266/D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampleMass.lean#L245) · [Omega’s harmonic bound](https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7066418938) · [Simultaneous bounds](https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7067180276) · [Brox’s continuous criterion](https://github.com/JoseBrox/GRH_distillation/blob/9ac7c801b7afadc4cfc91de88b9d6c338b96d5f3/notes/scale-averaged-criterion.md)

Using the separate seven-eighths theorem, the family also gives arbitrarily late shrinking blocks on which a signed average of the centered prime sum at squares is small. The statistic here clips each Möbius sample before summing it. [Signed averages at squares](../../square-blocks/SHORT-ARITHMETIC.md)

The arithmetic criterion has a Lean replay. The finite certificate combines Lean implications with a written finite-height estimate and outward-rounded calculations. The companion records which steps have a Lean proof. [Replay instructions and evidence](VERIFICATION.md)
