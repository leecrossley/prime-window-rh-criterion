# Sampling a dyadic prime sum at fixed powers

Lee Crossley · 21 November 2026

Let $`w_x,P,D`$ have the definitions in the [theorem statement](README.md). Write $`M(x)=(x/2)\log2-P(x)`$ for the ordinary-prime deficit. All estimates below concern $`x\ge8`$. They suffice for blocks with arbitrarily large lower endpoints.

## The continuous input

For $`0\lt \theta\lt 1`$ and fixed $`\delta\gt 0`$, suppose there are arbitrarily large $`X`$ for which $`-D(t)\le t^\theta`$ throughout $`X\le t\le X^{1+\delta}`$. Then $`\zeta(s)`$ has no zero with $`\Re s\gt \theta`$.

In the log coordinate $`u=\log t`$, the function in this assertion is the negative of the prime-power deficit. Its Laplace transform comes from three dilations of the original ramp. The multiplier $`(1-2^{-s})(2\,2^{-s}-1)`$ has no zero in the open critical strip. The zeta function has no real zero in that strip. The one-sided Landau window lemma therefore applies with this sign. The pointwise majorant gives its window hypothesis by integration. This implication is available as a Lean theorem using the analytic input from Alpöge. [Original window lemma](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83) · [Dyadic specialization](lean/PrimeWindow.lean) · [Majorant with an arbitrary constant](lean/PowerSamples.lean)

## How much can be missed between samples?

Let $`\Theta`$ be the supremum of the real parts of the nontrivial zeros. We have $`1/2\le\Theta\le1`$. Write

```math
H(s)=\frac{(2^s-1)(2^s-2)}{s(s-1)},\qquad y=x/4.
```

The removable values at 0 and 1 are interpreted by continuity. Mellin inversion of the weight and the explicit formula yield

```math
D(x)=\sum_\rho H(\rho)y^\rho+\sum_{j\ge1}H(-2j)y^{-2j}.
```

The first sum includes both signs of the ordinate and counts multiplicities. The second is bounded uniformly for $`x\ge8`$. In the first, $`|H(\rho)|\ll(1+|\Im\rho|)^{-2}`$. The zero-counting bound $`N(T)\ll T\log(2T)`$ implies $`\sum_\rho |H(\rho)|\,|\rho|^{1/2}\lt \infty`$ by dyadic summation. The continuous tent has zero weight at its outer endpoints. One can smooth it in logarithmic scale and pass to the limit using these summable bounds. [Weighted explicit formula, §7](https://people.maths.ox.ac.uk/greenbj/papers/primenumbers.pdf) · [Earlier explicit formula for the same tent](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24)

For $`8\le z\le x`$ put $`v=\log(z/x)\le0`$. Along the segment from $`0`$ to $`\rho v`$, the exponential has modulus at most one. Integration along the segment and the triangle inequality give

```math
|e^{\rho v}-1|\le\min(2,|\rho v|)\le2\sqrt{|\rho|\,|v|}.
```

Apply this to each zero term at $`x`$ and $`z`$. The result is the uniform estimate

```math
|D(x)-D(z)|\ll 1+x^\Theta\sqrt{\log(x/z)}. \tag{1}
```

Fix $`k\ge1`$. For $`n^k\le x\le(n+1)^k`$ and $`n\ge2`$,
$`\log(x/n^k)\le k\log(1+1/n)\le k/n\le2k\,x^{-1/k}`$.
Consequently

```math
|D(x)-D(n^k)|\ll_k 1+x^{\Theta-1/(2k)}. \tag{2}
```

No zero need have real part equal to $`\Theta`$. The termwise estimate uses only the upper bound $`\Re\rho\le\Theta`$.

## From the samples to the critical line

Suppose condition 2 holds. On each corresponding interval $`K^k\le x\le K^{2k}`$ choose $`n=\lfloor x^{1/k}\rfloor`$. Both endpoints are included and $`K\le n\le K^2`$. By (2) the entire interval satisfies

```math
-D(x)\ll_{C,k} x^{\max(1/2,\,\Theta-1/(2k))}. \tag{3}
```

If $`\Theta\gt 1/2`$, choose $`\theta`$ strictly between the exponent in (3) and $`\Theta`$. It satisfies $`0\lt \theta\lt 1`$, including when $`\Theta=1`$. The implicit constant is absorbed by $`x^\theta`$ on every sufficiently late block. The continuous input with $`\delta=1`$ rules out all zeros with real part greater than $`\theta`$. The definition of the supremum guarantees such a zero. Thus $`\Theta=1/2`$, and the functional equation puts every nontrivial zero on the critical line.

Under RH absolute convergence of the explicit formula gives $`D(x)=O(\sqrt x)`$. This proves condition 2. The previously established ordinary-prime inequality $`M(x)\gt 0`$ under RH gives condition 3. For completeness, its eventual form follows from the classical identity $`\sum_\rho 1/(\rho(1-\rho))=2+\gamma_E-\log(4\pi)`$. On the line this yields

```math
\liminf_{x\to\infty}\frac{D(x)}{\sqrt x}\ge-\tfrac12(4+3\sqrt2)(2+\gamma_E-\log(4\pi))\gt -0.191.
```

Prime squares contribute $`(3\sqrt2-4+o(1))\sqrt x`$ to $`M(x)-D(x)`$ by partial summation and the prime number theorem. The coefficient exceeds $`0.242`$. Higher prime powers contribute nonnegatively. Together these give $`\liminf_{x\to\infty}M(x)/\sqrt x\ge(3\sqrt2-4)-\tfrac12(4+3\sqrt2)(2+\gamma_E-\log(4\pi))\gt0.052`$ under RH. Conversely $`0\le M(x)-D(x)\ll\sqrt x`$ by the Chebyshev bound for $`\psi(x)-\vartheta(x)`$ and $`0\le w_x\le1`$. Hence condition 3 implies condition 2. [Zero-mass identity, equation (1.3)](https://arxiv.org/pdf/1202.0729) · [Earlier prime-square calculation](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24)

## An independent interpolation argument

The truncated von Mangoldt explicit formula at half-integers, with truncation height comparable to $`t`$, gives $`\psi(t)=t+O(t^\Theta\log^2 t)`$. Indeed $`\sum_{|\Im\rho|\le t}1/|\rho|\ll\log^2 t`$ and the truncation error there is $`O(\log^2 t)`$. Monotonicity between neighbouring half-integers gives the estimate for real $`t`$. If $`\Theta=1`$, the elementary Chebyshev bound suffices. Partial summation over each of $`[x/4,x/2]`$ and $`[x/2,x]`$ therefore gives a sum of $`\Lambda(m)/m`$ equal to $`\log2+O(x^{\Theta-1}\log^2x)`$, using half-open intervals. [Truncated explicit formula and zero count, Appendix A](https://www.rivmat.unipr.it/fulltext/2016-7-1/pdf/6_Zaccagnini.pdf)

Between the finitely many corners in any compact interval, direct differentiation gives

```math
D'(x)=\tfrac12\log2+\tfrac12\sum_{x/4\lt m\le x/2}\frac{\Lambda(m)}m
                   -\sum_{x/2\lt m\le x}\frac{\Lambda(m)}m
       =O(x^{\Theta-1}\log^2x).
```

The tent is continuous at every corner. Integrating piece by piece from $`n^k`$ to $`x`$ gives $`|D(x)-D(n^k)|\ll_k x^{\Theta-1/k}\log^2 x`$ for large $`n`$. This independently gives (2). Both arguments use the same Lean-checked continuous-window implication.

## Excursions on every late block

Fix $`k\ge1`$ and $`1/2\lt \theta\lt \Theta`$. For every sufficiently large integer $`K`$ there are $`K\le n_+,n_-\le K^2`$ such that

```math
M(n_+^k)\gt (n_+^k)^\theta,\qquad M(n_-^k)\lt -(n_-^k)^\theta.
```

Indeed, choose $`\theta\lt \sigma\lt \Theta`$. If arbitrarily late blocks lacked either signed excursion of size $`x^\sigma`$ for $`D`$, then on those blocks the corresponding one-sided majorant would hold throughout the real interval by (2), with exponent $`\max(\sigma,\Theta-1/(2k))`$. Choose a slightly larger exponent still below $`\Theta`$ and absorb the constant. The two signed versions of the continuous-window lemma rule out a zero to the right of that exponent. This contradicts the supremum. Thus both signed excursions of size $`x^\sigma`$ occur for $`D`$ on every sufficiently late block. The bound $`0\le M(x)-D(x)\ll\sqrt x`$ transfers both to $`M`$ at exponent $`\theta`$. At the squares this is already in `bramble_trace`'s proof, lines 179 to 181 of `smoothed-explicit-formula.md` in revision 24. The argument here covers every fixed power. [Both signs of the continuous-window lemma](lean/PrimeWindow.lean)

## Unconditional runs of consecutive powers

For every fixed integer $`k\ge1`$ and real $`0\lt \eta\lt 1`$, every sufficiently large integer $`K`$ admits an integer $`m`$ with $`K\le m\le m+\lfloor m^\eta\rfloor\le K^2`$ such that, for every integer $`j`$ from $`m`$ through $`m+\lfloor m^\eta\rfloor`$, the two inequalities

```math
M(j^k)\gt 0,\qquad D(j^k)\gt -j^{k/2}/5
```

hold simultaneously. This theorem has no hypothesis about the zeros of zeta.

If RH holds, the bounds on the zero sum and the prime squares above give both inequalities at every sufficiently large real scale. Take $`m=K`$.

If RH fails, $`\Theta\gt 1/2`$. Choose a positive $`d\lt (1-\eta)/(2k)`$ with $`\sigma=\Theta-d\gt 1/2`$. By the preceding argument for $`D`$, in every sufficiently late block there is an $`n`$ with $`D(n^k)\gt n^{k\sigma}`$. For integers $`j`$ with $`|j-n|\le L=\lceil2n^\eta\rceil`$, one has $`j/n=1+O(n^{\eta-1})`$ and $`|\log(j^k/n^k)|\ll_k n^{\eta-1}`$. Applying (1) in the correct order to the two scales gives

```math
|D(j^k)-D(n^k)|\ll_k 1+n^{k\Theta-(1-\eta)/2}=o(n^{k\sigma}).
```

This proves $`D(j^k)\gt 0`$ throughout that neighbourhood, and $`M(j^k)\ge D(j^k)`$. As a separate check, integrating the derivative estimate over the same neighbourhood instead gives $`O_k(n^{k\Theta-(1-\eta)}\log^2 n)`$, which is also $`o(n^{k\sigma})`$.

For large $`K`$ we have $`K^2-K\ge2L`$ uniformly for $`n\le K^2`$, since $`\eta\lt 1`$. At least one of $`[n-L,n]`$ and $`[n,n+L]`$ fits inside the block. Let $`m`$ be its left endpoint. Then $`m\le n`$ and $`\lfloor m^\eta\rfloor\le L`$, which proves the statement including the endpoint cases.

## Prior work and scope

The closest antecedent is `bramble_trace`’s 20 November 2026 proof. In its normalization $`D_{\rm p}`$ has centre $`t`$ and peak weight $`1/3`$. Direct substitution gives $`M(x)=3D_{\rm p}(x/2)`$. Its revision 24 is an archive of eight files. In `smoothed-explicit-formula.md`, lines 132 to 173 state and prove the ordinary-prime sign. Lines 175 to 181 give the square-sampling principle, including excursions of both signs on every late interval. Lines 190 to 218 give the prime-centre test by concavity. The proof already uses Alpöge’s analytic window lemma for localized oscillation. [Dated discussion](https://rstation.ai/r/riemann_hypothesis/posts/100#comment-61fubEt16h1nsGVD) · [Versioned proof](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24)

Its uniform Lipschitz estimate gives an error of order $`\sqrt x`$ when rounding to a square. Rounding to a $`k`$th power with that estimate alone costs $`O_k(x^{1-1/k})`$. For $`k\gt 2`$ a zero just to the right of $`1/2`$ can give smaller excursions than this error. Equations (1)–(3) resolve that difficulty by measuring the rounding error relative to $`\Theta`$. The extension to all fixed powers and the unconditional long-run theorem are the contributions advanced here. The supplied Lean files also record checks of the earlier square and prime-centre principles.

The Omega Institute proved that RH is equivalent to $`U(n^4)\lt n^2`$ for every sufficiently large integer $`n`$, where $`U`$ is the centred cumulative von Mangoldt sum. Their proof bounds the sum between consecutive fourth powers by convexity. The ordinary-prime condition here tests $`P(n^k)`$ on blocks $`K\le n\le K^2`$ for arbitrarily large $`K`$ and any fixed positive integer $`k`$. [Omega’s Lean theorem](https://github.com/the-omega-institute/trureturing/blob/4e51eeaa9736a08ad0e9b8b79579e4b7ba80837e/D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.lean#L131) [Proof outline](https://github.com/the-omega-institute/trureturing/blob/4e51eeaa9736a08ad0e9b8b79579e4b7ba80837e/Blueprint/D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.md)

Johnston treats an integral up to $`x`$. Suzuki treats signed weighted sums of the von Mangoldt function. Danesh uses the Weil form with pairs of test functions and varying supports. Searches by the weight, one-sided prime sums, polynomial sample scales and localized oscillation did not locate an earlier statement of this fixed-power criterion. Priority is open to additional references. [Continuous-window result](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/v1.0.0) · [Johnston, Theorem 1.2](https://arxiv.org/abs/2201.06184) · [Suzuki](https://arxiv.org/abs/2411.07436) · [Danesh, Theorem 1.1](https://arxiv.org/abs/2611.10726)

An alternative proof of RH along this route still requires an independent arithmetic proof of the sample inequality over whole arbitrarily late blocks.
