# Finite certificates for the fourth-power loss

For the [paired remainder](README.md) and its corresponding prime-power deficit, the following bounds include every point of each stated block.

| Quantity | Range of block parameters | Certified bound |
| --- | --- | --- |
| $`L_s(m)`$, for either fixed $`s\in\{-1,+1\}`$ | $`10{,}000\le m\le2{,}000{,}000`$ | $`L_s(m)\le2(1+2\log m)`$ |
| $`D(k^2)`$, for every integer $`K\le k\le K^2`$ | $`32\le K\le5{,}700{,}000{,}000{,}000`$ | $`D(k^2)\ge-100k`$ |
| $`D(k^2)`$, for every integer $`K\le k\le K^2`$ | $`32\le K\le26{,}000{,}000{,}000`$ | $`\lvert D(k^2)\rvert\lt k/5`$ |

## From the zero height to the deficit

Let $`H=3\cdot10^{12}`$. Platt and Trudgian verified the zeta zeros through this height. We use the smoothed explicit formula and its unsmoothing inequality as stated in equations (1) and (3) of the family's finite tent proof. In that proof $`S`$ is the centered prime-power sum. Comparing the tent integral with its sum over lattice cells costs at most the total variation of $`W`$, which gives $`|D(x)+S(x)|\le2`$. [Finite tent inequalities](../FINITE.md#the-smoothed-estimate) · [Lattice-cell estimate](https://github.com/leecrossley/prime-window-rh-criterion/blob/a27adcdb6e5b65bdf41f4629d27e1ca3b4d116bd/results/prime-window-power-samples/pairs/FINITE.md#L27) · [Platt and Trudgian](https://arxiv.org/abs/2004.09765)

Sanftenberg proves the sharper $`|D(x)+S(x)|\le\min(1,60/x)`$ for this same tent and every real $`x\gt 0`$. The bounds below already follow from the total-variation estimate. [Uniform bound](https://github.com/dbsanfte/RiemannGaussian/blob/f04c60e9de9f6bbf7808b53b2edc946641b0aeb1/scripts/CheckAlpogeFixedPrimeBand.lean#L886) · [Inverse-scale bound](https://github.com/dbsanfte/RiemannGaussian/blob/f04c60e9de9f6bbf7808b53b2edc946641b0aeb1/scripts/CheckAlpogeFixedPrimeBandCentered.lean#L91)

For $`32^2\le x\le10^{42}`$ the first row of the published table gives $`|S(x)|/\sqrt{x}\lt 0.293`$. Thus $`|D(k^2)|/k\lt 1`$ for $`32\le k\lt 10^8`$ and $`|D(k^2)|/k\lt 0.3`$ for $`10^8\le k\le10^{21}`$.

For $`a=10^{42}\le x\le b=10^{56}`$ set $`d=1/1000`$, $`v=12.1`$, $`r=4e^{2d}/a`$, $`T=(\log H+1)/(\pi H)`$ and $`B_2=\log3-(\gamma_E+\log(4\pi))/3`$. Bound each increasing term at $`b`$ and each decreasing term at $`a`$ in the two published inequalities. This gives $`|D(x)|/\sqrt{x}\le A_0+B_0\sqrt{x}/H^2`$, where we may take

```math
\begin{aligned}
A_0={}&\frac3{\sqrt2}(B_2+4T)+\frac{r^2}{3\sqrt a(1-r^2)}
\\ &+3.001e^{2d}\,3(b^{1/6}+a^{-1/2})\frac{\sqrt v}{H}
 +\frac{4e^{5d/2}(\log b+d)^2}{\log2}\frac{\sqrt v}{H},
\\ B_0={}&73.2T+\tfrac34\,3.001e^{2d}v .
\end{aligned}
```

At both 160 and 256 bits, outward rounding gives $`A_0\lt 0.155187`$ and $`B_0\lt 27.288598`$. Combining the ranges gives the input used by Lean,

```math
\frac{|D(k^2)|}{k}\le\frac3{10}+\frac{55}{2}\frac{k}{H^2}
\qquad(10^8\le k\le10^{28}).
```

The formula and the two analytic inequalities enter as written mathematics. The interval arithmetic certifies the displayed constants. [Arb calculation](check_finite_quartic.py) · [Lean input declaration](lean/FiniteQuarticBudget.lean)

## Summing one block

For every integer $`k\ge10^8`$, the explicit small-divisor and pairing estimates give $`|D(k^2)-R(k)|\le(47/24)k+1\le2k`$. Insert $`k=n^2`$ in the preceding display, add this discrepancy and divide by $`n^3`$. Either clipped sign is at most $`(23/10)/n+(55/2)n/H^2`$. Monotonicity gives $`\sum_{n=m}^{m^2}1/n\le\log m+1/m`$ and $`\sum_{n=m}^{m^2}n\le(m^4+m^2)/2`$. Therefore

```math
L_s(m)\le\frac{23}{10}\left(\log m+\frac1m\right)
             +\frac{55}{4}\frac{m^4+m^2}{H^2}.
```

The last term is below $`2`$ for $`m\le10^6`$ and below $`25`$ for $`m\le2\cdot10^6`$. On the second range $`\log m\ge6\log10`$. These bounds imply the first certificate throughout each interval. For the second certificate use $`k\le(5.7\cdot10^{12})^2`$ in the deficit estimate. Its right side is at most $`99.575`$. The small-$`k`$ estimate above covers the other endpoint. [Clipped-sum proof](lean/FiniteQuarticBudget.lean) · [All integers in the square block](lean/FiniteHundredBlocks.lean) · [Replay](VERIFICATION.md)

## A two-sided bound on the shorter range

The family’s equations (1) and (2) apply directly to $`D(x)`$. They give $`|D(x)|\lt \sqrt x/5`$ for every real $`1024\le x\le4.761\cdot10^{41}`$. In particular, $`|D(k^2)|\lt k/5`$ on the complete integer square blocks in the third row. [Smoothed formula](../FINITE.md#the-smoothed-estimate) · [Unsmoothing inequality](../FINITE.md#moving-back-to-the-original-tent)

Put $`s=\sqrt x`$, $`P=69\cdot10^{19}`$, $`\nu_0=12.1/H^2`$ and $`r_0=4e^{2d}/1024`$. In (1) the geometric term is largest at the lower endpoint. In (2) use $`\nu\le\nu_0`$. The triangle inequality gives

```math
\frac{|D(x)|}{s}\le
\frac{3}{\sqrt2}(B_2+4T)+\frac{r_0^2}{3\cdot32(1-r_0^2)}
+73.2T\frac{s}{H^2}
+e^{2d}(\log x+d)\left(\frac34s\nu_0+3\sqrt{\nu_0}\right).
```

The right side increases with $`s\ge32`$. At $`s=P`$, outward rounding at 160 and 256 bits puts it below $`0.199554261606147`$. This proves the real bound through $`x=P^2`$. For $`32\le K\le26\cdot10^9`$ and $`K\le k\le K^2`$ one has $`32\le k\le(26\cdot10^9)^2\le P`$, so the same inequality applies at $`x=k^2`$. [Arb endpoint](check_finite_quartic.py) · [Lean monotonicity and inclusive blocks](lean/FiniteFifthBlocks.lean)

Whether one logarithmic upper bound for the Möbius loss holds along arbitrarily late blocks by direct arithmetic cancellation remains open.
