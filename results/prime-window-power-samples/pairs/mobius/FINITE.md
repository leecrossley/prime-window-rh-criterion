# Finite certificates for the fourth-power loss

For the [paired remainder](README.md), both of the following bounds hold with the indicated endpoints included.

| Quantity | Range of block parameters | Certified bound |
| --- | --- | --- |
| $L_s(m)$, for either fixed $s\in\{-1,+1\}$ | $10{,}000\le m\le2{,}000{,}000$ | $L_s(m)\le2(1+2\log m)$ |
| $D(k^2)$, for every integer $K\le k\le K^2$ | $32\le K\le5{,}700{,}000{,}000{,}000$ | $D(k^2)\ge-100k$ |

## From the zero height to the deficit

Let $H=3\cdot10^{12}$. Platt and Trudgian verified the zeta zeros through this height. We use the smoothed explicit formula and its unsmoothing inequality as stated in equations (1) and (3) of the family's finite tent proof. In that proof $S$ is the centered prime-power sum. Comparing the tent integral with its sum over lattice cells costs at most the total variation of $W$, which gives $|D(x)+S(x)|\le2$. [Finite tent inequalities](../FINITE.md#the-smoothed-estimate) · [Lattice-cell estimate](https://github.com/leecrossley/prime-window-rh-criterion/blob/a27adcdb6e5b65bdf41f4629d27e1ca3b4d116bd/results/prime-window-power-samples/pairs/FINITE.md#L27) · [Platt and Trudgian](https://arxiv.org/abs/2004.09765)

Sanftenberg proves the sharper $|D(x)+S(x)|\le\min(1,60/x)$ for this same tent and every real $x>0$. The bounds below already follow from the total-variation estimate. [Uniform bound](https://github.com/dbsanfte/RiemannGaussian/blob/f04c60e9de9f6bbf7808b53b2edc946641b0aeb1/scripts/CheckAlpogeFixedPrimeBand.lean#L886) · [Inverse-scale bound](https://github.com/dbsanfte/RiemannGaussian/blob/f04c60e9de9f6bbf7808b53b2edc946641b0aeb1/scripts/CheckAlpogeFixedPrimeBandCentered.lean#L91)

For $32^2\le x\le10^{42}$ the first row of the published table gives $|S(x)|/\sqrt{x}<0.293$. Thus $|D(k^2)|/k<1$ for $32\le k<10^8$ and $|D(k^2)|/k<0.3$ for $10^8\le k\le10^{21}$.

For $a=10^{42}\le x\le b=10^{56}$ set $d=1/1000$, $v=12.1$, $r=4e^{2d}/a$, $T=(\log H+1)/(\pi H)$ and $B_2=\log3-(\gamma_E+\log(4\pi))/3$. Bound each increasing term at $b$ and each decreasing term at $a$ in the two published inequalities. This gives $|D(x)|/\sqrt{x}\le A_0+B_0\sqrt{x}/H^2$, where we may take

$$
\begin{aligned}
A_0={}&\frac3{\sqrt2}(B_2+4T)+\frac{r^2}{3\sqrt a(1-r^2)}\\
&+3.001e^{2d}\,3(b^{1/6}+a^{-1/2})\frac{\sqrt v}{H}
 +\frac{4e^{5d/2}(\log b+d)^2}{\log2}\frac{\sqrt v}{H},\\
B_0={}&73.2T+\tfrac34\,3.001e^{2d}v .
\end{aligned}
$$

At both 160 and 256 bits, outward rounding gives $A_0<0.155187$ and $B_0<27.288598$. Combining the ranges gives the input used by Lean,

$$
\frac{|D(k^2)|}{k}\le\frac3{10}+\frac{55}{2}\frac{k}{H^2}
\qquad(10^8\le k\le10^{28}).
$$

The formula and the two analytic inequalities enter as written mathematics. The interval arithmetic certifies the displayed constants. [Arb calculation](check_finite_quartic.py) · [Lean input declaration](lean/FiniteQuarticBudget.lean)

## Summing one block

For every integer $k\ge10^8$, the explicit small-divisor and pairing estimates give $|D(k^2)-R(k)|\le(47/24)k+1\le2k$. Insert $k=n^2$ in the preceding display, add this discrepancy and divide by $n^3$. Either clipped sign is at most $(23/10)/n+(55/2)n/H^2$. Monotonicity gives $\sum_{n=m}^{m^2}1/n\le\log m+1/m$ and $\sum_{n=m}^{m^2}n\le(m^4+m^2)/2$. Therefore

$$
L_s(m)\le\frac{23}{10}\left(\log m+\frac1m\right)
             +\frac{55}{4}\frac{m^4+m^2}{H^2}.
$$

The last term is below $2$ for $m\le10^6$ and below $25$ for $m\le2\cdot10^6$. On the second range $\log m\ge6\log10$. These bounds imply the first certificate throughout each interval. For the second certificate use $k\le(5.7\cdot10^{12})^2$ in the deficit estimate. Its right side is at most $99.575$. The small-$k$ estimate above covers the other endpoint. [Clipped-sum proof](lean/FiniteQuarticBudget.lean) · [All integers in the square block](lean/FiniteHundredBlocks.lean) · [Replay](VERIFICATION.md)

The finite certificates use the same remainder and the same two signs as the asymptotic criterion. Whether one logarithmic upper bound holds along arbitrarily late blocks by direct arithmetic cancellation remains open.
