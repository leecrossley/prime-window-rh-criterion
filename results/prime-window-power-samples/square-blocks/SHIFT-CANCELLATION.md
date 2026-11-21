# How much of the prime-pair discrepancy cancels between odd and even shifts?

Lee Crossley · 21 November 2026

On every sufficiently late block of square samples the odd and even shift errors cancel a proportion tending to one. The fraction left determines the supremum of the real parts of the nontrivial zeta zeros. The absolute upper bound needed to beat the diagonal remains open by this approach.

## The statistic

Use the dyadic tent $`W`$ from the [block definitions](README.md), $`b_m=\Lambda(m)-1`$, $`W_m=W(m/x)`$, and the **ordered** centered Hardy–Littlewood discrepancy

```math
R(x)=\frac2x\sum_{h\ge1}\sum_{m\ge1}
\big[b_m b_{m+h}-(\mathfrak S(h)-1)\big]W_mW_{m+h}.
```

Write $`R_o`$ and $`R_e`$ for its terms with odd and even $`h`$, respectively. Only positive shifts occur after the factor two, so the even subtotal excludes the diagonal. For an integer $`K\ge2`$ set $`M=\lfloor4K\sqrt{\log K}\rfloor`$, $`N=M-K+1`$, and $`\langle F\rangle_K=N^{-1}\sum_{n=K}^M F(n^2)`$. Define

```math
G_K=\langle R\rangle_K,\qquad
U_K=\big\langle |R_o|+|R_e|\big\rangle_K,\qquad
\eta_K=G_K/U_K
```

when $`U_K>0`$. The absolute values are taken separately at each square **before** averaging. Put $`\Theta=\sup_\rho\Re\rho`$ over the nontrivial zeros of $`\zeta`$, $`\mu=\int W=(\log2)/2`$ and $`I=\int W^2=3-4\log2`$.

**Theorem.** The quantities $`G_K`$ and $`U_K`$ are positive for all sufficiently large $`K`$. Without any premise about all zeros lying on the critical line,

```math
\eta_K\longrightarrow0,\qquad
\lim_{K\to\infty}\frac{\log\eta_K}{\log K}=2\Theta-2.
\tag{1}
```

The prime number theorem with the Vinogradov–Korobov error term gives $`\eta_K\ll\exp[-c(\log K)^{3/5}(\log\log K)^{-1/5}]`$ for some absolute $`c>0`$. Using the separate $`7/8`$ zero-free theorem gives $`\eta_K\ll K^{-1/4}`$ and the **absolute** upper bound $`G_K\ll K^{3/2}(\log K)^{3/4}`$. The absolute threshold in the question is $`2I\log K+O(\log\log K)`$.

## What cancels at a single scale

Let $`T_e=\sum_{2\mid m} W_m`$, $`T_o=\sum_{2\nmid m} W_m`$, $`S=\sum_m b_mW_m`$, and $`L=\log2`$. For every real $`x\ge4`$,

```math
\sum_{2\mid m}\Lambda(m)W_m=L,\qquad u:=\sum_{2\mid m}b_mW_m=L-T_e.
\tag{2}
```

Indeed write $`2^j\le x<2^{j+1}`$. The only powers of two with possible positive weight are $`2^j`$ and $`2^{j-1}`$, both even. At $`t=2^j/x\in(1/2,1]`$ their weights sum to $`(1/t-1)+(2-1/t)=1`$. The endpoint weights are included by continuity. In particular $`T_e\ge1`$, so $`u\le L-1<0`$.

For odd $`h`$ the singular series vanishes. Every ordered odd-shift pair selects one even and one odd member. Summing the two products separately gives the exact identities

```math
\frac{x R_o(x)}2=u(S-u)+T_eT_o,\qquad
S=u+\frac{xR_o(x)/2-T_eT_o}{u}.
\tag{3}
```

Thus an exact check of the original diagonal inequality can use (3) at each square and compare $`\sum S(n^2)^2/n^2`$ with the actual diagonal. It requires no even-shift correlation estimates or evaluation of the singular series. The odd-shift statistic already contains the full weighted prime sum. In fact the **uncentered** odd-shift contribution of $`\Lambda(m)\Lambda(m+h)`$ is just $`2L(S+T_e+T_o-L)/x`$. The large fluctuations in the two centered subtotals arise when the terms linear in $`\Lambda`$ are included.

The full-mesh trapezoidal rule gives $`T_e=\mu x/2+O(1/x)`$ and $`T_o=\mu x/2+O(1/x)`$, uniformly for real $`x`$. Both lattices have spacing $`2/x`$ and the derivative of the compact tent has bounded variation. Multiplying the quadrature error $`O((2/x)^2)`$ by $`x/2`$ gives the stated error, also for the translated odd lattice. Direct integration of the two branches gives $`\mu=L/2`$. In the numerator of (3) the terms independent of $`S`$ are $`-L^2+2LT_e+T_e(T_o-T_e)`$. Consequently

```math
R_o=-\mu S+L^2+O\big((|S|+1)/x\big).
\tag{4}
```

The [singular-series calculation for this weight](PAIR-DISCREPANCY.md) gives $`R=S^2/x+B+o(1)`$ with $`0.36160550<B<0.36160555`$. Partial summation and the prime number theorem give $`S=o(x)`$. Subtracting (4) yields

```math
R_e=\mu S+S^2/x+B-L^2+o(1),\qquad
R=\frac{(R_o-L^2)^2}{\mu^2 x}+B+o(1).
\tag{5}
```

For the second equality, squaring (4) and dividing by $`x`$ gives an error $`O((|S|+1)^2/x^2)=o(1)`$. Thus the terms of order $`S`$ cancel. The remaining square has a fixed sign. In particular, $`R(x)>0`$ for every sufficiently large real $`x`$.

## A finite error for a block test using only odd shifts

There is also a version of (3) that eliminates the lattice sums $`T_e,T_o`$ at the cost of a known error. For $`x\ge8`$ put

```math
Z(x)=\frac{L^2-R_o(x)}{\mu(1-4/x)}.
```

For every integer $`K\ge3`$, with $`N=M-K+1`$ and $`E_K=\sum_{n=K}^M S(n^2)^2/n^2`$, one has

```math
\left|\frac{E_K}{N}-\frac1N\sum_{n=K}^M\frac{Z(n^2)^2}{n^2}\right|
\le \frac{3700}{(K-1)N}.
\tag{A}
```

Thus a comparison of the odd-shift estimate with the observed mean diagonal, by more than this tolerance on the appropriate side, certifies either sign on the entire block. The tolerance decreases as $`O(1/(K^2\sqrt{\log K}))`$. This is an elementary finite inequality.

For its proof, the full-mesh trapezoid rule on a lattice of spacing $`d`$ obeys $`|d\sum f-\int f|\le d^2\mathrm{Var}(f')/8`$. On each cell $`[a,b]`$ the quadrature error is, up to sign, the integral of $`(t-a)(b-t)/2`$ against $`df'(t)`$, whose kernel is bounded by $`d^2/8`$. The bound includes the jumps of $`W'`$ at the corners. Since $`\mathrm{Var}(W')=8+6+6+3+1=24`$, write $`T_e=\mu x/2+e`$ and $`T_o=\mu x/2+o`$ with $`|e|,|o|\le6/x`$. Expanding (3) now gives

```math
\left|R_o+\left(\mu-\frac{2L}{x}\right)S-L^2\right|
\le \frac{12|S|}{x^2}+\frac{2L^2+12\mu}{x}
       +\frac{24L}{x^2}+\frac{144}{x^3}.
```

One has $`|S|\le3x`$ for $`x\ge4`$. Indeed $`\psi(2m)-\psi(m)\le\log\binom{2m}{m}\le2m\log2`$, by counting prime powers in the binomial coefficient. Summing at powers of two up to the first one at least $`x`$ gives $`\psi(x)\le4Lx<3x`$. Both $`\sum\Lambda W_m`$ and $`\sum W_m`$ are nonnegative and bounded respectively by $`\psi(x)`$ and $`x`$. Substitution bounds the last display by $`55/x`$ for $`x\ge4`$. As $`\mu-2L/x=\mu(1-4/x)\ge\mu/2`$ for $`x\ge8`$ and $`\mu>1/3`$, this gives $`|Z-S|\le330/x`$. Factoring the difference of two squares yields

```math
|Z^2/x-S^2/x|\le 1980/x+108900/x^3\le3700/x \qquad (x\ge8).
```

Sum this at $`x=n^2`$ and use $`\sum_{n=K}^M n^{-2}\le1/(K-1)`$ to obtain (A). The exact inversion (3) applies also at $`x=4`$, where this estimator has a zero denominator. At $`K=24`$ the block contains the 148 bases from 24 through 171. Summing the actual odd lags by polynomial convolution, subtracting the estimated energy from the mean diagonal and deducting the full tolerance in (A) still leaves more than $`0.5442`$. [Verification record](CHECKS.txt)

## An absolute first moment on every square block

Write $`V_K=\langle |S|\rangle_K`$. The triangle inequality applied to (4) and (5) gives

```math
\left|\,|R_o|+|R_e|-2\mu|S|\,\right|\le S^2/x+O(1).
\tag{6}
```

The following lower bound prevents the constant in (6) from dominating the denominator. For any fixed nontrivial zero $`\rho=\beta+i\gamma`$ with $`\beta\ge1/2`$, and $`X=4K^2\sqrt{\log K}`$,

```math
V_K\gg_\rho \frac{K^2}{N}X^{\beta-1/2}
\quad\text{for every sufficiently large }K.
\tag{7}
```

To see this, put $`f(y)=S(y)/\sqrt y`$. The [single-zero integral in the shorter-block theorem, equations (1)–(3)](https://github.com/leecrossley/prime-window-power-samples/blob/v1.2.0/pairs/SHORT-BLOCKS.md) supplies a kernel $`h_\rho`$ dominated in absolute value by a constant times a bounded probability density $`k`$, with

```math
\int_{\mathbb R}h_\rho(v) f(Xe^v)\,dv
   =c_\rho X^{\rho-1/2}+O_\rho(X^{-5/2}),\qquad c_\rho\ne0.
```

Truncation at $`|v|\le\frac12\log(2\log X)`$ has error $`O_\rho(X^{-7/2})`$. On these cells $`j=\lfloor\sqrt{Xe^v}\rfloor`$ lies between $`K`$ and $`M`$ for all large $`K`$. The mass of each cell under $`k(v)\,dv`$ is at most $`2\|k\|_\infty/j`$.

One needs a vanishing rounding error to include $`\beta=1/2`$ in (7). Off the knots the derivative of $`S`$ is the sum of $`b_m/m`$ over $`y/2<m<y`$ minus half the sum over $`y/4<m<y/2`$. Both are $`o(1)`$ uniformly as $`y\to\infty`$, by partial summation from $`\sum_{m\le t} b_m=o(t)`$. Thus $`f'(y)=o(y^{-1/2})`$ away from the knots. The tent is continuous and piecewise smooth on each compact interval. Integrating up to the next square a distance at most $`2j+1`$ away gives $`f(Xe^v)=S(j^2)/j+o(1)`$ uniformly. Taking absolute values in the integral yields

```math
|c_\rho|X^{\beta-1/2}\le o(1)+\frac{C_\rho}{K}
\sum_{K\le j\le M}\frac{|S(j^2)|}{j}
\le o(1)+\frac{C_\rho N}{K^2} V_K .
```

This proves (7), including for a zero of arbitrary multiplicity through the cited kernel. One known critical-line zero gives $`V_K\gg K/\sqrt{\log K}`$. The [absolutely convergent tent explicit formula](https://github.com/leecrossley/prime-window-power-samples/blob/e4de5134777c660f14a6013ab192d41812d1eab2/PROOF.md) gives $`S(x)=O(x^\Theta)`$, including the bounded lattice error. Apply this upper bound at $`M^2`$ and take the supremum over the lower bounds (7). It follows that $`\log V_K/\log K\to2\Theta`$. [Finite verification of critical-line zeros](https://arxiv.org/abs/2004.09765)

## Relative and absolute upper bounds

Put $`d_K=\sup_{x\ge K^2}|S(x)|/x=o(1)`$. Then $`\langle S^2/x\rangle_K\le d_K V_K`$. Equations (5)–(7) give $`U_K=(2\mu+o(1))V_K`$ and

```math
0<\eta_K\ll d_K+1/V_K.
\tag{8}
```

In particular the ratio tends to zero. For a quantitative bound write $`\ell(t)=(\log t)^{3/5}(\log\log t)^{-1/5}`$ at large $`t`$. The prime number theorem with remainder gives $`|S(x)|/x\ll e^{-c\ell(x)}`$ by partial summation over $`[x/4,x]`$ against the bounded-variation tent. Polynomial factors in $`\log x`$ are absorbed by decreasing $`c`$. This proves the exponential bound in the theorem. The triangle inequality also gives $`U_K\le\langle\sum_{h\ge1}|r_h|\rangle_K`$, where $`r_h`$ denotes the individual ordered, normalized summand for shift $`h`$. Thus (8) bounds the fraction remaining relative to the variation over individual shifts as well. The exact exponent in (1) concerns the two parity subtotals. [Johnston and Yang, Theorem 1.4](https://arxiv.org/pdf/2204.01980)

For a fixed zero-free half-plane $`\Re s>\sigma`$ with $`1/2\le\sigma<1`$, the same explicit formula gives $`d_K\ll K^{-2(1-\sigma)}`$. With the published $`\sigma=7/8`$ estimate, (7)–(8) give $`\eta_K\ll K^{-1/4}`$. Equation (5) also gives $`G_K\ll1+(M^2)^{2\sigma-1}\ll K^{3/2}(\log K)^{3/4}`$ at that value of $`\sigma`$. This corollary imports the September 2026 theorem about the $`7/8`$ half-plane. The argument for (1) uses the prime number theorem and the single-zero integral independently of that input. [Seven-eighths theorem and formalization](https://github.com/openai/math/blob/main/lean/docs/003.md) · [Pinned proof declaration](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)

It remains to determine the numerator's exponent. If $`\Theta>1/2`$, the shorter-block theorem bounds $`\sum S(n^2)^2/n^2`$ below by a constant times $`KX^{2\beta-1}`$ on every sufficiently large block, for each fixed zero with $`\beta>1/2`$. Division by $`N`$ and (5) give the lower exponent $`4\beta-2`$. The pointwise bound $`S(x)=O(x^\Theta)`$ gives upper exponent $`4\Theta-2`$. If $`\Theta=1/2`$, (5) gives $`B/2<G_K=O(1)`$ for all sufficiently large $`K`$. In both cases $`\log G_K/\log K\to4\Theta-2`$. Subtracting $`\log U_K/\log K\to2\Theta`$ proves (1). As a consequence, a bound $`\eta_K\le K^{-1+o(1)}`$ along any unbounded sequence would force $`\Theta=1/2`$.

The exact target is $`G_K\le-\langle P_{\mathfrak S}\rangle_K`$, where $`P_{\mathfrak S}`$ is the signed contribution of $`\mathfrak S(h)-1`$ before subtraction. Its right side is $`2I\log K+O(\log\log K)`$. Equation (5) reduces this to the mean square of the single odd-shift statistic, up to an additive $`o(1)`$ and the explicit constant $`B`$. In particular, any fixed $`\epsilon>0`$ and an unbounded sequence on which

```math
\frac1N\sum_{n=K}^M\frac{\big(R_o(n^2)-(\log2)^2\big)^2}{n^2}
\le (2I\mu^2-\epsilon)\log K,\qquad 2I\mu^2=0.0546302168994\ldots,
```

would suffice. Formula (3) gives an exact version if the sign at a boundary matters. The short-block theorem makes the diagonal target on an unbounded sequence equivalent to RH. On any block that passes, (7) forces $`\eta_K\ll(\log K)^{3/2}/K`$ for $`K`$ sufficiently large. More generally, an independent saving $`\eta_K\le K^{-a+o(1)}`$ along an unbounded sequence would rule out $`\Re\rho>1-a/2`$ by (1). For example $`a=1/3`$ would give the half-plane $`\Re s>5/6`$. [Exact threshold](PAIR-DISCREPANCY.md#the-missing-estimate-and-earlier-work) · [Published block criterion](https://github.com/leecrossley/prime-window-power-samples/blob/v1.2.0/pairs/SHORT-BLOCKS.md)

## Earlier work and checks

The odd-gap prime-power observation and the relation between averaged pair errors and prime-counting errors have precedents. Chou, Haag, Huryn and Ledoan explicitly isolate powers of two at odd gaps, and bound a sum of squares of raw per-gap errors. Earlier work on the signed mean for a sharp cutoff also recovers a linear prime-counting error and its square. Matomäki, Radziwiłł and Tao treat typical shifts, and Goldston and Suriajaya analyze the Cesàro mean of the singular series. Stechkin and Popov study integral averages of the ordinary prime-number-theorem error. I found no earlier statement of (1) for this tent, this parity ratio and all these square blocks, or of the explicit approximation (A). The exponent follows from the earlier block detector once the parity identity is in place. Priority for these specializations remains unconfirmed. [Chou et al.](https://arxiv.org/abs/2308.14888) · [Sharp-cutoff signed mean, equation (4)](https://zeta.teal-sea.com/read/hunts/prime_pair_error/SIGNED_MEAN_RENEWAL.html) · [Matomäki et al.](https://arxiv.org/abs/1707.01315) · [Goldston and Suriajaya](https://arxiv.org/abs/2007.14616) · [Stechkin and Popov](https://www.mathnet.ru/eng/rm1018)

Lean checks eight lemmas, including the ordered cross sum and its inversion, the estimate used in (8), and the deduction of the tolerance in (A) from the pointwise bounds $`|S|\le3x`$ and $`|Z-S|\le330/x`$. The trapezoid estimate, prime-number-theorem inputs and limiting arguments are written proofs. Exact rational arithmetic checks the dyadic partition at 3,988 scales. Arb at 160 and 256 bits checks every odd lag by polynomial convolution and sums every sample on seven finite blocks. Direct nested loops give a further check at small integer and rational scales. [Lean source](ShiftParity.lean) · [Interval and rational checks](check_shift_parity.py) · [Reproduction record](CHECKS.txt)
