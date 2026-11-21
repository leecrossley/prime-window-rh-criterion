# A sharp lower limit for the centered pair discrepancy

Lee Crossley · 21 November 2026

Use the [dyadic tent and centered coefficients](README.md). The Hardy–Littlewood singular series $`\mathfrak S(h)`$ is zero for odd positive $`h`$. At even positive $`h`$ it is $`2C_2\prod_{p\mid h,\ p>2}(p-1)/(p-2)`$, where $`C_2=\prod_{p>2}(1-(p-1)^{-2})`$. For real $`x\ge4`$ define the signed, normalized discrepancy

```math
R(x)=\frac{2}{x}\sum_{h\ge1}\sum_{m\ge1}
\big[b_m b_{m+h}-(\mathfrak S(h)-1)\big]W(m/x)W((m+h)/x).
```

The factor two counts both orders. Centering means $`b_m=\Lambda(m)-1`$ on both sides of the separation. This statistic retains prime powers and weights the entire macroscopic interval. The assertion below concerns the aggregate over all separations. An asymptotic for any fixed gap such as $`h=2`$ is a different question.

**Theorem.** There is an explicit constant $`0.36160550<B<0.36160555`$ for which

```math
R(x)=\frac{S(x)^2}{x}+B+o(1),\qquad
\liminf_{n\to\infty} R(n^2)=B.
```

Consequently $`R(x)>0.36`$ for all sufficiently large real $`x`$. Every sufficiently late block $`[K,4K\sqrt{\log K}]`$ contains a growing run of consecutive bases with $`R(n^2)=B+o(1)`$ uniformly on the run. No hypothesis about the real parts of zeta zeros or the distribution of prime pairs is used. The squared sum on an entire arbitrarily late block still needs an independent upper bound.

## The singular series with the original tent

Put $`I=\int W^2=3-4\log2`$, $`a=3/4`$, and $`F(u)=\int_{\mathbb R} W(t)W(t+u)\,dt`$. Then $`F(0)=I`$, $`F`$ is even, and its support is $`[-a,a]`$. The function $`F`$ is twice continuously differentiable, with $`F''(u)=-\int W'(t)W'(t+u)\,dt`$. This follows by differentiating in the sense of distributions, followed by continuity of translation in $`L^2`$. Thus $`F(a)=F'(a)=F'(0)=0`$.

For any $`u`$, the derivative of $`W(t)W(t+u)`$ has uniformly bounded variation. Indeed $`\|W\|_\infty=1`$, $`\mathrm{Var}(W)=2`$, $`\|W'\|_\infty=8`$, and $`\mathrm{Var}(W')=24`$. The trapezoidal rule on the full mesh of spacing $`1/x`$ then gives, uniformly in $`h`$,

```math
\frac1x\sum_m W(m/x)W((m+h)/x)=F(h/x)+O(x^{-2}).
```

On each cell the integrated error from linear interpolation is at most the square of the spacing times the variation of the derivative on that cell. Values outside the support vanish. With $`q(h)=\mathfrak S(h)-1`$, define $`Q(t)=\sum_{1\le h\le t}(t-h)q(h)`$. The unconditional Cesàro formula of Friedlander–Goldston and Montgomery–Soundararajan, as recorded by Goldston and Suriajaya, and the exact sum for the constant sequence one give

```math
Q(t)=-\tfrac12t\log t+\left(1-\tfrac{\gamma_{\rm E}+\log(2\pi)}2\right)t
      +O_\epsilon((1+t)^{1/2+\epsilon}).
```

Here $`t\log t=0`$ at zero, and the bounded fractional-part term of the constant sequence is included in the error. Positivity and the Cesàro formula at $`2y`$ imply $`\sum_{h\le y}|q(h)|=O(y)`$ for $`y\ge1`$. Thus the total error from replacing the discrete overlap by $`F`$ is $`O(x^{-1})`$. [Goldston and Suriajaya, equations (1.2) and (1.8)](https://arxiv.org/pdf/2007.14616)

Write $`P_{\mathfrak S}(x)`$ for the ordered contribution of $`q(h)`$ to the discrepancy definition, with its sign **before** subtraction and with the $`1/x`$ normalization. Since $`F(s)=\int_s^a(u-s)F''(u)\,du`$ for $`0\le s\le a`$, summing over $`h`$ gives

```math
P_{\mathfrak S}(x)=\frac2x\int_0^a Q(xu)F''(u)\,du+O(x^{-1})
=-I\log x+C_W+O_\epsilon(x^{-1/2+\epsilon})
```

for fixed $`0<\epsilon<1/2`$. In the second equality use $`\int_0^a uF''(u)\,du=I`$ and

```math
\int_0^a u\log u\,F''(u)\,du=I(1+\log a)-H_W,
\qquad H_W=\int_0^a\frac{I-F(u)}u\,du.
```

Two integrations by parts give this identity. The contribution at zero vanishes after subtracting $`F(0)`$, since $`F'(0)=0`$ and $`F''`$ is bounded. It follows that $`C_W=(1-\gamma_{\rm E}-\log(2\pi a))I+H_W`$.

## The actual diagonal to constant order

The classical prime number theorem with its logarithmic savings gives, by partial summation on the fixed support,

```math
\frac{A(x)}x=I\log x+J-I+o(1),\qquad J=\int W(t)^2\log t\,dt.
```

Indeed the ordinary-prime part of $`\sum\Lambda(m)^2W(m/x)^2`$ divided by $`x`$ has main term $`\int W(t)^2\log(xt)\,dt`$. The bound $`\vartheta(y)-y=O(y/\log^2 y)`$ makes the error $`o(1)`$ even with the extra logarithm, by partial summation. Proper prime powers contribute $`O(x^{-1/2}\log^3 x)`$ after normalization. The linear and lattice terms in $`(\Lambda-1)^2`$ contribute $`-2I+I+o(1)`$. The identity $`W(1/(4t))=2tW(t)`$ implies that the measure $`W(t)^2dt`$ is invariant under $`t\mapsto1/(4t)`$, so $`J=-I\log2`$. [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442)

The observed ordered-pair sum before subtracting $`P_{\mathfrak S}(x)`$ is exactly $`(S(x)^2-A(x))/x`$. The logarithmic terms cancel in $`-A(x)/x-P_{\mathfrak S}(x)`$. Since $`a=3/4`$, the constant that remains is

```math
B=(\gamma_{\rm E}+\log(3\pi))I-H_W.
```

In particular the local factors already give the leading $`-I\log x`$ in the ordered unequal-pair sum. At constant order they underestimate the observed signed aggregate by at least $`B-o(1)`$.

## Why the lower limit is sharp at squares

The identity just proved and the nonnegativity of $`S(x)^2`$ give $`\liminf R(n^2)\ge B`$. Here is one way of checking the reverse inequality without the quantitative short-block result. The Mellin transform $`\int_0^\infty S(x)x^{-s-1}\,dx`$ equals

```math
\widehat W(s)\left(-\frac{\zeta'(s)}{\zeta(s)}-\zeta(s)\right),\qquad
\widehat W(s)=\frac{(1-2^{-s})(1-2^{1-s})}{s(s-1)}
```

initially for $`\Re s>1`$. Both factors continue across every real point $`s>0`$ with the values at $`1`$ taken by cancellation. There is a pole at any nontrivial zeta zero, since the log derivative has nonzero residue there and the tent transform is nonzero throughout $`0<\Re s<1`$. One known critical-line zero suffices. If $`S`$ had an eventual fixed sign, Landau's theorem for the Mellin transform of a nonnegative function would force a real singularity at its abscissa of convergence. The abscissa would be in $`[1/2,1]`$ by that pole and absolute convergence for $`\Re s>1`$. Removing the finite initial interval changes the transform by an entire function, since $`S(x)=0`$ for $`0<x<1`$. This contradiction gives arbitrarily late values of each sign. Continuity then gives arbitrarily late real zeros $`y`$ of $`S`$. [Landau's oscillation argument, §4](https://arxiv.org/pdf/2007.14616) · [An independently verified critical-line zero range](https://arxiv.org/abs/2004.09765)

Off its knots, $`S'(x)=\sum_{x/2<m<x}b_m/m-\tfrac12\sum_{x/4<m<x/2}b_m/m=o(1)`$ uniformly at large $`x`$, by partial summation from $`\psi(t)-\lfloor t\rfloor=o(t)`$. The tent is continuous through the finitely many knots on each compact interval. For $`n=\lceil\sqrt y\rceil`$ one has $`|n^2-y|=O(n)`$, hence $`S(n^2)/n=o(1)`$ along these squares. This proves the sharp lower limit. The more precise statement for a run in *every* sufficiently late short block follows by substituting the uniform $`S(n^2)/n=o(1)`$ from the theta-average proof into the discrepancy identity. [Theta average and passage to consecutive squares](https://github.com/leecrossley/prime-window-power-samples/blob/v1.2.0/pairs/THETA.md#from-an-average-to-consecutive-square-samples)

## Two checks of the sign and size

Since $`I-F(u)=\tfrac12\int(W(t+u)-W(t))^2\,dt`$ and $`W\ge0`$, it is bounded above by $`\min(I,7u^2/2)`$. Here $`\int |W'|^2=7`$. Integrating this elementary majorant split at $`\sqrt{2I/7}<a`$ yields $`H_W\le I/2+I\log(a\sqrt{7/(2I)})`$. This alone gives $`B>0.2822`$.

For a narrower interval let $`G(u)=(I-F(u))/u`$, continuously extended to zero. One has $`G'(u)=-\int_0^1 tF''(tu)\,dt`$. Translation of a function of bounded variation in $`L^1`$ gives $`|F''(u)-F''(v)|\le\|W'\|_\infty\mathrm{Var}(W')|u-v|\le192|u-v|`$. Therefore $`G'`$ is Lipschitz with constant at most $`64`$. The composite midpoint rule over $`N`$ cells has absolute error at most $`64a^3/(24N^2)`$. On each overlap of branches, the two tent values multiply to $`(c+d/t)(e+f/(t+u))`$. Its integral requires only rational operations and real logarithms. Arb enclosed the integral on 16,384 midpoint cells at 160 and 256 bits. Direct enumeration by lag at $`x=16,64,256`$ checks the ordered-pair convention independently of diagonal subtraction. [Certificate](check_discrepancy.py) [Transcript](CHECKS.txt)

## The missing estimate and earlier work

Exactly $`E_K-D_K=\sum_{K\le n\le M}(R(n^2)+P_{\mathfrak S}(n^2))`$. Thus the exact threshold for the mean of $`R`$ is the mean of $`-P_{\mathfrak S}(n^2)`$. It is $`I(2\log K+\log\log K+2\log4-2)-C_W+o(1)`$. Indeed the mean of $`\log n`$ on this block is $`\log M-1+o(1)`$ by integration, since $`K\log(M/K)/(M-K)\to0`$. The proved lower limit is of constant size. It precludes replacing the entire ordered-pair sum by its singular-series model with normalized error $`o(1)`$ on these scales and leaves room for errors much larger than $`\log K`$. The finite bound in the companion note uses a different estimate.

One way to try to prove the upper estimate is to bound each separation before summing. Even a bound of $`O(x/\log^A x)`$ for the inner weighted error at **every** separation, for an arbitrary fixed $`A`$, gives only $`O(x/\log^A x)`$ for $`R(x)`$ by the triangle inequality. There are order $`x`$ separations and the normalization is $`2/x`$. This falls short of logarithmic size. The averaged results of Matomäki, Radziwiłł and Tao concern typical shifts and give logarithmic savings. A direct proof along this route would need cancellation in the signed sum beyond what the individual size estimates give. [Matomäki, Radziwiłł and Tao](https://arxiv.org/abs/1707.01315)

The modified singular series for centered prime tuples and the extraction of a lower-order contribution from pair separations are classical. Montgomery and Soundararajan study short-interval moments under a quantitative prime-tuple hypothesis. Goldston and Suriajaya give the unconditional Cesàro formula used here. Chou, Haag, Huryn and Ledoan study a sum of **squares of raw per-gap errors** in prime-pair counts. Their paper also relates a pair-error conjecture to RH. A contemporaneous note on the aggregate residual in short-interval variance likewise distinguishes the computable singular-series contribution from the actual prime correlations. The exact constant, its lower limit at squared scales for this particular tent and its attainment in the late runs are the scope of this calculation. [Montgomery and Soundararajan](https://arxiv.org/abs/math/0409258) · [Goldston and Suriajaya](https://arxiv.org/abs/2007.14616) · [Chou, Haag, Huryn and Ledoan](https://arxiv.org/abs/2308.14888) · [Earlier aggregate-error formulation](https://unboundedaxiom.org/p/lm-003946/)

Kuperberg treats singular series with smooth weights. Her theorem concerns the model sum. Here the comparison includes the actual centered Mangoldt pairs and attainment of the constant on square samples. [Kuperberg](https://arxiv.org/abs/2301.06095)
