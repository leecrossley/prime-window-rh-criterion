# The median of the prime-counting error on a block of squares

Lee Crossley · 21 November 2026

Let $`E(t)=\pi(t^2)-\operatorname{li}(t^2)`$, $`E_n=E(n)`$, $`L=\log\log K`$, $`H=\lfloor K/L\rfloor`$, $`J_K=\{K,\ldots,K+H\}`$, $`N=H+1`$, and $`T_K=K(\log K)^2`$. A median $`m_K`$ has at least half the observations on either side, including equality. All conclusions apply to every possible median. Write $`B_K=\#\{n\in J_K:|E_n-m_K|>T_K\}`$.

The question is whether $`B_K=O(K^{1-\eta})`$ on some unbounded sequence for a fixed $`\eta>0`$, independently of the full Riemann hypothesis. The previous proof gives $`B_K=K^{1-o(1)}`$ on every sufficiently late block if even one zero has real part greater than $`1/2`$. Under RH the classical $`E_n=O(n\log n)`$ gives $`B_K=0`$ on every sufficiently late block. The independent upper bound for $`B_K`$ remains unresolved here. [Prior median criterion](SHORT-ARITHMETIC.md) · [Conditional prime-counting bound and its finite versions](https://arxiv.org/abs/2109.02249)

Two results concern the exact block and its actual median. Unconditionally, $`B_K=0`$ for every integer $`16\le K\le1\,290\,008\,597\,927\,572`$. On every sufficiently late block at least $`\lfloor(\log K)^3/4\rfloor`$ consecutive samples pass. The latter gives only a small saving from the trivial upper bound $`N`$.

An estimate at unbounded height removes the fluctuations between a fixed grid of samples. Divide the exact block into consecutive groups of $`d=\lfloor K^{1/8}\rfloor`$ integers. The groups on which the range of $`E`$ exceeds $`K^{127/128}`$ contain, altogether, $`O(K^{31/32})`$ integers. This applies to the real range over each corresponding full closed interval of length $`d`$. The unresolved part is the variation from one group to the next. The proof uses the independent zero-free half-plane $`\Re s>7/8`$, with no use of the full RH. [Seven-eighths theorem](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)

## A finite bound for the actual median

Johnston's Theorem 4.1 gives $`|E_n|<2a n\log n`$ when $`c n/(2\log n)^{3/2}\le 3\cdot10^{12}`$, for $`(a,c)=(1,1.19)`$ and $`(10,0.117)`$. The input on the zeros is the finite verification of Platt and Trudgian. For $`n\ge16`$ the left side increases. The last eligible integers for the two rows are respectively

```math
z_1=1\,471\,729\,207\,270\,810,\qquad z_{10}=16\,551\,346\,706\,300\,673 .
```

The last $`K`$ with $`K+\lfloor N/2\rfloor\le z_1`$ is $`K_*=1\,290\,008\,597\,927\,572`$. At that base $`H=363\,441\,218\,686\,476`$, the middle index equals $`z_1`$, and $`K_*+H=1\,653\,449\,816\,614\,048<z_{10}`$. At $`K_*+1`$ the middle index is $`z_1+1`$. The endpoint and middle index increase for $`K\ge16`$, since $`K/\log\log K`$ has positive derivative there. Both zero-height inversions were checked by integer bisection and by the negative real branch of Lambert $`W`$. [Johnston, Table 2 and Theorem 4.1](https://arxiv.org/pdf/2109.02249#page=10) · [Finite zero verification](https://arxiv.org/abs/2004.09765)

For $`10^{15}<K\le K_*`$ a strict majority of the samples, namely the prefix through $`K+\lfloor N/2\rfloor`$, obey the $`a=1`$ bound. Every sample obeys the $`a=10`$ bound. With $`v=K+H`$ it follows for every median that $`|E_n-m_K|\le22v\log v`$. Here $`v\le1.3K`$, so the ratio to $`T_K`$ is below $`0.835`$. Whenever $`v\le fK`$ with fixed $`f\ge1`$, the expression $`f\log(fK)/(\log K)^2`$ decreases with $`K`$.

For $`10^6\le K\le10^{15}`$ all samples are within $`z_1`$ and $`v\le1.4K`$. The bound $`4v\log v`$ gives a ratio below $`0.416`$. For $`52\le K<10^6`$, $`2657\le n^2\le(2\cdot10^6)^2`$. Johnston's Corollary 3.3 gives $`|E_n|<n\log n/(4\pi)`$ there. Thus $`|E_n-m_K|\le v\log v/(2\pi)`$ and the ratio is below $`0.095`$. For $`16\le K\le51`$ the replay enumerates every prime count, evaluates the logarithmic integrals with intervals, and checks both endpoints of the set of medians. The value $`K_*`$ is the endpoint of this certificate. [Arithmetic replay](check_median_exceptions.py)

## A consecutive run at the true median

Uniformly for $`n,n+1\in J_K`$, the expected count in $`(n^2,(n+1)^2]`$ is $`(1+o(1))K/\log K`$, by integrating $`1/\log t`$. Brun–Titchmarsh bounds the actual count by $`2(2n+1)/\log(2n+1)=(4+o(1))K/\log K`$. Hence adjacent values of $`E_n`$ differ by at most $`(3+o(1))K/\log K`$. Every median lies between the minimum and maximum, so a sample equals the median or two consecutive values straddle it. In the latter case one is within half a step bound of it. From that sample, take $`\lfloor(\log K)^3/4\rfloor`$ consecutive indices in the direction with more room. The sum of their possible increments is less than $`T_K`$ for sufficiently large $`K`$. [Montgomery and Vaughan, *The large sieve*](https://doi.org/10.1112/S0025579300004708)

## Fluctuation inside groups of consecutive squares

Use $`u=\log(t/K)`$ and $`x=t^2=K^2e^{2u}`$ for $`K\le t\le 3K`$. Take a common truncation height $`T\in[K^{9/8},K^{9/8}+1]`$ different from every zero ordinate. Uniformly in this range of real $`x`$,

```math
\psi(x)-x=-\sum_{|\gamma|<T}\frac{x^\rho}{\rho}+O(K^{7/8}\log^2 K).
\tag{1}
```

Apply the truncated explicit formula at $`\lfloor x\rfloor+1/2`$, where $`\psi`$ has the same value. Its error is $`O(K^2\log^2 K/T)`$. Moving the powers back to $`x`$ costs $`O(K^{-1/4})`$ per zero by the seven-eighths theorem and differentiation of $`x^\rho/\rho`$. There are $`O(T\log T)`$ zeros with multiplicity. This proves (1), including the jump points of $`\psi`$. [Dudek, Theorem 2.1](https://arxiv.org/pdf/1401.4233#page=4) · [Zero count](https://doi.org/10.1090/mcom/4133)

Split the zeros into dyadic height ranges $`Y\le|\gamma|<2Y`$ and narrow real-part strips $`s\le\beta\le s+w`$, assigning each boundary once. For $`1/2\le s\le7/8`$ use

```math
p_I(s)=\frac{3(1-s)}{2-s},\qquad p_H(s)=\frac{3(1-s)}{3s-1},\qquad
p_G(s)=\frac{15(1-s)}{3+5s},\qquad p(s)=\min(p_I,p_H,p_G).
```

The count in the strip is $`O_\epsilon(Y^{p(s)+\epsilon})`$ by Ingham, Huxley, and Guth–Maynard. For $`\beta<1/2`$ use the real-part upper bound $`1/2`$ and exponent $`p=1`$ from ordinary zero counting. [Density estimates (1.2), (1.3) and Theorem 1.2](https://arxiv.org/pdf/2405.20552#page=2)

Let $`Z(u)`$ be the sum from a single group in (1), allowing any subset of the group's zeros. On a fixed compact interval containing $`[0,\log3]`$ the following squared norms hold, with the same bounds on any smaller interval:

```math
\|Z\|_2^2\ll_\epsilon K^{4(s+w)}Y^{p(s)-2+\epsilon},\qquad
\|Z'\|_2^2\ll_\epsilon K^{4(s+w)}Y^{p(s)+\epsilon}.
\tag{2}
```

To see this, majorize the interval integral by a nonnegative smooth cutoff equal to one there. In the expanded square, two integrations by parts bound each oscillatory integral by $`O((1+|\gamma-\gamma'|^2)^{-1})`$. The real exponential and its first two derivatives are uniformly bounded on the cutoff's support. The sum of these bounds in a row is $`O(\log(2Y))`$, since each unit interval in the height group contains $`O(\log(2Y))`$ zeros. The inequality $`2|ab|\le |a|^2+|b|^2`$ reduces the sum to the squared coefficients. Differentiation multiplies each coefficient by $`2\rho`$. This proves (2) with multiplicities and without any spacing hypothesis.

Write $`U=K/d\asymp K^{7/8}`$. Partition starting at $`K`$ and, if necessary, extend the last group to a full interval. Its extra points can be discarded at the end. Their logarithmic intervals $`I`$ have disjoint interiors and lengths $`\asymp1/U`$. Write $`g(u)=1/\log(K^2e^{2u})`$. A single group's contribution to a difference of ordinary prime-count errors is $`\int g\,dZ`$. For $`Y\le U`$ its squared oscillation on $`I`$ is at most $`O(|I|\int_I|Z'|^2)`$ by Cauchy–Schwarz. For $`Y>U`$ integration by parts bounds the oscillation by $`O(\sup_I|Z|)`$. For an interval of length $`\ell`$,

```math
\sup_I|Z|^2\le \ell^{-1}\int_I|Z|^2+2\int_I|Z Z'|.
```

This follows by integrating the derivative of $`|Z|^2`$ from a point with value at most its interval mean. Sum these bounds with weight $`1/U`$ per interval and use (2). For low heights the result is at most $`O_\epsilon(K^{4(s+w)}U^{-2}Y^{p(s)+\epsilon})`$. For high heights it is at most $`O_\epsilon(K^{4(s+w)}Y^{p(s)-2+\epsilon}(1+Y/U))`$. Since $`0\le p(s)\le1`$ and $`Y\ll K^{9/8}`$, both are bounded, up to a factor $`K^{O(\epsilon)}`$, by $`K^{4(s+w)}U^{p(s)-2}`$. The high-height estimate controls the supremum over the entire interval. There is no multiplication by the number of samples in the interval.

For the remainder in (1), Stieltjes integration by parts against $`g`$ costs $`O(K^{7/8}\log K)`$ pointwise in a local difference. For the prime powers, $`d\pi(x)=(d\psi(x)-d(\psi-\vartheta)(x))/\log x`$. Each $`p^j`$ with $`j\ge2`$ therefore has weight $`1/j`$ to remove. A group of width $`d`$ in $`t`$ meets at most $`d+1`$ possible prime bases of squares. The total number of powers of degree at least three before $`9K^2`$ is $`O(K^{2/3}\log K)`$. These two errors contribute at most $`K^{7/4+o(1)}`$ to the squared, normalized oscillation bound.

Finally one has

```math
4s-\tfrac78(2-p(s))\le \tfrac{203}{104},\qquad \tfrac12\le s\le\tfrac78 .
```

For $`s\le3/4`$ it suffices to use $`p_I`$. For $`s\ge3/4`$ it suffices to use $`p_H`$, with equality for that bound at $`7/8`$. The lower half of the strip contributes at most exponent $`2-7/8`$. The two rational inequalities are checked in Lean. Take fixed strips of sufficiently small width, sum their root mean squares and the $`O(\log K)`$ dyadic groups by Minkowski, and then let the width and the exponent losses tend to zero. With $`\operatorname{osc}_I E`$ denoting the real range over the corresponding interval in $`t`$, the result is

```math
\frac dK\sum_I(\operatorname{osc}_I E)^2\ \ll_\epsilon K^{203/104+\epsilon}
\quad\text{for every fixed }\epsilon>0 .
\tag{3}
```

For intervals with oscillation exceeding $`K^{127/128}`$, Markov's inequality now bounds the total number of their integer samples by $`O(K^{31/32})`$. Indeed $`2(127/128)-203/104-1/32=1/832>0`$. The same argument on a full interval of the original length would have $`U\asymp\log\log K`$, which contributes no negative power of $`K`$ in (2).

More generally, for $`d=\lfloor K^a\rfloor`$ with fixed $`0<a<7/46`$, the squared exponent in (3) is at most $`\max\{7/4,\,7/2-(23/13)(1-a)\}+\epsilon<2`$ for sufficiently small $`\epsilon`$. Indeed $`4s-(1-a)(2-p_I(s))`$ on $`[1/2,3/4]`$ and $`4s-(1-a)(2-p_H(s))`$ on $`[3/4,7/8]`$ both increase with $`s`$. Their derivatives are at least $`4-3/(5/4)^2`$ and $`4-6/(5/4)^2`$, respectively, and the two expressions coincide at $`3/4`$. The right endpoint has $`p_H(7/8)=3/13`$. For example, at $`a=3/20`$ the squared exponent is $`2-1/260+\epsilon`$. The groups of this length with real oscillation exceeding $`K`$ contain in total $`O(K^{1-1/300})`$ sample indices. This allows the grid below to be thinned to $`\asymp K^{17/20}/L`$ points with a smaller fixed saving.

## What remains on the grid

Take the leftmost sample of each complete group. This gives $`G=\lfloor N/d\rfloor`$ grid values, with $`G\asymp K^{7/8}/L`$. If, on an unbounded sequence, all but $`O(G^{1-\xi})`$ of these values lie within $`T_K/3`$ of a common real number, for some fixed $`0<\xi<1`$, the requested full-median assertion follows.

In fact at most $`O(K^{31/32})`$ samples belong to groups of large oscillation. At most $`d\,O(G^{1-\xi})=O(K^{1-7\xi/8})`$ samples belong to groups with an exceptional grid value. There are fewer than $`d`$ leftover samples. Every other sample lies within $`T_K/3+K^{127/128}`$ of the common number. These samples form a strict majority, so every full-block median lies in that same band. The total difference between such a sample and the median is at most $`2(T_K/3+K^{127/128})<T_K`$ for large $`K`$. This gives $`\eta=\min(1/32,7\xi/8)`$. The estimates within groups supply no independent proof of concentration of the grid values themselves.

## A bound on the part outside the low right-hand zeros

There is a second way to isolate the missing contribution directly on the full block. Set $`\delta=1/256`$, $`q(s)=(4s-2+\delta)/(2-p(s))`$, and

```math
\mathcal Z_K=\{\rho=\beta+i\gamma:\ \beta>1/2,\ 3\cdot10^{12}<|\gamma|\le K^{q(\beta)}\}.
```

For some real $`c_K`$ and all but $`O(K^{1-1/512})`$ of the integers $`n\in J_K`$ one has

```math
E_n=c_K-\sum_{\rho\in\mathcal Z_K}
             \int_{K^2}^{n^2}\frac{y^{\rho-1}}{\log y}\,dy
             +O(K\log K),\qquad \#\mathcal Z_K\ll K^{3/7}.
\tag{4}
```

Both signs of the ordinates and all multiplicities are included. The bound is independent of the full RH. Formula (4) estimates the omitted part on actual samples. It leaves the signed sum displayed there to be controlled.

For the discarded right-hand zeros apply the high-height supremum argument used in (2) to the unit cells in $`t`$. The factor $`1+Y/U`$ becomes $`1+Y/K`$. Both the continuous squared norm and the discrete squared norm with weight $`1/K`$ are thus bounded on a strip by $`K^{4(s+w)}Y^{p(s)-2+o(1)}(1+Y/K)`$. For $`Y\le K`$ each discarded zero has $`Y\ge \frac12 K^{q(s)-O(w)}`$. For $`Y\ge K`$ the factor $`Y^{p(s)-1}`$ decreases weakly. The definition of $`q`$ and $`q(s)<7/8`$ give an upper exponent $`2-\delta+O(w)`$ in both cases. Here $`q(s)<7/8`$ follows from the preceding bound $`203/104<2-\delta`$, and $`q`$ is Lipschitz on each of its finitely many smooth pieces. Therefore the square norms of the whole discarded sum $`Z_{\rm high}`$ are $`O_\epsilon(K^{2-\delta+\epsilon})`$. In particular $`|Z_{\rm high}(\log(n/K))|\le K`$ outside $`O(K^{1-1/512})`$ samples.

In passing from $`\psi`$ to ordinary counts, integrate $`g\,dZ_{\rm high}`$ by parts. Absorb its left endpoint in $`c_K`$. The cumulative integral of $`g'Z_{\rm high}`$ is uniformly $`O(K^{1-\delta/2+o(1)})`$ by its continuous norm. For all zeros with $`\beta\le1/2`$ the absolute sum in (1) is $`O(K\log^2K)`$ through the truncation height, hence their effect in the ordinary count is $`O(K\log K)`$ uniformly by partial summation. Prime powers over the full block cost $`O(K+K^{2/3}\log K)`$. The remainder from (1) is also within the error in (4). Finite verification excludes all right-half zeros at or below the lower cutoff. The retained powers give the displayed integrals by differentiation. [Finite verification](https://arxiv.org/abs/2004.09765)

To count the residual zeros, the fixed-strip argument gives upper exponent $`\max_s p(s)q(s)`$. One has $`p(s)(4s-2)/(2-p(s))\le36/85`$. Up to $`7/10`$ use $`3(1-s)(4s-2)/(1+s)`$ from Ingham. Above $`7/10`$ use $`15(1-s)(4s-2)/(25s-9)`$ from Guth–Maynard. After multiplication by positive denominators the two differences from $`36/85`$ have numerators $`(7-10s)(78-102s)`$ and $`(10s-7)(510s-318)`$ respectively. Both are nonnegative in their stated ranges. Since $`p/(2-p)\le1`$ and $`36/85+1/256<3/7`$, the strip-width and density losses fit inside the stated upper exponent.

A single fixed off-line conjugate pair illustrates why a bound on the number of terms alone is insufficient. For $`\rho=\beta+i\gamma`$ with $`\beta>1/2`$ and $`\gamma\ne0`$, take only its pair in the signed sum in (4). For every real centre $`c`$, at most $`O_\rho(K^{3/2-\beta}(\log K)^{3/2}+1)`$ samples of that pair lie within $`T_K`$ of $`c`$ on any sufficiently late block. To verify this, write its value as a function of $`u=\log(t/K)`$. Up to sign, its derivative is $`2t^{2\beta}\cos(2\gamma\log t)/\log t`$. Put $`A=K^{2\beta}/\log K`$ and $`\tau=(T_K/A)^{1/2}`$. The phase interval eventually has length less than $`\pi/4`$. Where $`|\cos|\le\tau`$ the total $`u`$-length is $`O_\rho(\tau)`$. The remainder has a bounded number of monotone pieces with derivative of magnitude $`\gg A\tau`$, so the preimage of a band of width $`2T_K`$ has length $`O_\rho(T_K/(A\tau))`$. These sets are unions of a bounded number of intervals, each containing at most its length times $`O(K)`$ plus one square-root samples. This proves the claim for the single pair. Other zeros in the actual sum can interfere with it.

## Prior work and verification

Johnston already proved the two finite prime-counting estimates. The explicit endpoint here applies them to a strict majority and the remainder of the same block. Richards studied normal prime density in short intervals under a fixed zero-free half-plane. Bazzanella and Perelli use explicit formulas and density estimates for exceptional sets of prime counts in short intervals. Bazzanella also gives bounds for individual gaps between consecutive squares. These results concern local increments. The remaining estimate here concerns their accumulated errors across the grid. [Johnston](https://doi.org/10.1007/s11139-022-00616-x) · [Richards](https://doi.org/10.1016/0022-314X(80)90031-1) · [Bazzanella and Perelli](https://doi.org/10.1006/jnth.1999.2429) · [Bazzanella on consecutive squares](https://doi.org/10.1007/s000130050469)

Stechkin and Popov study localized prime-counting errors, and Brent, Platt and Trudgian study the continuous mean square of the prime number theorem error. The search did not establish priority for the precise maximal estimate (3), the fixed-grid median test, or the height cutoff in (4). [Stechkin and Popov](https://www.mathnet.ru/eng/rm1018) · [Brent, Platt and Trudgian](https://arxiv.org/abs/2008.06140)

Lean checks the strict-majority argument for arbitrary finite samples, transport of the error to a full median, the prefix cardinality, and the rational exponent inequalities. The numerical checks use two precisions for the height inversion and the analytic range margins, exact prime counts at small scales, exhaustive finite arrays with ties and a nonconstant centre, and complex Gram integrals for both local inequalities. The number-theoretic asymptotics have written proofs. [Lean file](MedianExceptions.lean) · [Arithmetic replay](check_median_exceptions.py) · [Verification record](CHECKS.txt)
