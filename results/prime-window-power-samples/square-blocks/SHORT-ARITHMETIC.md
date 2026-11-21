# The arithmetic mean square on a shrinking block of squares

Lee Crossley · 21 November 2026

Let $`L=\log\log K`$, $`H=\lfloor K/L\rfloor`$, $`N=H+1`$, and $`J_K=\{K,\ldots,K+H\}`$. All asymptotic statements concern integer $`K\to\infty`$. Use the tent $`W(u)=2-1/(2u)`$ on $`[1/4,1/2]`$, $`W(u)=1/u-1`$ on $`(1/2,1]`$, and $`W=0`$ elsewhere. Put $`F(t)=S(t^2)/t`$ with $`S(x)=\sum_m(\Lambda(m)-1)W(m/x)`$. Denote its signed average on $`J_K`$ by $`\bar F_K`$ and its mean square by $`M_K`$. A subpower upper bound on a sequence means $`O_\epsilon(K^\epsilon)`$ for each fixed $`\epsilon>0`$ along the same sequence.

On arbitrarily late $`J_K`$ the signed average satisfies $`|\bar F_K|\ll K^{-1/4}`$ and the full mean square satisfies $`M_K\ll K^{3/2}/L^2`$. These estimates use the separate seven-eighths zero-free theorem. The requested subpower bound for $`M_K`$ remains unresolved by this argument. The earlier shrinking-interval theorem gives $`M_K=K^{4\Theta-2+o(1)}`$ on every sufficiently late block if $`\Theta=\sup_\rho\Re\rho>1/2`$. Under RH the absolutely convergent tent formula gives $`M_K=O(1)`$ on every block. [Earlier proof](SURVIVING-ZEROS.md) · [Seven-eighths theorem](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)

There is a test using only ordinary prime counts. For $`K\le n\le K+H`$ put
```math
U_K(n)=\pi(n^2)-\pi(K^2)-\int_{K^2}^{n^2}\frac{dt}{\log t}.
```
Let $`m_K`$ be a median of these $`N`$ values. An upper bound $`N^{-1}\sum|U_K(n)-m_K|\le K^{1+o(1)}`$ on an unbounded sequence implies the requested bound for $`M_K`$. It even suffices to bound the number of deviations larger than $`K(\log K)^2`$ by $`O(K^{1-\eta})`$ for any fixed $`\eta>0`$ on such a sequence. Under RH the individual $`U_K(n)`$ are $`O(K\log K)`$. In the off-line case the mean absolute deviation and the uncentered root mean square of $`U_K`$ are both $`K^{2\Theta+o(1)}`$ on every sufficiently late block. The proof uses a positive triangular weight with both endpoints in the block. Its repeated-prime contribution has leading constant $`8/45`$.

## The signed average and its variance

The separate seven-eighths theorem gives $`\beta=\Re\rho\le7/8`$ for every nontrivial zero. The truncated explicit formula at half-integers with height $`T`$ comparable to $`x`$ gives $`\psi(x)-x=O(x^{7/8})`$. Indeed the zeros with $`\beta<3/4`$ contribute $`O(x^{3/4}\log^2 x)`$. Ingham's density bound gives $`N(3/4,T)=O(T^p)`$ for some $`p<1`$, so the inverse absolute ordinates for the remaining zeros are summable. Their contribution is $`O(x^{7/8})`$. The truncation error is $`O(\log^2 x)`$ at half-integers and monotonicity transfers the estimate to real $`x`$. [Dudek, Theorem 2.1](https://arxiv.org/abs/1401.4233) · [Ingham](https://doi.org/10.1093/qmath/os-8.1.255) · [Density exponents, equations (1.2)–(1.3)](https://arxiv.org/pdf/2405.20552)

The partial sums of $`b_m=\Lambda(m)-1`$ are therefore $`O(x^{7/8})`$. The tent has bounded variation, so $`S(x)=O(x^{7/8})`$. Away from the knots its derivative is
```math
S'(x)=\sum_{x/2\lt m\lt x} b_m/m-\tfrac12\sum_{x/4\lt m\lt x/2}b_m/m.
```
Partial summation gives $`S'(x)=O(x^{-1/8})`$. Continuity and the piecewise derivative bound give $`|F(t)|\ll t^{3/4}`$ and $`|F'(t)|\ll t^{-1/4}`$ off knots, and hence the corresponding increment bound across knots.

Write $`P(X)=\sum_{n\le X}F(n)`$ and $`A(X)=\int_1^X F(t)\,dt`$. Integration on the unit intervals gives $`P(X)=A(X)+O(X^{3/4})`$, including the final incomplete interval. To see that $`P(X)`$ has large excursions of both signs, take its Mellin transform $`\int_1^\infty P(X)X^{-s-1}dX`$. For $`\Re s`$ sufficiently large the transform of $`A`$ is $`s^{-1}\int_1^\infty F(t)t^{-s}dt`$. The tent explicit formula continues the transform of $`P`$ meromorphically to $`\Re s>3/4`$ as
```math
-\frac1s\sum_\rho\frac{d_\rho}{s-2\rho}+\text{a holomorphic function},\qquad
d_\rho=\frac{(1-2^{-\rho})(2^{1-\rho}-1)}{\rho(1-\rho)}.
```
Indeed $`F(t)=-\sum_\rho d_\rho t^{2\rho-1}+O(t^{-1})`$ and $`\sum_\rho|d_\rho|<\infty`$. A bounded initial segment affects only the holomorphic term here. No nontrivial zero is real. Each zero on the critical line supplies an actual nonreal pole of real part one, since $`d_\rho\ne0`$ and multiplicities add. If $`P(X)+C X^{7/8}`$ were eventually nonnegative, its Mellin integral would have a finite abscissa of convergence at least one, by that pole. Landau's theorem forces a singularity at that real abscissa, where the displayed continuation is regular. The same proof applies to $`-P(X)+C X^{7/8}`$. This rules out an eventual one-sided bound of either sign for every fixed $`C`$. [Tent explicit formula](https://github.com/leecrossley/prime-window-rh-criterion/blob/1bcb390d5876569539f106e7f0e21a79669ead73/results/prime-window-power-samples/pairs/SHORT-BLOCKS.md) · [Landau's Mellin integral argument](https://secure.math.ubc.ca/~gerg/teaching/592-Fall2018/papers/1986.Kaczorowski_1.pdf) · [Platt and Trudgian](https://arxiv.org/abs/2004.09765)

Set $`e(k)=k+\lfloor k/\log\log k\rfloor`$. For large $`k`$ its increments are 1 or 2, since the derivative of $`k/\log\log k`$ lies in $`(0,1)`$. Suppose all sufficiently late blocks had nonnegative sum. Given a large integer $`m`$, choose the largest $`k`$ with $`e(k)\le m`$. This leaves at most one integer after $`e(k)`$, so $`P(m)\ge P(k-1)-O(m^{3/4})`$. Repeat backwards. Until a fixed terminal index, each new endpoint is at most $`m/(1+c/\log\log m)`$ for an absolute $`c>0`$. Hence $`O(\log m\log\log m)`$ steps suffice and $`P(m)\ge-O(m^{3/4}\log m\log\log m)`$. This contradicts the negative excursions just proved, also for real arguments since $`P`$ is a step function. Changing the sign gives the positive excursions of the block sums. Thus the signed averages take both signs arbitrarily late.

Compare consecutive averages by shifting each old sample one place to the right. The change in their mean is $`O(K^{-1/4})`$. If the length grows by one, the extra endpoint differs from this shifted mean by $`O(NK^{-1/4})`$ and has weight $`1/(N+1)`$. Consequently $`|\bar F_{K+1}-\bar F_K|\ll K^{-1/4}`$. Crossings give arbitrarily late integers with $`|\bar F_K|\ll K^{-1/4}`$. On those same blocks $`|F(n)-\bar F_K|\ll H K^{-1/4}`$ throughout, so
```math
M_K=\frac1N\sum_{n\in J_K}(F(n)-\bar F_K)^2+O(K^{-1/2})
       \ll \frac{K^{3/2}}{L^2}.
```
The size of the signed average therefore leaves almost the entire mean square to be explained by the variance.

## A weight using only primes inside the block

Put $`a=K^2`$, $`b=(K+H)^2`$, $`D=b-a`$, and for $`a\le x,t\le b`$ set
```math
G(x,t)=\frac{(\min(x,t)-a)(b-\max(x,t))}{D}.
```
Extend it by zero for $`t`$ outside $`[a,b]`$. Define
```math
T_K(n)=\frac{1}{n^3}\left\{\sum_{a\lt p\lt b}(\log p)G(n^2,p)-
                           \frac{(n^2-a)(b-n^2)}2\right\}.
```
The sum uses ordinary primes only. Let $`V(x)=\sum_{m\le x}\Lambda(m)(x-m)-x^2/2`$, and let $`\ell`$ be the affine function interpolating $`V(a),V(b)`$. The chord of $`(x-m)_+`$ less its value at $`x`$ is exactly $`G(x,m)`$, including its zero value for exterior knots. The chord of $`x^2/2`$ less its value is $`(x-a)(b-x)/2=\int_a^bG(x,t)dt`$. Thus $`\ell(x)-V(x)`$ gives the numerator of $`T_K`$ with $`\Lambda(m)`$ in place of ordinary primes. [Integrated explicit formula and triangular prime weight, p. 2](https://arxiv.org/pdf/1503.05403)

Proper prime powers make a uniformly small difference. The square weights sum to at most $`\vartheta(K+H)-\vartheta(K)\ll H`$ by the prime number theorem with a classical error term. Powers of degree at least three contribute $`O(K^{2/3}\log K)`$ by Chebyshev's bound summed over the exponents. Since $`G\le D/4`$ and $`D\asymp K^2/L`$,
```math
\frac{\ell(n^2)-V(n^2)}{n^3}-T_K(n)
=O(L^{-2}+K^{-1/3}\log K).
\tag{1}
```

The classical explicit formula gives
```math
\frac{V(t^2)}{t^3}=-\sum_\rho\frac{t^{2\rho-1}}{\rho(\rho+1)}+O(1/t).
\tag{2}
```
Under RH, absolute convergence bounds this quantity, and bounds the normalized chord because the endpoint arguments are comparable to $`t`$. Hence $`T_K(n)=O(1)`$.

Suppose $`\Theta>1/2`$. Fix a zero $`\rho_0`$ with $`\beta_0>1/2`$ and fix $`1/2<\sigma<\beta_0`$. The filter in the earlier shrinking-interval proof isolates the exponent $`\lambda_0=2\rho_0-1`$ among all $`\lambda_\rho=2\rho-1`$ with $`\beta\ge\sigma`$. Here it must also annihilate the two real exponents $`-3,-1`$, since $`\ell(t^2)/t^3`$ is a linear combination of $`t^{-3}`$ and $`t^{-1}`$. To do this, take the earlier mass-one measure for the differences $`\lambda_\rho-\lambda_0`$ with support length at most $`h/4`$. For each $`\alpha\in\{-3,-1\}`$ convolve with
```math
\frac{r\delta_0-\delta_v}{r-1},\qquad
v=h/8,\quad r=\exp\big(v(\alpha-\lambda_0)\big).
```
Its mass is one, its transform vanishes at $`\alpha-\lambda_0`$ and its total variation is $`O_{\rho_0}(1/h)`$ for small $`h`$. Smooth by the uniform probability on $`[0,h/2]`$ and multiply the resulting density by $`\exp(-\lambda_0 v')`$ at the integration variable $`v'`$. The final density $`w`$ has support in $`[0,h]`$, transform one at $`\lambda_0`$, and zero at the other specified exponents. With $`h=\log((K+H)/K)\asymp1/L`$ it satisfies $`\|w\|_1\le B`$, $`\|w\|_\infty\ll B/h`$, where $`B=K^{o(1)}`$. Indeed Ingham gives $`N(\sigma,T)=O(T^p)`$ for a fixed $`p<1`$ and the earlier cost is $`\exp(O(h^{-p/(1-p)}))`$. The two extra factors cost $`O(h^{-2})`$. [Filter construction and sampling argument](SURVIVING-ZEROS.md)

Write $`Z_K(t)=(\ell(t^2)-V(t^2))/t^3`$. For the real interval $`K\le t\le K+H`$, $`Z_K`$ has Lipschitz constant $`O(1)`$ uniformly. In fact $`V'(x)=\psi(x)-x=O(K^2)`$ off knots, $`V(x)=O(K^4)`$, and the interpolating chord satisfies the same bounds on its slope and value. Thus replacing $`Z_K(Ke^{v'})`$ by $`T_K(\lfloor Ke^{v'}\rfloor)`$ costs $`O(1)`$ by (1). In the filter integral the target from (2) has absolute size $`m_0 K^{2\beta_0-1}/|\rho_0(\rho_0+1)|`$ with $`m_0`$ its multiplicity. The low zeros $`\beta<\sigma`$ cost $`O(BK^{2\sigma-1})`$ and the replacement and remainder cost $`O(B)`$. Each logarithmic cell has length at most $`1/K`$. The supremum bound for $`w`$, followed by Cauchy–Schwarz and $`N\asymp Kh`$, therefore gives
```math
\left(\frac1N\sum_{n\in J_K}T_K(n)^2\right)^{1/2}
\gg_{\rho_0,\sigma} K^{2\beta_0-1}/B .
```
Taking $`\beta_0`$ arbitrarily close to $`\Theta`$ gives the lower exponent on every sufficiently late block. Absolute convergence in (2), also at the endpoints of the chord, gives the upper bound $`O(K^{2\Theta-1})`$. Consequently the mean square of $`T_K`$ is $`K^{4\Theta-2+o(1)}`$ if $`\Theta>1/2`$. Together with the earlier result for $`F`$, a subpower bound for either observable on some unbounded sequence implies RH and bounds both observables on every late block. This is a logical equivalence of the assertions about unbounded sequences.

## Repeated primes and the remaining discrepancy

Write $`\mu=d\vartheta-dt`$ on $`[a,b]`$. After squaring $`\int G\,d\mu`$, the mass on the diagonal comes only from repeated primes. Its normalized average is
```math
\mathcal D_K=\frac1N\sum_{n\in J_K}\frac1{n^6}\sum_{a\lt p\lt b}(\log p)^2G(n^2,p)^2
  \sim \frac{8}{45}\frac{\log K}{L^3}.
\tag{3}
```
To compute it, use $`y=(n^2-a)/D`$, $`z=(p-a)/D`$, $`g(y,z)=\min(y,z)-yz`$. Then $`G=Dg`$. Uniformly for $`0\le y\le1`$, partial summation and the prime number theorem give
```math
\sum_{a\lt p\lt b}(\log p)^2g(y,(p-a)/D)^2
=D\log a\left(\int_0^1g(y,z)^2dz+o(1)\right).
```
The error is absolute inside the parentheses. The variation of $`g^2`$ is bounded uniformly, $`\log p/\log a=1+o(1)`$ throughout, and the normalized prime number theorem error $`O_A(a/(D\log^A a))`$ tends to zero. The integral is $`y^2(1-y)^2/3`$. Its mean over the samples tends to $`1/90`$ since $`y=(n-K)/H+O(1/L)`$ uniformly. Also $`n/K=1+O(1/L)`$ and $`D^3\log a/K^6\sim16\log K/L^3`$. This proves (3).

Let $`C_K=N^{-1}\sum_nT_K(n)^2-\mathcal D_K`$. Expanding the square, $`C_K`$ includes the unequal-prime sum, the negative twice-prime-times-integral term, and the square of the integral. Positivity gives $`C_K\ge-\mathcal D_K`$. A one-sided subpower upper bound for $`C_K`$ on unboundedly many blocks suffices. On RH, $`C_K=-\mathcal D_K+O(1)`$. If $`\Theta>1/2`$, $`C_K=K^{4\Theta-2+o(1)}`$ on every sufficiently late block.

Nearby distinct pairs can also be removed. The contribution integrated over $`0<|s-t|\le R`$ against $`d\mu(s)d\mu(t)`$ has absolute value after normalization at most $`O((R+1)\log K/L^3)`$. Indeed $`\vartheta(b)-\vartheta(a)+D\ll D`$, a radius-$`R`$ interval has $`\vartheta`$-mass plus length $`O((R+1)\log K)`$ inside the block, and $`G\le D/4`$. This bound includes the continuous centering terms over the same region. One may discard all separations up to $`\exp(\sqrt{\log K})`$ at subpower cost. Cancellation among larger separations remains unresolved.

## Cumulative counts between consecutive squares

For real $`t\in[a,b]`$ let $`u(t)=\pi(t)-\pi(a)-\int_a^t ds/\log s`$. Then $`u(n^2)=U_K(n)`$ and $`\log t\,du(t)=d\mu(t)`$. Integration by parts, using the zero endpoint values of $`G`$, gives exactly
```math
T_K(n)=-n^{-3}\int_a^b (u(t)-c)\big(\partial_tG(n^2,t)\log t+G(n^2,t)/t\big)\,dt
```
for every real constant $`c`$, because $`G(n^2,t)\log t`$ vanishes at both endpoints. The derivative of $`G`$ has modulus at most one, and continuity at the corner allows integration by parts there. On each gap $`[j^2,(j+1)^2]`$, $`|u(t)-u(j^2)|\ll K`$ simply by counting integers. All these gaps have lengths comparable to $`K`$. Integrating the absolute value over each gap and taking $`c=m_K`$ gives
```math
\max_{n\in J_K}|T_K(n)|\ll\frac{\log K}{K L}
       \left(K+\frac1N\sum_{j\in J_K}|U_K(j)-m_K|\right).
\tag{4}
```
If $`\Theta>1/2`$, the lower bound for $`T_K`$ forces the mean absolute deviation from the median to be at least $`K^{2\Theta-o(1)}`$. This also bounds the uncentered root mean square from below since the median minimizes absolute deviations and the mean absolute value is at most the root mean square. The ordinary truncated explicit formula gives $`\psi(x)-x=O_\epsilon(x^{\Theta+\epsilon})`$ and partial summation gives the same upper exponent for $`\pi(x)-\mathrm{li}(x)`$. This gives $`\max_j|U_K(j)|\le K^{2\Theta+o(1)}`$ and the matching upper exponents. Under RH the usual $`O(\sqrt{x}\log x)`$ bound for $`\pi(x)-\mathrm{li}(x)`$ bounds each $`U_K(j)`$ on the block. [Explicit formula](https://arxiv.org/abs/1401.4233) · [Prime-counting bounds under RH](https://www.sciencedirect.com/science/article/abs/pii/S0022314X26000090)

Put $`B_K=\#\{j\in J_K:|U_K(j)-m_K|>K(\log K)^2\}`$. In the off-line case the mean absolute deviation is at most $`K(\log K)^2+(B_K/N)K^{2\Theta+o(1)}`$. Its matching lower exponent therefore forces $`B_K=K^{1-o(1)}`$ on every sufficiently late block, in the sense that $`\log B_K/\log K\to1`$. Under RH the count is eventually zero. Thus showing $`B_K=O(K^{1-\eta})`$ for any fixed $`\eta>0`$ on some unbounded sequence would suffice. This test needs an upper bound on the number of exceptional cumulative counts and allows a free common offset on each block.

Equivalently, compute the median of $`E_j=\pi(j^2)-\mathrm{li}(j^2)`$ over the block and count the same deviations about that median. Subtracting $`E_K`$ from every observation gives exactly $`U_K(j)`$ and shifts the median by the same amount.

One can also replay the triangular sum from the ordinary counts $`c_j=\pi((j+1)^2)-\pi(j^2)`$. In $`T_K(n)`$ replace the weighted prime and continuous measures in each gap by a single mass $`2c_j\log j-(2j+1)`$ at $`j^2`$. This changes the normalized statistic by $`O(1/L)`$ uniformly. Moving the mass by $`O(K)`$ costs $`O(KD/n^3)`$ by the Lipschitz bound for $`G`$ and the prime number theorem. Replacing each $`\log p`$ by $`2\log j`$ costs a further $`O(D^2/(K^4\log K))`$, since $`|\log p-2\log j|\le2/K`$ and the number of primes in the whole block is $`O(D/\log K)`$.

Bazzanella established unconditional control on exceptions to the expected count in individual gaps between consecutive squares. Applying a relative error estimate to each gap loses the sign correlations that enter $`U_K`$. For example, in a hypothetical sequence with a same-sign error of size $`K^\delta/\log K`$ in each gap, with $`0<\delta<1`$, that error would be a vanishing fraction of the expected count and would accumulate to order $`K^{1+\delta}/(L\log K)`$ across the block. [Bazzanella, *Primes between consecutive squares*](https://iris.polito.it/bitstream/11583/1397858/2/Primes-between-squares.pdf)

## An upper bound for the actual cumulative discrepancy

The separate seven-eighths theorem and zero density give, on every sufficiently late block,
```math
\max_{j\in J_K}|U_K(j)|\ll \frac{K^{7/4}}{L^{3/4}\log K},
\qquad \max_{n\in J_K}|T_K(n)|\ll\frac{K^{3/4}}{L^{7/4}}.
```
To see this, subtract the truncated explicit formulas for $`\psi`$ at $`a+1/2`$ and $`\lfloor t\rfloor+1/2`$ for $`a\le t\le b`$, taking the same cutoff $`T=a/2`$. The errors cost $`O(\log^2 K)`$ and the change of the main term from rounding costs $`O(1)`$. For each zero $`\rho`$ the difference of the two power terms divided by $`\rho`$ is
```math
\ll K^{2\beta}\min\{(1+|\gamma|)^{-1},L^{-1}\}.
```
Use the triangle inequality for the first bound and integrate $`y^{\rho-1}`$ for the second. For $`\beta\ge87/100`$ Huxley's density exponent is at most $`39/161<1/4`$, so the count through $`Y`$ is $`O(Y^{1/4})`$. Splitting at $`Y=L`$ and summing dyadically above $`L`$ bounds the sum of the minimum by $`O(L^{-3/4})`$ for these zeros. Their factor $`K^{2\beta}`$ is at most $`K^{7/4}`$. The remaining zeros contribute $`O(K^{174/100}\log^2 K)`$ by the ordinary zero count. Removing the proper prime powers costs $`O(K\log K)`$ or less. This gives
```math
\sup_{a\le t\le b}|\vartheta(t)-\vartheta(a)-(t-a)|\ll K^{7/4}L^{-3/4}.
```
Stieltjes partial summation with $`1/\log t`$ gives the stated bound for $`U_K`$. Integrating the derivative of $`G`$ against the same cumulative discrepancy costs at most $`D/n^3`$ times the supremum, which gives the bound for $`T_K`$. The resulting mean-square bound for $`T_K`$ is $`O(K^{3/2}/L^{7/2})`$. These are positive-power estimates for the two normalized tests. [Dudek, Theorem 2.1](https://arxiv.org/abs/1401.4233) · [Huxley](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0015/PPN356556735_0015.pdf) · [Density exponent (1.3)](https://arxiv.org/pdf/2405.20552) · [Seven-eighths theorem](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)

## Priority and verification

Triangular weights for prime counts, the integrated explicit formula, Landau oscillation, and zero-density isolation all have precedents. Stechkin and Popov study localized mean prime-counting errors and sparse zeros. Brent, Platt and Trudgian study the continuous dyadic mean square of the uncentered prime number theorem error. Bazzanella treats the individual square gaps. A search of these works and of the literature on Selberg integrals, square samples and local means did not identify the exact cumulative count criterion or the $`8/45`$ normalization above. Priority for these specializations is unconfirmed. [Stechkin and Popov](https://www.mathnet.ru/eng/rm1018) · [Brent, Platt and Trudgian](https://arxiv.org/abs/2008.06140) · [Dudek, Grenié and Molteni](https://arxiv.org/pdf/1503.05403) · [Bazzanella](https://doi.org/10.1007/s000130050469)

The nine Lean lemmas check finite algebra, the variance decomposition, the threshold count, the constant and the gap between neighbouring endpoints. Interval computations compare five actual prime blocks against direct sums, include proper prime powers, expand the unequal-prime sum explicitly at one sample, and test the passage to unweighted counts at two precisions. The Mellin, density, and asymptotic arguments have written proofs. [Lean lemmas](ShortArithmetic.lean) · [Arithmetic replay](check_short_arithmetic.py) · [Verification record](CHECKS.txt)
