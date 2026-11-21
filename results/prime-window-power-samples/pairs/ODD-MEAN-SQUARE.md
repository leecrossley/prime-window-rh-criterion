# The odd-shift mean square on short blocks of squares

Lee Crossley · 21 November 2026

Let $K\ge2$ be an integer, $M=\lfloor4K\sqrt{\log K}\rfloor$, $P=M+1$ and $N=P-K$. Set $b_m=\Lambda(m)-1$, where $\Lambda(p^j)=\log p$ for primes $p$ and integers $j\ge1$, and $\Lambda$ is zero elsewhere. Use the continuous tent $W(t)=2-1/(2t)$ on $[1/4,1/2]$, $W(t)=1/t-1$ on $(1/2,1]$, and zero elsewhere. Write $L=\log2$, $\mu=\int W=L/2$, $I=\int W^2=3-4L$, and

$$
S(x)=\sum_m b_mW(m/x),\quad A(x)=\sum_m b_m^2W(m/x)^2,\quad
E_K=\sum_{n=K}^M S(n^2)^2/n^2,\quad D_K=\sum_{n=K}^M A(n^2)/n^2.
$$

**Finite theorem.** Every complete block of square samples satisfies $E_K<8D_K/9$ for $2\le K\le4\cdot10^{24}$. On $5\cdot10^{22}\le K\le4\cdot10^{24}$ the raw odd-shift mean square in (1) below is less than $2.502$, $E_K/N<20.83$ and $D_K/N>23.914$. This is a bound on the sum over all bases in each block. Its zero-location inputs are the finite verification through $3\cdot10^{12}$ and the separate zero-free half-plane $\Re s>7/8$. [Platt and Trudgian](https://arxiv.org/abs/2004.09765) · [Seven-eighths theorem](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)

Expanding the square gives the contribution from ordered unequal pairs as $E_K-D_K$. The theorem puts that contribution strictly below $-D_K/9$ on each complete block. Proving its sign by this route for arbitrarily large $K$ remains open. [Short-block criterion](SHORT-BLOCKS.md)

## Recovering the prime sum from odd shifts

The Hardy–Littlewood singular series vanishes at an odd displacement. Its centered value is $-1$. With $W_m=W(m/x)$, define the ordered odd-shift discrepancy and its raw centered mean square by

$$
R_o(x)=\frac{2}{x}\sum_{\substack{h\ge1\\h\ {\rm odd}}}\sum_{m\ge1}
(b_mb_{m+h}+1)W_mW_{m+h},\qquad
V_K=\frac1N\sum_{n=K}^M\frac{(R_o(n^2)-L^2)^2}{n^2}. \tag{1}
$$

Let $T_e,T_o$ be the sums of $W_m$ on even and odd integers. For $x\ge4$ the weights on even prime powers add to one, since the two adjacent powers of two have weights $1/t-1$ and $2-1/t$ for $1/2<t\le1$. Hence the even centered sum is $u=L-T_e$. Each odd displacement joins opposite parities. Factoring the two ordered products gives $xR_o/2=u(S-u)+T_eT_o$. [The odd-gap prime-power observation in Chou, Haag, Huryn and Ledoan](https://arxiv.org/abs/2308.14888)

For completeness write $T_e=\mu x/2+e$, $T_o=\mu x/2+o$. The trapezoid rule on either parity lattice gives $|e|,|o|\le6/x$. Its error on mesh $d$ for the integral is at most $d^2\operatorname{Var}(W')/8$, by integration against the cell kernel $(t-a)(b-t)/2$. Here $d=2/x$ and $\operatorname{Var}(W')=24$. Expanding the factored product gives

$$
|R_o+(\mu-2L/x)S-L^2|
\le 12|S|/x^2+(2L^2+12\mu)/x+24L/x^2+144/x^3 \le55/x
$$

for $x\ge4$. Indeed $|S|\le3x$, since $\sum W_m\le x$ and $\psi(x)\le4Lx<3x$ by summing $\psi(2j)-\psi(j)\le\log\binom{2j}{j}\le2jL$ at powers of two. For $t^2\ge8$ put

$$
Q(t)=\frac{R_o(t^2)-L^2}{\mu(1-4/t^2)t},\qquad F(t)=-S(t^2)/t.
$$

Thus $|Q(t)-F(t)|\le330/t^3$, because $\mu(1-4/t^2)\ge\mu/2>1/6$. Also $V_K\le\mu^2 N^{-1}\sum Q(n)^2$ for $K\ge3$.

## A positive integral for the square

The tent explicit formula gives, for $t\ge4$,

$$
F(t)=\sum_\rho d_\rho t^{2\rho-1}+O(3/t),\qquad
d_\rho=\frac{(1-2^{-\rho})(2^{1-\rho}-1)}{\rho(1-\rho)}. \tag{2}
$$

Here the error has absolute value at most $3/t$. The lattice error is at most $2/t$ by variation and the trivial-zero sum is at most $r^2/(3t(1-r^2))$ with $r=4/t^2$. The nontrivial zeros are counted with multiplicity and both signs. The coefficients are absolutely summable. [Tent explicit formula, mass identity and trivial terms](../finite/QUARTIC.md)

Consider a group of zeros $a\le\beta\le b$ with $a\ge1/2$. For $\lambda=7/5$, the nonnegative weight $(1-t/(\lambda P))_+/(1-1/\lambda)$ is at least one on $[K,P]$. Set $B=\lambda P$ and $v_\rho=d_\rho B^{2\rho-1}$. Integrating the squared sum against that weight, dividing by $N$, gives

$$
\frac PN\frac{\lambda^2}{\lambda-1}
\sum_{\rho,\rho'}\frac{v_\rho\overline{v_{\rho'}}}{(1+z)(2+z)},\qquad
z=2\beta+2\beta'-2+2i(\gamma-\gamma'). \tag{3}
$$

Indeed $\int_0^1 y^z(1-y)\,dy=1/((1+z)(2+z))$. Compact integration and absolute convergence justify passage from finite groups to the infinite sum. The absolute value of each kernel entry is at most $1/((4a-1)^2+4(\gamma-\gamma')^2)$. For a symmetric nonnegative matrix $w$, the inequality $2|v_i v_j|\le |v_i|^2+|v_j|^2$ bounds its quadratic form by $\sum_i |v_i|^2\sum_j w_{ij}$.

For $D=2-\beta'$, $\kappa=4a-1$ and $y=\gamma-\gamma'$, the row entry satisfies

$$
\frac1{\kappa^2+4y^2}\le c\,\frac{D}{D^2+y^2}
\quad\text{if }D\le c\kappa^2,\quad 1\le4cD.
$$

Every real-part summand on the right is positive. Summing over all nontrivial zeros gives the real part of $\xi'/\xi(2+i\gamma)$ by the paired Hadamard product of $\xi$ about $1/2$. For $|\gamma|\ge H_0=3\cdot10^{12}$,

$$
2\Re(\xi'/\xi)(2+i\gamma)\le\log|\gamma|+8. \tag{4}
$$

In the completed zeta logarithmic derivative the two rational poles contribute at most $3$ after doubling. The Dirichlet series contributes at most $2\sum_{m\ge2}\log(m)/m^2<2.2$ by integral comparison. The real part of the digamma function at $1+iv$, $v=\gamma/2$, is $-\gamma_{\rm E}+\sum_{j\ge1}v^2/[j(j^2+v^2)]$. Split at $\lceil |v|\rceil$. The first sum is at most $1+\log|\gamma|$, and the rest is at most $v^2/(2\lceil|v|\rceil^2)\le1/2$. Dropping $-\log\pi$ gives (4). [Digamma series, equation 5.7.6](https://dlmf.nist.gov/5.7#E6) · [Product and logarithmic derivative of the completed zeta function](https://people.math.harvard.edu/~elkies/M259.06/zeta2.pdf)

## Bounding the high ordinates numerically

On a strip $a<\beta\le b$ write $|d_\rho|\le d/\gamma^2$. The two strips used for the finite theorem have the following bounds. The coefficient bound follows from $(1+2^{-a})(1+2^{1-a})$, and the two inequalities for $c$ above hold throughout each strip.

| $a$ | $b$ | $d$ | $c$ |
| ---: | ---: | ---: | ---: |
| $1/2$ | $4/5$ | $4.2$ | $3/2$ |
| $4/5$ | $7/8$ | $3.4$ | $1/4$ |

By (3)–(4) the strip's normalized continuous mean square above $H_0$ is at most

$$
2\frac PN\frac{\lambda^2}{\lambda-1}\,d^2\frac c2
\sum_{\substack{\gamma> H_0\\a<\beta\le b}}
B^{4\beta-2}\frac{\log\gamma+8}{\gamma^4}. \tag{5}
$$

The factor two restores the negative ordinates. The row bound in (4) already allows interactions between both signs.

Write $w(T)=(\log T+8)/T^4$. For $N(s,T)$ counting positive ordinates at most $T$ with $\beta\ge s$, each upper bound by a sum of terms $A T^p(\log T)^q$ gives a bound for $\sum_{\gamma>H_0,\,\beta\ge s}w(\gamma)$ by the corresponding sum of

$$
J(A,p,q)=\frac{4(\ell+8) A H_0^{p-4}\ell^q}
                   {4-p-(q+1)/\ell},\qquad\ell=\log H_0.
$$

This follows by partial summation, dropping the nonpositive lower boundary, using $-w'(T)\le4(\log T+8)/T^5$ and bounding $(\log T)/\ell$ and $(\log T+8)/(\ell+8)$ by $(T/H_0)^{1/\ell}$. The denominators used here are positive. The bound for the number of all positive ordinates is $N(T)\le T\log T/(2\pi)$. For $5/8\le s\le7/8$, Chourasiya and Simonič also give the three terms with $(A,p,q)$ equal to

$$
\left(21.77,\frac{3(1-s)}{2-s},\frac{7-5s}{2-s}\right),\quad
(8.290,0,2),\quad (147.0,0,1).
$$

Both estimates apply for every $T\ge H_0$. [Chourasiya and Simonič, Corollary 1 and equation (11)](https://arxiv.org/pdf/2507.15184)

Let $U(s)$ be the smaller available bound. On a grid $a=s_0<\cdots<s_J=b$, the sum in (5) is at most

$$
B^{4a-2}U(a)+\sum_{j=0}^{J-1}
       (B^{4s_{j+1}-2}-B^{4s_j-2})U(s_j).
$$

Each zero in a cell is therefore charged at its upper real-part endpoint. This construction includes zeros on the boundaries. Every coefficient is nonnegative and increasing in $B\ge1$, so the largest endpoint suffices for all smaller blocks in the stated range.

## Finite endpoint and passage back to squares

Put $K_0=5\cdot10^{22}$ and $K_*=4\cdot10^{24}$. For $K_0\le K\le K_*$ use $P/N\le28/27<1.05$ and $B\le(7/5)(4K_*\sqrt{\log K_*}+1)$. For the low zeros through $H_0$, let $T_0=(\log H_0+1)/(\pi H_0)$ and $B_2=\log3-(\gamma_{\rm E}+\log(4\pi))/3$. The verified critical-line coefficients give a uniform absolute bound $3(B_2+4T_0)/\sqrt2$. The remaining zeros with $\beta\le1/2$ contribute at most $12T_0$ since $\sum_{\gamma>H_0}\gamma^{-2}\le T_0$ and $t^{2\beta-1}\le1$ on $[K,P]$. [Zero mass and reciprocal-square bound](../finite/QUARTIC.md#averaging-the-prime-power-explicit-formula)

To interpolate only the full prime sum, put $V=K_0^2/4$. On $y\ge V$, $|\psi(y)-\lfloor y\rfloor|\le \delta y$ with

$$
\delta=0.2/\log^2 V+(\log V)^2/(\sqrt V\log2)+1/V.
$$

Use Dusart's bound for $\vartheta$, count higher powers by $\sqrt y(\log y)^2/\log2$, and note all normalized majorants decrease here. Partial summation gives $|S(x)|\le2\delta x$ for $x\ge K_0^2$. Off the knots $S'(x)$ is the sum of $b_m/m$ over $(x/2,x)$ minus half the sum over $(x/4,x/2)$. Each interval sum has absolute value at most $(2+\log2)\delta$. Therefore $|F'(t)|\le[3(2+\log2)+2]\delta$ through integration on smooth pieces. This bounds the error between $F(n)$ and $F(t)$ on every $[n,n+1]$. [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442)

Take the $L^2$ norm with measure $dt/N$ on $[K,P]$, replacing $Q(n)$ by its constant value on each such cell. Minkowski's inequality bounds the sampled root mean square by the sum of the two square roots in (5), the low-zero and left-half bounds, the lattice and trivial error $3/K_0$, the rounding error above, and $330/K_0^3$. The coarser interval-arithmetic run gives the following outward bounds.

| Quantity | Bound |
| --- | ---: |
| Terms outside the two strips | $<0.132841$ |
| RMS from $1/2<\beta\le4/5$ | $<0.022458$ |
| RMS from $4/5<\beta\le7/8$ | $<4.408539$ |
| Sampled RMS of $Q$ | $<4.563837$ |
| Raw odd-shift mean square $V_K$ | $<2.502$ |
| Mean prime energy $E_K/N$ | $<20.829$ |

For the last row add $330/K_0^3$ once more and square. The diagonal estimate from the finite pair proof gives $A(n^2)/n^2>0.219\log(n^2)$ on this range. The mean of $\log n$ on $K,\ldots,M$ exceeds $\log M-1$ by integration, and $M\ge28K$. Thus $D_K/N>2(0.219)(\log(28K_0)-1)>23.914$. This proves the strict $8/9$ comparison. For $2\le K\le K_0$ the largest scale $x\le16K_0^2\log K_0$ satisfies $4096x/\log x\le H_0^4$ throughout the relevant range $x\ge4$. The earlier pointwise bounds give ratios at most $0.293^2/0.108$ or $0.441^2/0.219$ for $n\ge32$. Both are below $8/9$. Direct prime-power sums cover $2\le n<32$. [Pointwise certificate and diagonal bound](FINITE.md)

## Prior work and verification

The compact tent and its weighted prime formula are due to bramble_trace. Büthe obtained explicit bounds on prime counts from finite verification of zeta zeros. Brent, Platt and Trudgian bound the mean square of the ordinary prime-counting error on a continuous dyadic interval by studying pairs of zeta zeros. The present argument applies a triangular integral to the square of the smoothed error and then passes to the integer square samples. Chourasiya and Simonič supply the explicit density constants. I found no earlier statement of this finite endpoint with the $8/9$ margin for this statistic in the work checked. [Original tent](https://rstation.ai/r/riemann_hypothesis/posts/100#comment-61fubEt16h1nsGVD) · [Büthe](https://arxiv.org/abs/1410.7015) · [Brent, Platt and Trudgian](https://arxiv.org/abs/2008.06140) · [Chourasiya and Simonič](https://arxiv.org/abs/2507.15184)

The analytic argument is a written proof. Arb encloses the endpoint constants at two precisions and checks the small bases directly. The comparison at $K=24$ tests the odd-shift formula against the first 64 conjugate pairs of zeros. Two Lean lemmas verify the finite row bound and the comparison of kernels used in (3)–(5). The reproduction record gives the pinned environment, outputs and source hashes. [Interval certificate](check_odd_mean_square.py) · [Lean lemmas](OddMeanSquare.lean) · [Reproduction record](ODD-MEAN-CHECKS.txt)

With Python and python-flint 0.9.0 installed, run from this directory

~~~sh
python3 -B check_odd_mean_square.py --bits 160 --mesh 4000
python3 -B check_odd_mean_square.py --bits 256 --mesh 8000
~~~
