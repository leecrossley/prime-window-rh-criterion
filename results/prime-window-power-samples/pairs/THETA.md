# Long runs of negative unequal-pair sums

Lee Crossley · 21 November 2026

Use the [dyadic tent, centered prime sum and ordered unequal pairs](FINITE.md). Write $I=3-4\log2$ and

$$
\ell(B)=(\log B)^{3/5}(\log\log B)^{-1/5}.
$$

**Theorem.** For every sufficiently large real $B$, the interval $[B,4B\sqrt{\log B}]$ contains at least $\lfloor\exp(\ell(B)/5)\rfloor$ consecutive integer bases $j$ on which

$$
c_j=-(I+o(1))\log(j^2).
$$

The error tends to zero uniformly along the selected run. In particular every sufficiently late square block $[K,K^2]$ contains a run of this length with $B=K$. The proof uses the classical theta transformation, divisor convolution and an unconditional error bound in the prime number theorem.

## A theta average that can be evaluated arithmetically

Let $F(t)=\sum_{k\ge1}e^{-\pi k^2t^2}$ and put

$$
g(t)=e^{-\pi t^2}-3e^{-4\pi t^2}+2e^{-16\pi t^2},\qquad
G(t)=F(t)-3F(2t)+2F(4t)=\sum_{k\ge1}g(kt).
$$

The theta transformation gives $G(t)=(2t)^{-1}G(1/(4t))$. Splitting off the even indices also gives $`G(t)=\sum_{k\ {\rm odd},\,k>0}(e^{-\pi k^2t^2}-2e^{-4\pi k^2t^2})`$. For $t\ge1/2$ each summand is positive. Reciprocity gives positivity for smaller $t$. The function and its derivatives decrease faster than any power at both ends, with the corresponding change of variable at zero.

For a weight $U$, set $S_U(x)=\sum_{m\ge1}(\Lambda(m)-1)U(m/x)$. Because $\sum_{m\mid h}\Lambda(m)=\log h$ and $\sum_{m\mid h}1=\tau(h)$, absolute convergence at each fixed $x>0$ gives the exact identity

$$
S_G(x)=\sum_{h\ge1}(\log h-\tau(h))g(h/x). \tag{1}
$$

Write $`\widehat f(s)=\int_0^\infty f(t)t^{s-1}\,dt`$ and $P(s)=(1-2^{-s})(1-2^{1-s})$. Then $\widehat g(s)=\tfrac12\pi^{-s/2}\Gamma(s/2)P(s)$ for $\Re s>0$. Mellin inversion of (1) on $\Re s=2$ has integrand $x^s\widehat g(s)(-\zeta'(s)-\zeta(s)^2)$. At $s=1$ the double poles cancel, and $P$ cancels the remaining simple pole. At $s=0$ the zero of $P$ removes the gamma pole. Move to $\Re s=-5$, crossing the simple gamma poles at $-2$ and $-4$. Polynomial growth of $\zeta,\zeta'$ on bounded vertical strips and exponential decay of $\Gamma$ justify the contour shift. The residue coefficient at $-2$ is $21\pi\zeta'(-2)=-21\zeta(3)/(4\pi)$, by the functional equation. Thus

$$
S_G(x)=-\frac{21\zeta(3)}{4\pi}x^{-2}+O(x^{-4}). \tag{2}
$$

There is a second way to see the cancellation used below. Poisson summation for the even Schwartz function $g$ gives $\sum_{h\ge1}g(h/x)=O_A(x^{-A})$ for every $A>0$, since $g(0)=\int_0^\infty g=0$. For $g(t)\log t$ the second derivative is integrable at zero, and $G$ is smooth and flat there. The composite trapezoidal bound therefore approximates both lattice sums by $x$ times their integrals with error $O(x^{-1})$. Their integrals agree because $\widehat G(s)=\zeta(s)\widehat g(s)$ for $\Re s>1$ and $\widehat G(1)=\widehat g'(1)$. Applying these observations to $\sum_h(\log h)g(h/x)-\sum_m G(m/x)$ proves $S_G(x)=O(x^{-1})$ without the residue calculation.

Direct integration of the compact tent gives $\widehat W(s)=P(s)/(s(s-1))$. With $\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$ the Mellin identity becomes

$$
\widehat G(s)=\widehat W(s)\xi(s).
$$

Use the classical even function

$$
\Phi(u)=\sum_{k\ge1}\bigl(2\pi^2 k^4e^{9u}-3\pi k^2e^{5u}\bigr)e^{-\pi k^2e^{4u}}.
$$

Its terms are positive for $u\ge0$. Rodgers and Tao record the classical representation $`\xi(1/2+iz/2)/8=\int_0^\infty\Phi(u)\cos(zu)\,du`$ and the evenness of $\Phi$. Let $`k(v)=\Phi(v/2)/\int_{\mathbb R}\Phi(w/2)\,dw`$. This is a positive probability density with bilateral transform $`\int_{\mathbb R}e^{(s-1/2)v}k(v)\,dv=\xi(s)/\xi(1/2)`$. For $|v|$ large, $e^{|v|/2}k(v)\ll\exp(-2e^{2|v|})$, by the displayed series and evenness. Mellin uniqueness now gives $`\int k(v)e^{-v/2}W(t e^{-v})\,dv=G(t)/\xi(1/2)`$. [Rodgers and Tao, equations (1)–(3)](https://arxiv.org/pdf/1801.05914)

In particular, with $f(y)=S_W(y)/\sqrt y$,

$$
\int_{\mathbb R} k(v) f(Xe^v)\thinspace{}dv
   =\frac{S_G(X)}{\xi(1/2)\sqrt X}=O(X^{-5/2}). \tag{3}
$$

Chebyshev's bound gives $\sum_m|b_m|W(m/y)\ll y$ for $y\ge1$, and the sum vanishes for $0<y<1$. This justifies termwise integration in (3). It also bounds the tail of (3) on $|v|>r$ by $O(\sqrt X\exp(-2e^{2r}))$ for large $r$.

## From an average to consecutive square samples

Take $r=\tfrac12\log(2\log X)$. The omitted tail is $O(X^{-7/2})$, while the mass on $[-r,r]$ tends to one. The weighted mean of $f(Xe^v)$ over this closed interval is consequently $O(X^{-5/2})$. The function is real and continuous. It attains this mean somewhere, so for some $y$,

$$
\frac{X}{\sqrt{2\log X}}\le y\le X\sqrt{2\log X},
\qquad |S_W(y)|/\sqrt y\ll X^{-5/2}. \tag{4}
$$

Choose $X=4B^2\sqrt{\log B}$. The lower and upper endpoints for $y$ in (4) are respectively $(2+o(1))B^2$ and $(8+o(1))B^2\log B$. The square root of this entire interval lies inside $[B,4B\sqrt{\log B}]$ with room at each end.

Away from its knots the derivative of $S_W(t)$ is

$$
S_W'(t)=\sum_{t/2<m<t}\frac{b_m}{m}
  -\tfrac12\sum_{t/4<m<t/2}\frac{b_m}{m}.
$$

Since $\sum_{m\le u}b_m=\psi(u)-\lfloor u\rfloor$, partial summation on these two intervals and Johnston–Yang's estimate with exponential coefficient $0.1853$ give $|S_W'(t)|\ll \exp(-0.17\ell(t))$ for large $t$. The loss in the coefficient absorbs the logarithmic factor and the fixed change of scale. Continuity and piecewise linearity allow integration through the knots. [Johnston and Yang, Theorem 1.4](https://arxiv.org/pdf/2204.01980)

Set $m=\lceil\sqrt y\rceil$ and $J=\lfloor e^{\ell(B)/5}\rfloor$. For $m\le j\le m+J$, $j^2-y=O(\sqrt y(J+1))$, since $J=B^{o(1)}$. Throughout these displacements $\ell(t)/\ell(B)\to2^{3/5}$ uniformly. As $0.17\cdot2^{3/5}>1/5$, integration from (4) gives $\max_{m\le j\le m+J}|S_W(j^2)|/j=o(1)$, and $m+J\le4B\sqrt{\log B}$. Finally $\sum_{m\le x}b_m^2\sim x\log x$ by the prime number theorem and partial summation on primes. Higher powers contribute $O(\sqrt x\log^3x)$ and the linear centering terms are $O(x)$. Weighted partial summation gives $A(x)/(x\log x)\to I$. This proves the theorem for the genuine unequal-pair statistic.

## What the averaging leaves on a whole block

Write $C_K(U)$ for the ordered unequal-pair sum with weight $U$ in both variables. For fixed smooth rapidly decreasing weights at both ends, and their sums with $W$, the same prime number theorem argument gives

$$
\sum_{K\le n\le K^2}\frac1{n^2}\sum_m b_m^2 U(m/n^2)^2
  =(4\Vert{}U\Vert{}_2^2+o(1))K^2\log K.
$$

Here $`\|U\|_2^2=\int_0^\infty U(t)^2\,dt`$. First integrate on a fixed compact interval, then bound both tails by dyadic summation with $`\sum_{m\le t}b_m^2\ll t\log(2t)`$. The factor four comes from $\sum_{K\le n\le K^2}\log(n^2)\sim4K^2\log K$. In particular (2) gives $`C_K(G)\sim-4\|G\|_2^2K^2\log K`$ on every sufficiently late whole block for the theta weight.

Let $V(t)=\sum_{j=1}^d a_jG(r_jt)$ for any fixed real coefficients and fixed positive dilations. Then $S_V(x)=O_V(x^{-2})$ by (2). Put $E=W-V$. Since $S_W(x)=O(x)$, the difference between the two block sums of $S_W(n^2)^2/n^2$ and $S_E(n^2)^2/n^2$ is $O_V(\sum_{n\ge K}n^{-4})$. Consequently

$$
C_K(W)=C_K(E)-4\bigl(I-\Vert{}E\Vert{}_2^2\bigr)K^2\log K+o_V(K^2\log K). \tag{5}
$$

For an explicit example use

$$
V(t)=-\tfrac{19}{16}G(4t/5)+\tfrac{37}{8}G(t)-\tfrac{95}{64}G(5t/4).
$$

An interval integral gives $`\|W-V\|_2^2/I<0.00410`$. The certificate sums upper bounds on cells of width $1/4096$ over $[1/16,4]$, and uses reciprocity and Gaussian tails elsewhere. Equation (5) therefore accounts for more than $`99.59\%`$ of the leading diagonal, while $S_E$ still contains the original centered sum up to $O_V(x^{-2})$. [Interval integral and arithmetic cross-check](check_theta.py)

In fact these dilations span a dense subspace of $L^2((0,\infty),dt)$. Under the unitary map $h(t)\mapsto e^{u/2}h(e^u)$ their span becomes the span of translates. The Fourier transform of the image of $G$ is $\widehat G(1/2+it)$ up to the choice of sign for $t$. This nonzero entire function has only isolated zeros. A function orthogonal to every translate must vanish, since the product of its Fourier transform and the conjugate transform of the image of $G$ is in $L^1$ and has identically zero inverse transform. This proves the density assertion. Thus any fixed fraction below one is possible in (5).

For each nontrivial zero $\rho=\beta+i\gamma$ and each of these finite $V$, however, $\widehat V(\rho)=0$ whereas $\widehat W(\rho)\ne0$. In particular $`\int_0^\infty|E(t)|t^{\beta-1}\,dt\ge|\widehat W(\rho)|>0`$. Small squared norm of the residual weight therefore leaves an explicit obstruction at each zero. A bound for the residual block energy $\sum S_E(n^2)^2/n^2$ is still required. The mean in (3) selects negative runs of $c_n$ but gives no upper bound for that energy over $[K,K^2]$.

For example, put $f_\rho(y)=y^{\beta-1/2}\cos(\gamma\log y)$. The left side of (3) for this test function is identically zero, by the transform of $k$. If $\beta>1/2$, its squared values on the bases $K^2/2\le n\le K^2$ sum to $\gg_\rho K^{8\beta-2}$. To see this, write $N=K^2$, $n=Nu$. After division by $N^{4\beta-1}$ the sum is a Riemann sum for $`\int_{1/2}^1u^{4\beta-2}\cos^2(2\gamma\log u+\phi)\,du`$, where $\phi=2\gamma\log N$. The integral has a positive minimum over phases since $\gamma\ne0$, and the Riemann sums converge uniformly in $\phi$ by a uniform derivative bound. This example identifies the information the theta average loses even with exact knowledge of that average at every real scale.