# How short a block can detect an off-line zero?

Lee Crossley · 21 November 2026

Let $c_n=(S(n^2)^2-A(n^2))/n^2$ be the [ordered unequal-pair sum for the original dyadic tent](FINITE.md). Put $I=3-4\log2$ and $\Theta=\sup_\rho\Re\rho$ over nontrivial zeta zeros. For real $B>e$ write

$$
T(B)=\sum_{B\le n\le 4B\sqrt{\log B}} c_n .
$$

**Theorem.** Under RH, $T(B)\sim-8I B(\log B)^{3/2}$. If $\Theta>1/2$, then $T(B)>0$ for every sufficiently large $B$ and $\log T(B)/\log B\to4\Theta-1$. Thus $T(B)\le0$ on an unbounded sequence of integer bases is equivalent to RH. The proof also gives real zeros of $S(y)$ and long runs of negative $c_n$ inside every sufficiently late interval of these bases, independently of the location of the zeta zeros. The theorem changes the window in the criterion. It leaves the arithmetic proof of its nonpositive sign open.

## Isolating a single zero

Use the functions $f(y)=S(y)/\sqrt y$, $k$, $g$, $G$ of the [theta argument](THETA.md). In particular, $k$ is a positive probability density, its bilateral transform at $z$ is $\xi(1/2+z)/\xi(1/2)$, and its average of $f(Xe^v)$ is $S_G(X)/(\xi(1/2)\sqrt X)$. The latter is $O(X^{-5/2})$ as $X\to\infty$.

Fix a nontrivial zero $\rho=\beta+i\gamma$ with $\beta\ge1/2$, allowing arbitrary multiplicity $m$. Write $z_0=\rho-1/2$ and define the absolutely convergent kernel

$$
h(v)=\frac{e^{-z_0v}}{(m-1)!}\int_v^\infty
       (w-v)^{m-1} e^{z_0w} k(w)\thinspace{}dw.
$$

The moments $`\int w^j e^{z_0w}k(w)\,dw`$ vanish for $0\le j<m$ by the order of the zero of $\xi$. On the negative half-line this lets us replace the last integral by minus the integral from $-\infty$ to $v$ with the same integrand. There is a constant $D_\rho>0$ with $|h(v)|\le D_\rho k(v)$ on the whole real axis. Indeed, for $v\to+\infty$ the first term in the theta series gives $k(v)\asymp e^{9v/2}e^{-\pi e^{2v}}$, so uniformly for $t\ge0$,

$$
\frac{k(v+t)}{k(v)}
 \ll \exp\negthinspace{}\big((9/2-2\pi e^{2v})t\big).
$$

This bounds the tail integral defining $h/k$ even with the polynomial factor. At the negative end use the other integral and evenness of $k$. On a compact interval use continuity and strict positivity of $k$.

Let $N(s)=\widehat g(s)(-\zeta'(s)-\zeta(s)^2)$. The divisor identity gives

$$
N(s)=\int_0^\infty S_G(t)t^{-s-1}\thinspace{}dt \qquad(\Re s>-2).
$$

First unfold for $\Re s>1$. At zero $S_G(t)$ decays faster than every power, and at infinity it is $O(t^{-2})$. The removable singularities and continuation in this half-plane follow from the theta argument. At $\rho$, $N$ has a zero of order exactly $m-1$ (order zero means a nonzero value). Indeed $\widehat g(\rho)\ne0$ and $-\zeta'$ has order $m-1$ there, whereas $-\zeta^2$ has order $2m$. In particular

$$
R_\rho=\frac{N^{(m-1)}(\rho)}{(m-1)!\thinspace{}\xi(1/2)}
  =-\frac{m\thinspace{}\widehat g(\rho)}{\xi(1/2)}\thinspace{}\frac{\zeta^{(m)}(\rho)}{m!}\ne0 .
$$

Fubini's theorem in the definition of $h$, followed by $t=Xe^{-(w-v)}$, gives the exact evaluation

$$
\int h(v) f(Xe^v)\thinspace{}dv=
\frac{X^{z_0}}{\xi(1/2)(m-1)!}\int_0^X S_G(t)t^{-\rho-1}
                  \big(\log(X/t)\big)^{m-1}\thinspace{}dt . \tag{1}
$$

For the interchange, $|f(y)|\ll\sqrt y$, and the integral in $w-v\ge0$ is dominated by a polynomial times $e^{(\beta-1)(w-v)}$. Extend the last integral to infinity. On $t\ge X$, the bound $S_G(t)=O(t^{-2})$ costs $O_\rho(X^{-5/2})$ after normalization. Expanding the logarithmic power in the full integral leaves just $N^{(m-1)}(\rho)$, as all its lower derivatives vanish. Hence (1) is

$$
R_\rho X^{\rho-1/2}+O_\rho(X^{-5/2}). \tag{2}
$$

The same coefficient is the residue of $N(s)/(\xi(1/2)(s-\rho)^m)$ at $\rho$. This second calculation follows by taking the bilateral transform of $h$, which divides the transform of $k$ by $(z-z_0)^m$.

## Both signs on real scales

Take $r=\tfrac12\log(2\log X)$. The absolute error in truncating either the $k$- or $h$-integral to $[-r,r]$ is $O_\rho(X^{-7/2})$, by $|h|\le D_\rho k$, the double-exponential tails and $|f(y)|\ll\sqrt y$. Choose a unit complex scalar $\lambda$ rotating $R_\rho X^{i\gamma}$ to the positive real axis. The two real densities $k\pm\Re(\lambda h)/(2D_\rho)$ lie between $k/2$ and $3k/2$. Their integrals against $f$ on the truncated interval have opposite signs and absolute values $\gg_\rho X^{\beta-1/2}$ by (2). Their masses are at most $3/2$. Thus the continuous function $f$ takes a value at least $c_\rho X^{\beta-1/2}$ and one at most $-c_\rho X^{\beta-1/2}$ on

$$
[X/\sqrt{2\log X},\thinspace{}X\sqrt{2\log X}]. \tag{3}
$$

There is a real $y$ there with $S(y)=0$. A single known critical-line zero suffices for this last conclusion. Starting at this exact zero also proves the consecutive negative-run theorem using the derivative estimate already given. [Finite zero verification](https://arxiv.org/abs/2004.09765) · [Rounding and run length](THETA.md)

## The discrete square sum

Suppose $\beta>1/2$. Set $X=4B^2\sqrt{\log B}$. For $|v|\le r$ let $j(v)=\lfloor\sqrt{Xe^v}\rfloor$. For large $B$ its range lies in $[B,4B\sqrt{\log B}]$, by the endpoints of (3). Uniformly on these cells,

$$
f(Xe^v)=f(j(v)^2)+O(1).
$$

Indeed $S(y)=O(y)$ and $S'(y)=O(1)$ off the knots, from Chebyshev and the two finite derivative sums. Thus $f'(y)=O(y^{-1/2})$, and any one cell has length $2j+1$ in $y$. The weight of a cell under $`k(v)\,dv`$ is at most $`2\|k\|_\infty/j\ll1/B`$ since its length in $v$ is at most $2\log(1+1/j)$. The restriction of $k$ to these cells has total mass at most one.

Apply $|h|\le D_\rho k$ and Cauchy–Schwarz to (2), after truncation and rounding. This gives

$$
X^{\beta-1/2}\ll_\rho 1+
\left(\frac1B\sum_{B\le j\le4B\sqrt{\log B}} f(j^2)^2\right)^{1/2}.
$$

Because $\beta>1/2$, this proves a lower bound $\gg_\rho B X^{2\beta-1}$ for the squared sum on **every** sufficiently late short block. By the prime number theorem the total diagonal on this block is asymptotic to $8IB(\log B)^{3/2}$. It is lower order. Therefore $T(B)>0$ and $\liminf\log T(B)/\log B\ge4\beta-1$. Take the supremum over the zeros. The absolutely convergent [tent explicit formula](https://github.com/leecrossley/prime-window-power-samples/blob/e4de5134777c660f14a6013ab192d41812d1eab2/PROOF.md) gives $S(y)=O(y^\Theta)$, hence $\limsup\log T(B)/\log B\le4\Theta-1$. Under RH the same formula gives $f(y)=O(1)$, the squared sum is $O(B\sqrt{\log B})$, and the diagonal gives the displayed negative asymptotic.

For the original block $[K,K^2]$, take $B=K^2/(8\sqrt{\log K})$. The short block then fits inside it when $K$ is large. Its lower bound is $K^{8\beta-2+o(1)}$ for the sum of squares alone. The entire original diagonal has size $O(K^2\log K)$. This supplies an independent derivation of the obstruction to the original sign. Negative runs can coexist with a dominant positive sum of squares when an off-line zero is present.

The distinction between averaging a sum and averaging its square can also be tested exactly. For $a=\beta-1/2$ put $f_\rho(y)=y^a\cos(\gamma\log y)$ and $`M(z)=\int e^{zv}k(v)\,dv`$. Its $k$-average is zero. Its squared $k$-average is at least $X^{2a}(M(2a)-|M(2a+2i\gamma)|)/2$. The parenthesis is strictly positive by the strict triangle inequality, since $k$ is positive on every interval and $\gamma\ne0$. Thus a positive scale average can eliminate the first moment of this oscillation at every center while its square retains a growing contribution if $a>0$.