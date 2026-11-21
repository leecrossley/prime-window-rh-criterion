# A finite-height bound for a prime sum on every real scale through 10⁴⁵

Let $w_x(t)$ be zero outside $[x/4,x]$, equal to $2-x/(2t)$ on $[x/4,x/2]$ and equal to $x/t-1$ on $[x/2,x]$. Write

$$
P(x)=\sum_p(\log p)w_x(p),\qquad M(x)=\tfrac12 x\log 2-P(x).
$$

**Theorem.** Let $H\ge H_0=3\cdot10^{12}$. If every nontrivial zeta zero of positive ordinate at most $H$ lies on the critical line, then

$$
M(x)>0.012\sqrt x \qquad (10^{30}\le x\le H^4/81000).
$$

Platt and Trudgian proved the height hypothesis at $H_0$. The upper endpoint there is exactly $10^{45}$. The previously established strict sign below $10^{30}$ gives $M(x)>0$ for every real $0<x\le10^{45}$. In particular every square sample on $K\le n\le K^2$ passes whenever $K^4\le10^{45}$. The earlier certificate by bramble_trace uses the normalization $M(x)=3D_{\rm p}(x/2)$. [Platt and Trudgian, Theorem 1](https://arxiv.org/abs/2004.09765) · [Earlier finite certificate, revision 38](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=38) · [Discussion](https://rstation.ai/r/riemann_hypothesis/posts/100#comment-61fubEt16h1nsGVD)

**A bound on the ordinate of a witness.** If an actual prime sum has $M(x)\le0.012\sqrt x$ at any $x\ge10^{45}$, some nontrivial zero with real part greater than $1/2$ has positive ordinate at most $(81000x)^{1/4}<17x^{1/4}$. Apply the theorem with $H=(81000x)^{1/4}$ and use reflection and conjugation. The fixed-height result gives a finite range. The existence of whole passing blocks for arbitrarily large integer $K$ still requires a separate argument.

For a failure of the sign itself there is a stronger conclusion. If $M(x)\le0$, a zero $\beta+i\gamma$ satisfies **both**

$$
3\cdot10^{12}<\gamma\le(81000x)^{1/4},\qquad
\beta>\tfrac12+\frac{20}{\log(x/2)}.
$$

## A positive dilation with a small transform above the verified height

Write $d=1/1000$, $b=H/4$, and $\mathrm{sinc}(t)=\sin(t)/t$, with value one at zero. Give $W$ the probability density

$$
f(v)=\frac{3b}{2\pi}\mathrm{sinc}^4(bv).
$$

Its characteristic function and its first derivative vanish for $|\gamma|\ge H$. Indeed $\mathrm{sinc}(bv)$ is the characteristic function of the uniform distribution on $[-b,b]$. The sum of four such uniforms has a continuous density supported on $[-4b,4b]$. Fourier inversion gives the asserted support for the transform of $f$. The finite first absolute moment makes the derivative continuous through the endpoints.

For the normalization, the sum of two uniforms on $[-1,1]$ has triangular density $\max(2-|t|,0)/4$. Its squared integral is $1/3$. Convolving with the reflected density and evaluating at zero gives $\int_{\mathbb R}\mathrm{sinc}^4(t)\thinspace dt=2\pi/3$. Also $\sin^4 t=[4(1-\cos 2t)-(1-\cos4t)]/8$. The identity $\int_{\mathbb R}(1-\cos at)t^{-2}\thinspace dt=\pi |a|$ therefore gives $\int_{\mathbb R}t^2\mathrm{sinc}^4(t)\thinspace dt=\pi/2$. Hence $\mathbb EW^2=12/H^2$.

Let $V$ have the law of $W$ conditioned on $|W|\le d$. Put $A=\mathbb E e^V$ and $U=e^V/A$. Symmetry gives $1\le A\le e^d$, so $\mathbb E U=1$ and $e^{-2d}\le U\le e^d$. From $f(v)\le3/(2\pi b^3v^4)$, the omitted probability and first absolute moment are bounded, respectively, by

$$
r=\frac{64}{\pi H^3d^3},\qquad r_1=\frac{96}{\pi H^3d^2}.
$$

For $|\gamma|\ge H$ the integrals of $e^{i\gamma v}$ and $v e^{i\gamma v}$ against the full density vanish. On $|v|\le d$ and $0\le\beta\le1$ the difference between $e^{\beta v}$ and $1+\beta v$ is bounded by $e^dv^2/2$. Restoring the two omitted tails and using $|A^{-\beta-i\gamma}|\le1$ gives

$$
|\mathbb EU^{\beta+i\gamma}|
\le\frac{r+r_1+6e^d/H^2}{1-r}<\frac{6.1}{H^2}.
$$

The variance $v_0$ of $U$ is at most $\mathbb E(e^V-1)^2\le e^{2d}\mathbb EV^2$, hence $v_0<12.1/H^2$. After multiplication by $H^2$ the right-hand majorants for both estimates decrease with $H$. Checking them at $H_0$ suffices.

## Finding the loss at the middle corner

Use $s_+=\max(s,0)$. At a prime $p$ the weight as a function of the scale is

$$
w_x(p)=\frac{\max(x-p,0)}{p}-\frac{3\max(x-2p,0)}{2p}+\frac{\max(x-4p,0)}{2p}.
$$

The convexity gap $\mathbb E\max(xU-a,0)-\max(x-a,0)$ is nonnegative. Only $a=2p$ can raise $P(x)$ above its smoothed value. For a displacement $h=x(U-1)$ subtract $h\mathbf1_{x>a}$ from the hinge increment. Its expectation is unchanged, since $\mathbb E h=0$. The resulting nonnegative quantity is bounded by the integral, from $0$ to $|h|$, of the indicator that $a$ lies between $x$ and $x+\mathrm{sgn}(h)t$, endpoints included. This follows by integrating the two constant slopes on either side of $a$ and also covers $a=x$.

At any crossing of $2p$, one has $1/p\le 2e^{2d}/x$ and $p\le xe^d/2<x$. The primes encountered by time $t$ occupy a closed interval of length $t/2$. Enlarge it to a left-open interval beginning one unit below its lower endpoint, of length $Y=t/2+x^{2/3}+1$. The lower endpoint is positive here, and $\log Y\ge(2/3)\log x$. The modulus-one Brun–Titchmarsh inequality bounds the sum of $\log p$ over the original interval by $2Y\log x/\log Y\le3Y$. Integrate first in $t$, then take the expectation. Using $\mathbb E|U-1|\le\sqrt{v_0}$ gives

$$
\frac{P(x)-\mathbb E P(xU)}{\sqrt x}
\le 9e^{2d}
\left(\frac{\sqrt x}{4}v_0+(x^{1/6}+x^{-1/2})\sqrt{v_0}\right).
\tag{1}
$$

The factor $1/4$ comes from $\int_0^{|h|}(t/2)\thinspace dt=h^2/4$. All prime sums here are finite by compact support. [Montgomery and Vaughan, *The large sieve*, Theorem 2](https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/S0025579300004708)

## Averaging the prime-power explicit formula

Let $D(y)=y\log(2)/2-\sum_n\Lambda(n)w_y(n)$. In the normalization centered at $y/2$, define

$$
C(s)=\frac{(2^s-1)(2^{1-s}-1)}{3s(1-s)},\qquad
B_2=\log3-\frac{\gamma_E+\log(4\pi)}3 .
$$

The tent explicit formula gives $D(y)=3\sum_\rho C(\rho)(y/2)^\rho$ plus a nonnegative trivial-zero sum for $y>4$. The sum runs over both signs of the ordinate with multiplicity. In the strip $|C(\beta+i\gamma)|\le2/\gamma^2$, since for $1\le z=2^\beta\le2$ one has $(z+1)(1+2/z)\le6$. The zero sum converges absolutely and uniformly on each compact interval of positive scales. At $\beta=1/2$, $C(\rho)=|2^\rho-1|^2/(3|\rho|^2)>0$. The unconditional identity $\sum_\rho C(\rho)=B_2$ evaluates the available low-zero mass. The earlier fixed-tent proof derives it at ramp cutoffs one and two. In the alternative normalization at $y/4$, the trivial terms have numerator $(2^{-2j}-1)(2^{-2j}-2)>0$ and denominator $(-2j)(-2j-1)>0$. [Fixed-tent formula and mass identity](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24) · [Explicit formula in the upper-endpoint normalization](https://github.com/leecrossley/prime-window-power-samples/blob/9af696c425c8dfff85416b2a27ff92a2af248d0b/PROOF.md)

Write $S(H)=(\log H+1)/(\pi H)$. The published zero count gives $N(t)\le t\log(t/(2\pi e))/(2\pi)+0.43\log t\le t\log t/(2\pi)$ for $t\ge H_0$. Partial summation, discarding the nonpositive lower boundary, yields $\sum_{\gamma>H}\gamma^{-2}\le S(H)$ for positive ordinates. Thus the verified low coefficients sum to at most $B_2+4S(H)$. For these zeros $|\mathbb EU^\rho|\le\mathbb E\sqrt U\le1$. For the remaining zeros use the transform bound, conjugation, and $(x/2)^\beta\le x$. This proves

$$
\frac{\mathbb E D(xU)}{\sqrt x}\ge
-\frac3{\sqrt2}(B_2+4S(H))-12\sqrt x\thinspace S(H)\frac{6.1}{H^2}.
\tag{2}
$$

The zero count and the transform estimate above use no assertion about the real parts of zeros beyond $H$. [Chourasiya and Simonič, equation (11)](https://arxiv.org/pdf/2507.15184v2#page=5)

## Ordinary primes and the uniform constants

The prime squares contribute $Q_2(y)=\int w_y(t^2)\thinspace d\vartheta(t)$ to $M(y)-D(y)$, and the higher powers contribute nonnegatively. Put $R=\sqrt y$. Direct integration on $[R/2,R/\sqrt2]$ and $[R/\sqrt2,R]$ gives $\int w_y(t^2)\thinspace dt=(3\sqrt2-4)R$. The weight vanishes at the endpoints and has total variation two. On this support Dusart gives $|\vartheta(t)-t|\le0.2R/\log^2(R/2)$ as soon as $R/2>3594641$. Integration by parts bounds the error in the square sum by twice that quantity. Consequently for $x\ge X_0=10^{30}$,

$$
\frac{\mathbb E Q_2(xU)}{\sqrt x}
\ge e^{-d}\left(3\sqrt2-4-
\frac{0.4}{\log^2(e^{-d}\sqrt{X_0}/2)}\right).
\tag{3}
$$

Here $\sqrt{xU}\ge e^{-d}\sqrt{x}$ and the quantity in parentheses is positive. [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442)

Since $\mathbb EU=1$, one has $M(x)=\mathbb EM(xU)-(P(x)-\mathbb E P(xU))$. Combine (1)–(3), put $C_0=81000$, and use

$$
\frac{\sqrt x}{H^2}\le\frac1{\sqrt{C_0}},\qquad
\frac{x^{1/6}+x^{-1/2}}H\le\frac{1}{H_0^{1/3}C_0^{1/6}}+\frac1{H_0},
\qquad S(H)\le S(H_0).
$$

| Quantity after division by $\sqrt x$ | Outward bound |
| --- | ---: |
| Contribution from squares | $>0.2420493$ |
| Loss from verified zeros | $<0.1326511$ |
| Loss above $H$ | $<0.000000000001$ |
| Loss at doubled primes | $<0.0961811$ |
| Remaining margin | $>0.0132171$ |

The margin proves the stated strict bound. The certificate checks all rounding inequalities at 160 or 256 bits using Arb. [Interval-arithmetic certificate](check_quartic.py)

## How far off the line a failure would reach

Suppose $M(x)\le0$. The finite result forces $x>10^{45}$. Set $H=(81000x)^{1/4}$. Use the same dilation, but split the zeros at **both** $H_0$ and $H$. The low-zero bound through $H_0$ and the high-zero bound above $H$ still give exactly the uniform losses in the table. For the middle range, $|\mathbb E U^\rho|\le\mathbb E U^\beta\le1$ by concavity. Pair conjugates and use $|C(\rho)|\le2/\gamma^2$. The extra possible loss after normalization is at most $(12/\sqrt2)W(x)$, where the sum counts positive ordinates with multiplicity and

$$
W(x)=\sum_{H_0<\gamma\le H}\frac{(x/2)^{\beta-1/2}}{\gamma^2}.
$$

A failure thus requires $W(x)>0.00155$. If every middle zero satisfied $(\beta-1/2)\log(x/2)\le20$, this extra loss would be at most $(12/\sqrt2)S(H_0)e^{20}<0.0130$. The unspent margin exceeds $0.0132171$. This contradiction proves the joint bound on height and real part. The earlier fixed-tent analysis also related hypothetical failure to weighted zeros in a fixed box. Here the top of the box scales as the fourth root of the failing input. [Earlier fixed-box calculation](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=38)

## What the finite hypothesis buys

The power four comes from the variance cost $\sqrt x\thinspace\mathrm{Var}(U)$ and a dilation with variance of order $H^{-2}$. There is a limit to reducing this particular cost. For any real random variable $V$ of finite variance, if $|\mathbb E e^{iHV}|\le\delta<1$, then $\mathrm{Var}(V)\ge 2(1-\delta)/H^2$. Indeed center $V$ and apply $1-\cos t\le t^2/2$. This observation concerns the smoothing argument. A different estimate for cancellation in the prime sum could have a different range.

The underlying square criterion, the exact value of $B_2$, and a finite proof through centered scale $10^{35}$ are due to bramble_trace. That endpoint is $2\cdot10^{35}$ in the upper-endpoint variable used here. Büthe previously transferred a finite zero verification to explicit estimates for unsmoothed prime-counting functions. Cáceres treated a two-sided bound through $2.15\cdot10^{29}$ for a logarithmically weighted von Mangoldt sum. The contribution advanced here is the explicit quartic transfer for this compact tent and the resulting ordinate bound for a failure. A search of these sources and the literature on finite-height smoothing located no earlier statement of either bound for this weight. [Earlier tent and certificates, revision 38](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=38) · [Büthe](https://doi.org/10.1090/MCOM/3060) · [Cáceres](https://hexagonmath.org/pdf/2610.00661v2)

## Reproduction

Run the following in the directory containing this note. The first program uses only the Python standard library. It bounds Euler's constant by harmonic sums, brackets logarithms and $\pi$ with rational series, checks the Fourier kernel using the four-uniform density, and verifies the hinge identities at exact rational inputs. The second program encloses the constants with Arb. The mathematical argument above supplies the uniform analytic estimates.

~~~sh
python3 check_quartic_exact.py
python3 -m venv /tmp/quartic-venv
/tmp/quartic-venv/bin/python -m pip install python-flint==0.9.0
/tmp/quartic-venv/bin/python check_quartic.py --bits 160
/tmp/quartic-venv/bin/python check_quartic.py --bits 256
~~~

Lean 4.33.1 checks the hinge representation, its exact displacement, nonnegativity after a finite mean-zero average, and the reduction to the middle corner. The Fourier analysis, sieve estimate and explicit-formula argument are written proofs. From the pinned Mathlib checkout with its cache installed, run the shell script under its Lake environment. [Lean source](QuarticCorners.lean) · [Replay command](replay_corners.sh) · [Verification transcript](CHECKS.txt)

~~~sh
lake env sh /absolute/path/to/finite/replay_corners.sh
~~~
