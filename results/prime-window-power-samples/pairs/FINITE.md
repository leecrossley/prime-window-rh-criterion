# Negative unequal-pair sums on square blocks through K = 1.2 trillion

Lee Crossley · 21 November 2026

Let $\Lambda$ be the von Mangoldt function, $b_m=\Lambda(m)-1$, and let $W$ be the compact dyadic tent

$$
W(t)=\begin{cases}
2-1/(2t)&1/4\le t\le1/2,\\
1/t-1&1/2\lt t\le1,\\
0&\text{otherwise}.
\end{cases}
$$

Write $S(x)=\sum_{m\ge1}b_mW(m/x)$, $A(x)=\sum_{m\ge1}b_m^2W(m/x)^2$. The normalized sum over ordered unequal pairs and the full square block are

$$
c_n=\frac{1}{n^2}\sum_{m\ne j}b_mb_jW(m/n^2)W(j/n^2)
    =\frac{S(n^2)^2-A(n^2)}{n^2},\qquad
C_K=\sum_{n=K}^{K^2}c_n .
$$

**Theorem.** For every integer $`2\le K\le1\,200\,000\,000\,000`$, every $c_n$ on $[K,K^2]$ is strictly negative. In particular $C_K<0$. More generally, let $H\ge H_0=3\cdot10^{12}$ and suppose that all nontrivial zeta zeros of positive ordinate at most $H$ lie on the critical line. For $n\ge2$ the same strict inequality holds whenever $4096 n^2/\log(n^2)\le H^4$. Platt and Trudgian proved the height hypothesis for $H_0$. [Finite zero verification](https://arxiv.org/abs/2004.09765)

## The smoothed estimate

Set $d=1/1000$, $L=\log x$, $I=\int W^2=3-4\log2$ and $D(x)=x(\log2)/2-\sum_m\Lambda(m)W(m/x)$. Comparing each lattice cell with its integral costs at most the total variation, so $|S(x)+D(x)|\le2$. Use the previously constructed positive random dilation $U$, for which $\mathbb EU=1$, $e^{-2d}\le U\le e^d$, $\nu=\mathrm{Var}(U)<12.1/H^2$ and $|\mathbb EU^{\beta+i\gamma}|<6.1/H^2$ for $0\le\beta\le1$, $|\gamma|\ge H$. [Dilation, mass identity and explicit formula](https://github.com/leecrossley/prime-window-power-samples/blob/e4de5134777c660f14a6013ab192d41812d1eab2/finite/QUARTIC.md)

Put $T_0=(\log H_0+1)/(\pi H_0)$ and $B_2=\log3-(\gamma_E+\log(4\pi))/3$. For all $x\ge32^2$, with $r=4e^{2d}/x$,

$$
\frac{|\mathbb E D(xU)|}{\sqrt x}
\le \frac3{\sqrt2}(B_2+4T_0)
   +73.2T_0\frac{\sqrt x}{H^2}
   +\frac{r^2}{3\sqrt x(1-r^2)}. \tag{1}
$$

Indeed the low zero coefficients $C(\rho)$ are positive on the critical line, have total mass at most $B_2+4T_0$ there up to height $H$, and $|\mathbb EU^\rho|\le1$ at those zeros. Above $H$, $|C(\rho)|\le2/\gamma^2$, the positive ordinates have reciprocal-square sum at most $T_0$, and the explicit formula counts both signs. These absolute bounds work on both sides. In the normalization at $y/4$, the trivial-zero coefficients are $(2^{-2j}-1)(2^{-2j}-2)/(2j(2j+1))\le1/3$. At $y=xU$ their sum is bounded by a geometric series. [Coefficient normalization](https://github.com/leecrossley/prime-window-power-samples/blob/e4de5134777c660f14a6013ab192d41812d1eab2/PROOF.md)

The tent, its explicit formula and the exact value of $B_2$ are due to bramble_trace. [Fixed-tent formula and mass identity](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=24)

## Moving back to the original tent

As a function of $x$, $`m W(m/x)=(x-m)_+-(3/2)(x-2m)_++(1/2)(x-4m)_+`$. Each mean hinge increment $`\mathbb E(xU-a)_+-(x-a)_+`$ is nonnegative by convexity. For $`h=x(U-1)`$ subtract $`h\mathbf1_{x>a}`$ from the displacement at fixed $h$ before averaging. The remainder is bounded by the integral from $0$ to $|h|$ of the indicator that $a$ is between $x$ and $x+\mathrm{sgn}(h)t$, endpoints included. For the hinge at $km$ this requires $1/m\le ke^{2d}/x$. At time $t$, eligible integers occupy an interval of length $t/k$. Both groups of coefficients, the positive one at $k=1,4$ and the absolute negative one at $k=2$, have $\sum|a_k|=3/2$ and $\sum k|a_k|=3$. Thus bounding either side costs the same.

First allow every integer at weight at most $L+d$. There are at most $t/k+1$ crossings. Integrating in $t$ and using $\mathbb E h^2=x^2\nu$, $\mathbb E|h|\le x\sqrt\nu$ proves

$$
\frac{|D(x)-\mathbb ED(xU)|}{\sqrt x}
\le e^{2d}(L+d)\left(\frac34\sqrt x\thinspace{}\nu+3\sqrt\nu\right). \tag{2}
$$

For $x\ge10^{42}$ use the following sharper bound. For ordinary primes pad the crossing interval to a left-open interval of length $Y=t/k+x^{2/3}+1$, starting one unit to the left. Brun–Titchmarsh for modulus one bounds the mass by $2Y(L+d)/\log Y\le3.001Y$ since $\log Y\ge2L/3$. Higher powers can be treated before taking the expectation. The Lipschitz bound for $W(m/x)$ as a function of $x$ is $1/m$. A term that can change has $xe^{-2d}/4\le m\le xe^d$, and $`\sum_{p^j\le z,\,j\ge2}\log p\le \sqrt z(\log z)^2/\log2`$. Together these give

$$
\begin{split}
\frac{|D(x)-\mathbb ED(xU)|}{\sqrt x}
&\le 3.001e^{2d}\left(\frac34\sqrt x\thinspace{}\nu+
                3(x^{1/6}+x^{-1/2})\sqrt\nu\right)\\
&\quad+\frac{4e^{5d/2}(L+d)^2}{\log2}\sqrt\nu .
\end{split}\tag{3}
$$

The linear centering term cancels in both (2) and (3). [Montgomery and Vaughan, Theorem 2](https://doi.org/10.1112/S0025579300004708)

## The diagonal and the certified bounds

The even integers have $b_m=-1$ except at powers of two. Comparing the even lattice with the integral of $W^2$ costs at most two. There are at most three powers of two on $[x/4,x]$, each with $W^2\le1$. Hence $A(x)/x\ge I/2-5/x$.

For $x\ge10^{42}$ retain only ordinary primes. On the support, $(\log p-1)^2\ge (L-\log4-2)\log p$. Integration by parts against $\vartheta(t)-t$, using total variation two for $W^2$ and Dusart's bound $|\vartheta(t)-t|\le0.2t/\log^2t$ for $`t>3\,594\,641`$, gives

$$
\frac{A(x)}{xL}\ge
\left(1-\frac{\log4+2}{L}\right)
\left(I-\frac{0.4}{(L-\log4)^2}\right). \tag{4}
$$

Both factors are positive and increasing on this range. [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442)

For $32^2\le x\le10^{42}$ evaluate (1) and (2) with $H=H_0$, the upper endpoint for all increasing terms and the lower endpoint for the geometric series and $2/\sqrt x$. For larger $x$ with $4096x/L\le H^4$, use $\sqrt x/H^2\le\sqrt L/64$ and $x^{1/6}/H\le x^{-1/12}L^{1/4}/8$. Both $x^{-1/12}L^{1/4}$ and $x^{-1/4}L^{1/4}(L+d)^2$ decrease from $10^{42}$ onward. This controls every term in (3).

| Range | Upper bound for centered sum | Lower bound for diagonal |
| --- | --- | --- |
| $32^2\le x\le10^{42}$ | $\lvert S(x)\rvert/\sqrt x<0.293$ | $A(x)/x>0.108$ |
| $10^{42}\le x,\ 4096x/L\le H^4$ | $\lvert S(x)\rvert/\sqrt{xL}<0.441$ | $A(x)/(xL)>0.219$ |

The first row gives $S^2<A$. In the second row the weaker cutoffs $0.45$ and $0.21$ already give $(S^2-A)/x<-(3/400)\log x$. For $2\le n<32$, interval arithmetic on the exact prime powers gives $c_n<0$ in every case. Finally $x/\log x$ is increasing for $x\ge4$. At $`K_*=1\,200\,000\,000\,000`$, $`4096K_*^4/(\log(K_*^4)H_0^4)<0.943`$. All $`x=n^2\le K_*^4`$ are covered.

The certificate replays the endpoint and interval estimates at either 160 or 256 bits. Direct ordered-pair enumeration also checks the diagonal subtraction at $2\le n\le8$. [Interval certificate](check_pairs.py)

## Where a failure would put a zero

If $c_n\ge0$ at $x=n^2$, some zero $\rho=\beta+i\gamma$ satisfies both

$$
H_0<\gamma\le8(x/\log x)^{1/4},\qquad
(\beta-1/2)\log(x/2)>20+\tfrac12\log\log x .
$$

Indeed a failure requires $x>10^{42}$ and $H=8(x/L)^{1/4}>H_0$. Apply the dilation at this $H$ without assuming any zero verification above $H_0$. Use (1) for the low zeros through $H_0$ and the tail above $H$. If every intermediate zero fails the second strict inequality, the absolute contribution of both signs of its ordinate, summed over this intermediate range and divided by $\sqrt{xL}$, is at most $(12/\sqrt2)T_0e^{20}<0.0131$. Here $|\mathbb E U^\rho|\le\mathbb E U^\beta\le1$ by concavity. Adding this to the previous $0.441$ bound still leaves its square below $0.219$. Equation (4) then forces $c_n<0$.
