# Exact positive averages near each cutoff

Use $Q,a,H,I_b,z_\rho$ and $A_b$ from the [signed-prefix companion](CUTOFFS.md). Fix $\xi>0$. On every sufficiently late square block and each grid with $g\le Q^{1-\xi}$, prescribe all inner progressions. Every grid point $b$ belongs to an interval, inside $[Q/\log Q,Q]$, whose upper-to-lower endpoint ratio is

$$
F_Q=e^8 H^{1/20}(\log(2H))^{3/20}.
$$

There are strictly positive probabilities $\lambda_{b,c}$ on **all** grid points $c$ of this interval, including $b$, for which

$$
\sum_c\lambda_{b,c}\frac{1}{|I_c|}\sum_{n\in I_c}n^{z_\rho}=0
\quad\text{for every retained }\rho,\qquad \sum_c\lambda_{b,c}A_c=0 .
$$

One set of outer weights works for all retained zeros in each interval. The inner arithmetic means keep their original equal weights. The interval can be centered at $b$ in log coordinates whenever it fits. Otherwise take $[b,bF_Q]$ or $[b/F_Q,b]$ pointing into the tested range. One of these fits eventually because $F_Q^2<\log Q$. Uniform control of the individual value $A_b$ remains open.

## A continuous reference measure

Put $Y=\log Q$, $L=4$ and $T=(\log H+3\log\log(2H))/40$. The chosen log interval has length $2(L+T)$ and midpoint $y$. Let $\kappa$ be the classical positive xi probability, scaled by $1/20$ so its transform is
$\int e^{zv}d\kappa(v)=\xi(1/2+z/20)/\xi(1/2)$. It vanishes at every $z_\rho$. The theta series bounds its density by $O(\exp(90|v|-\pi e^{40|v|}))$ outside a fixed compact interval. [Romik, equations (1.8)–(1.11)](https://danromik.com/resources/papers/riemannxi-acta-online-first.pdf#page=3)

Let $P(x)$ be any real conjugate-paired linear combination of $e^{z_\rho x}$. There are $M=O(H\log(2H))$ distinct modes by the total zero count. Scale the [binomial taper](CUTOFFS.md#a-taper-for-measuring-the-width-of-an-excursion) to radius $L$ around $y$, with $N$ a sufficiently large constant times $(1+H)\log(2H)$. Average its translates by $d\kappa(v)$ restricted to $|v|\le T$, obtaining $W$. Then $0\le W\le1$, $W$ is supported inside the chosen log interval, and it is bounded below on $|x-y|\le1/2$ by the positive $\kappa$-mass on $|v|\le1/2$ times $1/2$. Write $Z=\int W|P|$. The taper inequality gives
$\int|(WP)'|\ll H\log(2H)Z$.

To control relative errors, let $M_0=\sup_{|u|\le1/4}|P(y+u)|$. The unit-scale complex interpolation bound in the taper proof gives $M_0\le e^{C(M+H+1)}Z$, by bounding the derivative near a maximum. For every real $v$,
$$
|P(y+v)|\le e^{10\max(v,0)}[C(1+|v|)]^M M_0. \tag{1}
$$
For $M\ge1$ put $k=\lceil8M(1+|v|)\rceil$ and $s=v/k$. Interpolate $w^k$ on the nodes $e^{z_\rho s}$. The divided difference of order $j$ has size at most $\binom{k}{j}R^{k-j}$ for $R=\max(1,\max_\rho|e^{z_\rho s}|)$, by the complete homogeneous polynomial formula. Each Newton product has coefficient norm at most $(2R)^j$. Apply this interpolant to the shift of $P$ at $y$, where $|js|\le1/4$ for $j<M$. Summing the bounds and using $R^k\le e^{10\max(v,0)}$ gives (1). Repeated nodes can be combined and the zero space is immediate.

For $\log a-1\le x\le Y+1$, the forward displacement from $y$ is $O(H)$, the backward displacement is $O(\log Q)$, and all mode real parts are nonnegative. Applying (1) and the unit-scale disk estimate at each new center bounds $|P|+|P'|+|P''|$ by $K_Q Z$, with $K_Q=\exp(CH^2\log(2H))=Q^{o(1)}$. For the signed integral $\int WP$, the full xi integral is zero, term by term. On the omitted tail, (1) with the taper radius fixed and the bound on $M_0$ are dominated by the double exponential in the density. Indeed $e^{40T}=H(\log(2H))^3$ dominates $M\log(2+T)+O(M+H+T)$ at the start of the tail. Thus $|\int WP|\ll\exp(-cH(\log(2H))^3)Z$.

## Arithmetic sampling and positive correction

Set $F=P+P'$. The sample $B_c=|I_c|^{-1}\sum_{n\in I_c}F(\log n)$ is within $Q^{-1/2+o(1)}Z$ of $P(\log c)$, uniformly in the interval and all inner choices. In fact $d[tP(\log t)]/dt=F(\log t)$. Replacing $h_c\sum_{I_c}F(\log n)$ by $\int_a^cF(\log t)\,dt$ costs $O(h_c(1+\log Q)K_QZ)$ by the derivative bound and the two partial cells. Dividing by $h_c|I_c|=c-a+O(h_c)$ and using $a,h_c\le\sqrt Q$, $c\ge Q/\log Q$, proves the claim.

Give $\log c$ the cell between adjacent log midpoints, with the two end cells bounded by the ends of the chosen interval. Its length is $\ell_c$, and the maximum length is $O(g\log Q/Q)$. Put $p_c=\ell_c(W(\log c)+Q^{-1})>0$. For $WP$ and $|WP|$, the Riemann-sum error is at most the largest cell length times $\int|(WP)'|$. The floor term is at most $O(\log F_Q)Q^{-1}K_Q Z$. It follows that
$$
\left|\sum_c p_c B_c\right|\le\eta_Q Z,\qquad
\left|\sum_c p_c|B_c|-Z\right|\le\eta_Q Z
$$
with $\eta_Q=o(1)$ uniformly in $b$ and $P$ for every fixed $\xi>0$.

On the real space of sample vectors, $v\mapsto\sum p_cv_c$ therefore has norm at most $\eta_Q/(1-\eta_Q)$ under $\|v\|=\sum p_c|v_c|$. Extend it to all real vectors without increasing the norm. The coordinate coefficients $d_c$ of this extension satisfy $|d_c|\le p_c\eta_Q/(1-\eta_Q)$. Hence $p_c-d_c>0$ on every node eventually, and these weights annihilate the sample subspace. Normalize to total mass one. Since $1+z_\rho\ne0$, the real and imaginary components of every arithmetic mode are among the samples of $F=P+P'$. This proves simultaneous cancellation. [Lean weight correction and probability normalization](lean/BalancedCutoffs.lean) · [Exact rational example](check_cutoffs.py)
