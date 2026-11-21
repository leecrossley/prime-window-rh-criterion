# Signed prefixes on a regular grid of tenth-power roots

Write $`Q=a^2`$, $`H=\log\log Q`$, with $`a`$ a positive integer. A base $`n`$ gives the root $`n^{10}`$ and the tent argument $`n^{20}`$. The cutoffs $`b`$ are ordinary integers in $`[Q/\log Q,Q]`$. At each $`b`$ choose a step $`1\le h_b\le a`$ and a residue $`0\le r_b\lt h_b`$, and form the nonempty set $`I_b=\{a\le n\le b:n\equiv r_b\bmod h_b\}`$. The inner progression may change at every cutoff.

For the nontrivial zeros $`\rho=\beta+i\gamma`$ with $`\beta\gt 1/2`$ and $`|\gamma|\le H`$, put

```math
z_\rho=20(\rho-\tfrac12),\qquad
T(\rho)=\frac{(1-2^{-\rho})(1-2^{1-\rho})}{\rho(\rho-1)},\qquad
A_b=\sum_\rho T(\rho)\,\frac1{|I_b|}\sum_{n\in I_b} n^{z_\rho}.
```

Conjugates and multiplicities count. Thus $`A_b`$ is real. Since $`\sum_\rho|T(\rho)|\lt \infty`$, adding the zeros on or to the left of the line would change a fixed lower allowance by at most an absolute constant. [Tent and explicit formula](../../finite/QUARTIC.md)

**Terminal interval.** There is a fixed $`c\gt 0`$ such that on arbitrarily late squares $`Q`$, $`A_b\ge0`$ for every integer $`b\in[Q-cQ/H,Q]`$ and every choice of the inner progressions. For each fixed $`\varepsilon\gt 0`$, every sufficiently late $`[X,X(\log\log X)^\varepsilon]`$ contains such a square. The same $`c`$ works for all $`\varepsilon`$.

**Full-interval criterion.** There is a $`c_0\gt 0`$ with the following property for any admissible choices of the inner progressions. RH is equivalent to the existence of a fixed $`B\ge0`$ and arbitrarily late squares $`Q`$ such that $`A_b\ge-B`$ at every point of one regular outer grid in $`[Q/\log Q,Q]`$ of spacing $`g\le c_0Q/H`$. The grid's residue may depend on the block. The same $`B`$ must serve every cutoff on every selected square. For example $`g=\lfloor Q/(C H)\rfloor`$ uses only $`O(\log\log Q)`$ cutoffs for a sufficiently large fixed $`C`$. A direct proof of this lower bound over the **whole interval remains open**.

## Approximating the arithmetic prefixes

Suppose a right-of-line zero exists. Put $`\Theta=\sup_\rho\Re\rho`$, $`D_*=20(\Theta-1/2)\gt 0`$, and choose $`1/2\lt \beta_1\lt \Theta`$. Keep $`\beta\ge\beta_1`$ in the real exponential polynomial

```math
P(x)=\sum_{\substack{\beta\ge\beta_1\\|\gamma|\le H}}
        \frac{T(\rho)}{1+z_\rho}e^{z_\rho x}.
```

There is an $`\omega\gt 0`$ such that $`A_b=P(\log b)+O(Q^{D_*-\omega})`$ uniformly in $`b,h_b,r_b`$. To see this, write $`z=z_\rho`$ and $`d=\Re z`$. Replacing $`h_b\sum_{I_b}n^z`$ by $`\int_a^b t^z\,dt`$ costs $`O(h_b b^d(1+|z|\log b))`$ by integrating $`|z|t^{d-1}`$ on the complete cells and allowing two end cells. Also $`h_b|I_b|=b-a+O(h_b)`$. The normalized integral differs from $`b^z/(1+z)`$ by $`O(ab^{d-1})`$. Since $`b\ge Q/\log Q`$ and $`h_b\le a`$, summing the errors costs $`Q^{D_*-1/2+o(1)}`$. The discarded real parts contribute $`O(Q^{20(\beta_1-1/2)})`$. Both exponents leave a fixed saving.

Ingham's estimate gives $`N(\beta_1,t)\ll t^{3(1-\beta_1)/(2-\beta_1)}\log^5(2t)`$. Thus the number $`M`$ of distinct exponents in $`P`$ is $`o(H)`$ and $`\sum_{\beta\ge\beta_1,\,\gamma\gt 0}1/\gamma`$ converges. [Ingham, *On the estimation of N(σ,T)*](https://doi.org/10.1093/qmath/os-11.1.201)

Two compact measures will be used. For $`z=d+i\tau`$ with $`\tau\gt 0`$ take $`\ell=\pi/\tau`$ and give $`0,\ell`$ masses proportional to $`e^{d\ell},1`$. Its transform vanishes at $`z`$ and $`\bar z`$. Convolve these factors over the right-hand half-strip $`\beta\ge\beta_1`$. The resulting probability $`\nu`$ has support in $`[0,S]`$, where $`S=\sum\pi/(20\gamma)\lt \infty`$. The sum of the independent two-valued shifts converges on this interval and bounded convergence preserves each transform zero. In particular $`\int P(x+v)\,d\nu(v)=0`$ for every $`x`$.

Fix a target $`z_0`$ with $`d_0=\Re z_0`$ close to $`D_*`$. A complex measure of total mass one and bounded density, supported in any prescribed interval of positive length, can isolate the coefficient at $`z_0`$. For the differences $`z-z_0\ne0`$ with $`\Re z\ge d_0`$, use the two-point factors above for the large ordinates, with $`\ell=\pi/|\Im(z-z_0)|`$. Their total support length can be made arbitrarily small by starting the tail late. Each remaining difference $`v\ne0`$ is killed by $`(e^{vt}\delta_0-\delta_t)/(e^{vt}-1)`$ for a sufficiently short $`t\gt 0`$. Convolve with a short uniform density, then translate. When this measure is applied to $`e^{-z_0x}P(x)`$, the target survives with nonzero coefficient, including its multiplicity. The terms with smaller real part tend uniformly to zero in the integral as the center $`y`$ tends to infinity, by dominated convergence on $`\sum|T(\rho)|`$. The target is retained for all sufficiently large $`H`$. On a fixed central interval $`J_0`$ about $`y`$ this proves $`\int_{J_0}|P|\gg_{\rho_0}e^{d_0y}`$.

## A taper for measuring the width of an excursion

For a finite sum $`p(t)=\sum_{j=1}^M a_j e^{\zeta_jt}`$, with $`|\zeta_j|\le R`$, take an integer $`N\ge4+M+R`$. On $`[-\pi,\pi]`$ put $`u=\cos^2(t/2)`$ and

```math
w_N(t)=\sum_{j=N}^{2N}\binom{2N}{j}u^j(1-u)^{2N-j}.
```

The zero extension is positive in the interior, at most one, and at least $`1/2`$ on the middle half. The last assertion follows by pairing binomial terms. At the endpoints it vanishes to order $`2N`$. With an absolute constant,

```math
\int |(w_Np)'|\le C N\int |w_Np|. \tag{1}
```

Here are details giving uniformity even for very close exponents. Write $`M_0=\sup_{|t|\le1/4}|p(t)|`$ and $`s=1/(16N)`$. To evaluate $`p(v)`$ for complex $`|v|\le\pi+2`$, interpolate $`\exp((v/s)\operatorname{Log}w)`$ on the nodes $`e^{s\zeta_j}`$ in $`|w-1|\le1/8`$. Its size on $`|w-1|=1/2`$ is at most $`e^{CN}`$. Cauchy's formula bounds a divided difference of order $`k`$ by $`2\cdot4^k e^{CN}`$ and the coefficient norm of its Newton product by $`(1+9/8)^k`$. Applying the interpolant to the shift of $`p`$ at $`0`$ uses only $`p(js)`$, $`0\le j\lt M`$. Hence $`|p(v)|\le e^{C'N}M_0`$. Equal exponents may first be combined.

The analytic formula for $`f=w_Np`$ is likewise bounded by $`e^{CN}M_0`$ on complex unit neighborhoods of the real period. Cauchy's estimate bounds $`p'`$ in the middle by $`e^{CN}M_0`$, giving $`\|f\|_1\ge e^{-C_1N}M_0`$ from a short interval about a point attaining $`M_0`$. It also bounds $`|f^{(N)}|`$ by $`N!e^{CN}M_0`$. Integrating the Fourier coefficients by parts $`N`$ times gives $`|\widehat f(k)|\le e^{C_2N}M_0(N/|k|)^N`$. Beyond $`D N`$, for a sufficiently large absolute $`D`$, both the tail and its derivative have uniform norm at most $`e^{-(C_1+2)N}M_0`$. The remaining trigonometric polynomial $`U`$ has $`\|U'\|_1\ll DN\|U\|_1`$. Indeed $`2F_{2K}-F_K`$ reproduces it for $`K=\lceil DN\rceil`$, with $`F_K`$ the Fejér kernel. Differentiating the sine formula gives $`\|F_K'\|_1\ll K`$ (use the Fourier coefficients for $`|t|\le1/K`$). Adding the two tail errors proves (1).

Scale the taper to radius $`L`$ about $`y`$ and average its translates by $`\nu`$ to get $`W`$. Choose $`L`$ so that $`J_0`$ remains in the middle half under every shift. Take $`N=\lceil4+M+(10+20H)L/\pi\rceil`$. Positivity and (1) give, with $`J`$ a fixed-length interval containing the support,

```math
\int WP=0,\qquad Z=\int W|P|\gg_{\rho_0} e^{d_0y},\qquad
\int|(WP)'|\ll (N/L)Z .
```

For either sign the integral of $`(\pm WP-Z/(4|J|))_+`$ is at least $`Z/4`$. On each positive component the supremum is bounded by the variation on that component. Summing shows that at least one component has length $`\gg L/N`$. There $`\pm P\ge Z/(4|J|)`$ since $`W\le1`$. For fixed $`L`$, $`M=o(H)`$ gives $`L/N\gg1/H`$. All these width estimates concern a single interval and its own weighted mass.

Choose $`\Lambda\gt 1`$ large enough to fit $`J`$ in $`\log[X,\Lambda X]`$. Every such band inside the tested range has a run of each sign of ordinary length $`\gg X/H`$ on every sufficiently late block. Choose $`d_0\gt D_*-\omega/2`$ before applying the arithmetic error estimate. The runs persist with magnitude $`\gg_{\rho_0}X^{d_0}`$ for every inner choice. Applying this to $`[Q/\Lambda,Q]`$ proves that each grid in the full-interval criterion meets a negative run below any prescribed $`-B`$ on every sufficiently late square. If all zeros lie on the line, the retained sum is empty. This proves the equivalence.

## Putting a square endpoint inside the positive run

If $`\Theta\gt 1/2`$ is attained, then, uniformly throughout the tested interval,
$`A_b/b^{D_*}=f(\log b)+o(1)`$, where $`f`$ is the series of terms at $`\beta=\Theta`$ with coefficients $`T(\rho)/(1+z_\rho)`$ and frequencies $`20\gamma`$. The lower real parts disappear by dominated convergence and the omitted top-line tail has vanishing absolute mass. The two preceding measures give peaks of both signs of fixed size in every sufficiently long fixed log interval. The derivative of $`f`$ is bounded since $`|20\gamma/(1+z_\rho)|\le1`$ and $`\sum|T(\rho)|\lt \infty`$. Hence both signs persist for fixed positive log lengths, even as the height cap changes. A square in the last quarter of a positive run gives the terminal assertion within a fixed factor of any sufficiently large starting point.

If $`\Theta\gt 1/2`$ is unattained, fix any log length $`0\lt l\le1`$. As $`\beta_1\uparrow\Theta`$, the support bound $`S`$ tends to zero by dominated convergence. Choose $`S\lt l/20`$ and put the isolating measure inside another interval of length $`l/20`$. The whole tapered construction now fits in a band of log length $`l`$, for example with $`L=l/4`$. The target can still be chosen above the discarded exponents. Eventually $`N/L\le10H`$ for this fixed $`l`$, since $`M=o(H)`$. The lower width constant in $`c/H`$ is therefore independent of $`l`$. The required starting height can depend on $`l`$.

Put $`Y_0=\log X`$, $`H_0=\log Y_0`$. As $`y`$ varies over $`[Y_0,Y_0+\varepsilon\log H_0]`$, the cap $`\log y`$ lies in $`[H_0,H_0+1]`$. The classical zero count in a unit interval is $`O(\log(2H_0))`$. A gap between jumps therefore contains a fixed log interval of length $`l\gt 0`$ depending on $`\varepsilon`$. Work there with the cap held fixed. Consecutive squares have ordinary gaps $`O(\sqrt Q)=o(Q/H)`$, so a square in the last quarter of the positive run retains an entire terminal interval of length $`cQ/H`$. Its actual cap equals the cap used to find the run. The empty-spectrum case works on every square. These cases give the stated search range with the same $`c`$ for every fixed $`\varepsilon`$.

## Returning to the Möbius loss on the same block

For one grid of spacing $`g\le c_0Q/H`$ set $`M_Q=\max_b(-A_b)_+`$ and put $`m=a^5=Q^{5/2}`$. For either sign and every $`\varepsilon\gt 0`$,

```math
L_s(a^5)\ll_\varepsilon Q^\varepsilon(1+M_Q). \tag{2}
```

Indeed, if $`D_*\gt 0`$, the tent formula gives $`|D(x)|/\sqrt x\ll x^{D_*/20}`$ by absolute summation. At $`x=n^4`$, summing with weight $`1/n`$ from $`m`$ through $`m^2`$, and using $`|D(n^4)-R(n^2)|\le2n^2`$, gives $`L_s(a^5)\ll Q^{D_*}`$. The negative run in $`[Q/\Lambda,Q]`$ gives $`M_Q\gg_{\varepsilon}Q^{D_*-\varepsilon}`$ by choosing a target sufficiently close to the supremum. If there is no right zero, the same calculation gives $`L_s(a^5)\ll1+\log Q`$. This proves (2). It is an upper comparison on one block. An independent upper bound on $`M_Q`$ is still needed.

Each prescribed cutoff on a sufficiently fine grid also belongs to a neighborhood on which positive weights give **exactly zero** signed mean, simultaneously for all retained modes. Positive neighboring terms can offset a negative term at the prescribed cutoff. [Proof of local weighted cancellation](LOCAL-AVERAGES.md) · [Verification scope](VERIFICATION.md)
