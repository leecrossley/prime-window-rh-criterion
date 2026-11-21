# The off-line zero sum on square samples

Lee Crossley · 21 November 2026

Write $`\nu=397/1000`$, $`H_0=3\cdot10^{12}`$ and $`M=\lfloor4K\sqrt{\log K}\rfloor`$. The following real sum counts both signs of the ordinate and all multiplicities.

```math
Q(n)=\sum_{\substack{\rho=\beta+i\gamma,\ \beta>1/2\\H_0<|\gamma|\le n^\nu}}
 d_\rho n^{2\rho-1},\qquad
d_\rho=\frac{(1-2^{-\rho})(2^{1-\rho}-1)}{\rho(1-\rho)}.
```

For a finite integer interval $`J`$ write $`V_J=|J|^{-1}\sum_{n\in J}|Q(n)|^2`$. With the family's tent $`W`$ and $`b_m=\Lambda(m)-1`$, write $`S(x)=\sum b_mW(m/x)`$, $`A(x)=\sum b_m^2W(m/x)^2`$, and $`D(J)=\sum_{n\in J}A(n^2)/n^2`$. The requested inequality is $`|J|V_J\le D(J)`$ on an unbounded sequence of whole intervals $`J=[K,M]\cap\mathbb Z`$. Put $`I=\int W^2=3-4\log 2`$. The prime number theorem gives $`A(n^2)/n^2\sim2I\log n`$. This is a pointwise asymptotic, so the average diagonal is $`\sim2I\log K`$ on each of the intervals used below. [Tent and diagonal](https://github.com/leecrossley/prime-window-rh-criterion/blob/1bcb390d5876569539f106e7f0e21a79669ead73/results/prime-window-power-samples/pairs/FINITE.md) · [Family block theorem](https://github.com/leecrossley/prime-window-rh-criterion/blob/1bcb390d5876569539f106e7f0e21a79669ead73/results/prime-window-power-samples/pairs/SHORT-BLOCKS.md)

**Whole blocks at finite height.** For every integer
$`2\le K\le808\,207\,554\,957\,546\,091\,088\,863\,653\,250`$,
$`|J|V_J<0.462D(J)`$. The proof allows off-line zeros in the 45,000 height units immediately beyond Platt and Trudgian's exact verification endpoint. This bound concerns $`Q`$ alone.

**Short runs at arbitrarily large height.** Every sufficiently late $`[K,M]`$ contains at least $`\lfloor K^{1/4}\rfloor`$ consecutive integers on which $`|Q(n)|=O(1)`$ uniformly. On the run, the ratio of its energy to its diagonal is $`O(1/\log K)`$. A sufficiently small fixed $`c>0`$ gives a run of length $`\lfloor cK^{1/4}\sqrt{\log K}\rfloor`$ on which $`|Q(n)|^2\le A(n^2)/(2n^2)`$ at each sample. These estimates use the separate seven-eighths nonvanishing theorem.

**An obstruction on shrinking intervals.** Let $`\Theta=\sup_\rho\Re\rho`$ and $`J_K=[K,K+\lfloor K/\log\log K\rfloor]\cap\mathbb Z`$ for large $`K`$. If $`\Theta>1/2`$, then

```math
V_{J_K}=K^{4\Theta-2+o(1)}
\quad\text{as }K\to\infty. \tag{1}
```

The same exponent holds for the arithmetic mean $`|J_K|^{-1}\sum_{n\in J_K}|S(n^2)/n|^2`$. This proof uses classical zero density and zero counting, with no fixed zero-free half-plane beyond the classical strip. It gives an arithmetic target shorter than the family's published block. A bound $`K^{o(1)}`$ for that arithmetic mean on one unbounded sequence already implies RH. The upper bound on such a sequence remains unproved here.

## The finite whole-block estimate

Platt and Trudgian's Theorem 1 puts every zero up to $`H=3\,000\,175\,332\,800`$ on the line and gives $`N(H)=12\,363\,153\,437\,138`$, counting only positive ordinates. Take $`T=H+5000`$. Corollary 1.2 of Hasanalizade, Shen and Wong gives

```math
N(T)\le \frac{T}{2\pi}\left(\log\frac{T}{2\pi}-1\right)
+0.1038\log T+0.2573\log\log T+9.3675.
```

After integer rounding, $`N(T)-N(H)\le21\,411`$. The number on the right with **both** signs is at most this number. At positive height, $`\rho\mapsto1-\bar\rho`$ pairs each right-hand copy with a left-hand copy at the same height. Conjugation accounts for the negative ordinates. [Finite verification, Theorem 1](https://arxiv.org/html/2004.09765) · [Explicit zero count](https://arxiv.org/abs/2107.06506)

Put $`j_y=\lfloor y^{1000/397}\rfloor`$ and let $`k_y`$ be the largest integer $`K`$ with $`16K^2\log K<(j_y+1)^2`$. Then $`M^\nu\le y`$ exactly when $`K\le k_y`$, including the effect of the floor in $`M`$. For $`K\le k_H`$ the sum vanishes. For $`k_H<K\le k_T`$, at most $`j_T-j_H`$ samples can contribute, and $`|J|\ge j_H+2-k_T`$. Use $`\beta\le7/8`$ and $`|\rho(1-\rho)|\ge H^2`$. Every single term has absolute value at most

```math
B=(1+2^{-1/2})(1+\sqrt2)j_T^{3/4}/H^2.
```

The even-lattice bound $`A(n^2)/n^2\ge I/2-5/n^2`$ follows by summing $`W^2`$ over even integers and dropping powers of two. Thus the nonempty height range obeys

```math
\frac{|J|V_J}{D(J)}
\le\frac{j_T-j_H}{j_H+2-k_T}\,
   \frac{(21\,411 B)^2}{I/2-5/(k_H+1)^2}<0.509 .
```

The exact covered block bases are $`k_H=808\,207\,524\,642\,627\,297\,477\,593\,017\,475`$ and $`k_T=808\,207\,528\,010\,951\,574\,175\,194\,121\,439`$. The latter certifies a bound for possible contributions above the verified height. The independent zero-location certificate ends at $`H`$. [Independent seven-eighths theorem](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean) · [Even-lattice proof](https://github.com/leecrossley/prime-window-rh-criterion/blob/1bcb390d5876569539f106e7f0e21a79669ead73/results/prime-window-power-samples/pairs/FINITE.md#the-diagonal-and-the-certified-bounds)

For the stronger bound put $`T'=H+45\,000`$ and $`L_0=2\log(k_H+1)`$. On a nonempty block the family's prime contribution to the diagonal gives

```math
\frac{D(J)}{|J|}\ge D_0=(L_0-\log4-2)
\left(I-\frac{0.4}{(L_0-\log4)^2}\right)>30.
```

Indeed, on $`[x/4,x]`$ the weight of an ordinary prime in $`A(x)`$ is at least $`(\log x-\log4-2)\log p`$ times $`W(p/x)^2`$. Its sum is bounded below by integration by parts against Dusart's explicit bound on $`|\vartheta(t)-t|`$. The total variation of $`W^2`$ is two. Both positive factors increase with $`\log x`$, and $`x\ge(k_H+1)^2>10^{42}`$. [Family diagonal calculation, equation (4)](https://github.com/leecrossley/prime-window-rh-criterion/blob/1bcb390d5876569539f106e7f0e21a79669ead73/results/prime-window-power-samples/pairs/FINITE.md#the-diagonal-and-the-certified-bounds) · [Dusart, Theorem 5.2](https://arxiv.org/pdf/1002.0442)

Partition $`(H,T']`$ into 360 intervals of width 125 with endpoints $`t_i=H+125i`$. Let $`C_i`$ be the floor of the preceding upper bound on $`N(t_i)`$ minus $`N(H)`$. For $`j_{t_{i-1}}<n\le j_{t_i}`$ use this *cumulative* count, including all potential earlier off-line zeros. Take $`B_i=(1+2^{-1/2})(1+\sqrt2)j_{t_i}^{3/4}/H^2`$. Over every whole block with $`k_H<K\le k_{T'}`$ this gives

```math
\frac{|J|V_J}{D(J)}
\le \frac{\sum_{i=1}^{360}(j_{t_i}-j_{t_{i-1}})(C_i B_i)^2}
{(j_H+2-k_{T'})D_0}<0.462 .
```

Interval arithmetic encloses the right-hand side between $`0.461315221326`$ and $`0.461315221328`$. A separate partition of width 250 gives an upper bound below $`0.464`$. For $`K\le k_H`$ the numerator vanishes and the diagonal is positive. In fact $`W`$ is positive at some integer in the interior of its scaled support and $`\Lambda(m)\ne1`$ for every integer $`m`$.

The same estimate explains what a larger verified height could supply. Suppose all zeros through height $`Y\ge H_0`$ lie on the line. With $`1\le L\le Y/2`$ and $`M^\nu\le Y+L`$, the ratio on a whole block, for large $`Y`$, is

```math
O\!\left((1+L)^3\log Y\,Y^{-485/397}\right).
```

For a nonempty sum $`M\asymp Y^{1/\nu}`$, $`|J|\asymp M`$ and $`\log K\asymp\log Y`$. Only a proportion $`O((1+L)/Y)`$ of samples can enter the extra height interval. It contains $`O((1+L)\log Y)`$ possible terms, each $`O(Y^{(3/4)/\nu-2})`$. Divide the resulting mean square by the diagonal per sample. In particular a sufficiently small constant times $`Y^{485/1191}/(\log Y)^{1/3}`$ can be added to a verified height for the purpose of this energy test. This implication explicitly allows zeros in the added interval.

## Small values on consecutive samples

Use the full tent formula $`U(t)=\sum_\rho d_\rho t^{2\rho-1}=-S(t^2)/t+O(1/t)`$. Its coefficients are absolutely summable, since $`|d_\rho|\ll(1+|\gamma|)^{-2}`$ and each unit height interval contains $`O(\log(3+|\gamma|))`$ zeros. The strictly left and critical-line terms are $`O(1)`$ in absolute sum for $`t\ge1`$. The fixed lower cutoff costs nothing on the right by the finite zero verification. Put $`A_*=2\Theta-1`$. The moving upper cutoff therefore gives, pointwise,

```math
Q(n)=U(n)+O\big(1+n^{A_*-\nu}\log(2n)\big). \tag{2}
```

If $`\Theta=1/2`$, $`Q`$ vanishes identically. Otherwise choose a fixed zero $`\rho_0`$ with $`a_0=2\Re\rho_0-1>\max(0,A_*-\nu)`$. The family's signed single-zero theorem gives real samples of $`S(t^2)/t`$ with opposite signs and magnitude $`\gg_{\rho_0}X^{a_0/2}`$, where $`X=4K^2\sqrt{\log K}`$ and $`t^2`$ is in $`[X/\sqrt{2\log X},X\sqrt{2\log X}]`$. The proof gives $`O(1)`$ rounding error to $`t=\lfloor t\rfloor`$. The range of rounded samples is bounded away from both ends of $`[K,M]`$ by at least a constant times $`K`$ for large $`K`$. Since $`X^{a_0/2}\ge K^{a_0}`$, the errors in (2) preserve the two signs for $`Q`$ (with the sign of the explicit formula reversed). [Signed isolation and rounding](https://github.com/leecrossley/prime-window-rh-criterion/blob/1bcb390d5876569539f106e7f0e21a79669ead73/results/prime-window-power-samples/pairs/SHORT-BLOCKS.md)

For $`n\le m\le n+n^{1/4}\sqrt{\log n}`$, freeze the cutoff at $`n^\nu`$. The contribution to the derivative on $`[n,m]`$ of the frozen terms with $`\beta\ge3/4`$ is $`O(n^{-1/4})`$. Indeed Ingham's zero density gives $`N(3/4,T)\ll T^p`$ for some $`p<1`$, so $`\sum_{\beta\ge3/4}(1+|\gamma|)|d_\rho|<\infty`$ by dyadic summation. The seven-eighths bound gives the factor $`n^{-1/4}`$. The terms with $`\beta<3/4`$ have derivative $`O(n^{-1/2}\log^2 n)`$ by the ordinary zero count. The interval $`(n^\nu,m^\nu]`$ has length $`o(1)`$ because $`\nu-1+1/4<0`$. Each of its $`O(\log n)`$ ordinates contributes at most $`O(n^{3/4-2\nu})`$. Consequently

```math
|Q(m)-Q(n)|\ll (m-n)n^{-1/4}+n^{-11/250}\log n. \tag{3}
```

Opposite signs on integer samples, together with (3) for $`m=n+1`$, force a sample with $`|Q(n)|=o(1)`$. Use (3) afresh from that sample to each later integer. This counts each entering frequency once over the entire extension. The asserted lengths follow from $`n\ge K`$ and $`A(n^2)/n^2\sim 2I\log n`$. The margin to the block endpoints leaves room for either stated length. [Ingham's density estimate](https://doi.org/10.1093/qmath/os-8.1.255) · [Density formula (1.2)](https://arxiv.org/pdf/2405.20552)

There is a corresponding run for the directly observable prime sum. The family's theta theorem supplies a real zero $`S(t_0^2)=0`$ in the same interior range for every sufficiently late block. For real $`t\le u\le t+t^{1/4}\sqrt{\log t}`$ truncate the full explicit formula at the fixed height $`t`$ at both endpoints. The two tails cost $`O(t^{-1/4}\log t)`$ in absolute value, by the seven-eighths bound. Below this height the same derivative split at $`\beta=3/4`$ costs $`O(t^{-1/4})`$ per unit of $`u`$. The $`O(1/t)`$ remainders in the explicit formula give

```math
\left|\frac{S(u^2)}u-\frac{S(t^2)}t\right|
\ll (u-t)t^{-1/4}+t^{-1/4}\log t .
```

Start at $`t=t_0`$ and take successive integer $`u\ge t_0`$. This gives the same two run lengths for $`|S(n^2)/n|`$ and its prime diagonal. Its starting point can differ from the one chosen for $`Q`$. [Family theta theorem](https://github.com/leecrossley/prime-window-rh-criterion/blob/1bcb390d5876569539f106e7f0e21a79669ead73/results/prime-window-power-samples/pairs/THETA.md)

## Isolating one zero in a shrinking interval

Fix $`1/2<\sigma<\Re\rho_0`$. Write $`\lambda_\rho=2\rho-1`$, $`\lambda_0=2\rho_0-1`$, and $`\Delta_\rho=\lambda_\rho-\lambda_0`$. Take only distinct zeros in the construction, restoring multiplicities in the sum. The zeros with $`\beta\ge\sigma`$ and $`|\gamma|\le T`$ number $`O_\sigma(T^p)`$ for any fixed $`p`$ strictly between $`p_0=3(1-\sigma)/(2-\sigma)`$ and $`1`$. In particular, $`\sum_{\beta\ge\sigma,\,|\gamma|>Y}|\gamma|^{-1}\ll_\sigma Y^{p-1}`$. The constants below may depend on $`p,\sigma,\rho_0`$. The test requires no minimum spacing among the other zeros.

For every sufficiently small $`h>0`$ there is a complex measure $`\mu`$ of mass one supported on $`[0,h/2]`$, whose transform $`\int e^{\Delta_\rho v}\,d\mu(v)`$ is zero for every competitor with $`\beta\ge\sigma`$. Its total variation obeys

```math
\|\mu\|_{\rm TV}\le\exp\!\big(C h^{-p/(1-p)}\big). \tag{4}
```

To construct it, choose $`Y=C_1h^{-1/(1-p)}`$ with a sufficiently large fixed $`C_1`$. For each competitor with $`|\gamma|>Y>2|\Im\rho_0|+1`$, set $`u=\pi/|\Im\Delta_\rho|`$ and $`r=e^{u\Re\Delta_\rho}`$. The probability measure $`(r\delta_0+\delta_u)/(1+r)`$ has transform zero at $`\Delta_\rho`$. The sum of its support widths over the high ordinates is $`O(Y^{p-1})`$. Their infinite convolution exists as the law of a sum of independent variables bounded by a summable sequence. Its support has that same width. Each prescribed transform remains zero by factoring out the corresponding probability measure.

For every remaining competitor use the common width $`v=c/Y`$ with a sufficiently small absolute $`c>0`$. Its factor is $`(r\delta_0-\delta_v)/(r-1)`$ with $`r=e^{v\Delta_\rho}`$. It has unit mass and zero transform at $`\Delta_\rho`$, even if the competitor and target share an ordinate. For large $`Y`$ one has $`|v\Delta_\rho|\le1/2`$. Therefore $`|r-1|\gg v|\Delta_\rho|`$ and the factor has variation $`\ll Y/|\Delta_\rho|`$. The total support cost of these factors is $`O(Y^{p-1})`$. Their total log variation is $`O(Y^p)`$. Indeed the finitely many zeros with $`|\gamma|\le 2|\Im\rho_0|+2`$ cost $`O_{\rho_0,\sigma}(\log Y)`$, and the rest cost at most

```math
O(N(\sigma,Y))+\sum_{1\le|\gamma|\le Y,\ \beta\ge\sigma}\log(Y/|\gamma|)
\ll Y^p+\int_1^Y N(\sigma,t)\frac{dt}{t}\ll Y^p .
```

Take $`C_1`$ large enough that the combined support cost is at most $`h/2`$. This proves (4). Multiple copies of the target contribute the same nonzero coefficient $`d_{\rho_0}`$, since neither numerator factor vanishes inside $`0<\Re\rho<1`$.

Convolve $`\mu`$ with the uniform probability on $`[0,h/2]`$, and multiply its density by $`e^{-\lambda_0 v}`$ to get $`w(v)`$. If $`B=\exp(C h^{-p/(1-p)})`$, then $`\|w\|_1\le B`$, $`\|w\|_\infty\le2B/h`$, and $`w`$ is supported on $`[0,h]`$. For $`F_\sigma(t)=\sum_{\beta\ge\sigma}d_\rho t^{\lambda_\rho}`$, counted with multiplicity, absolute convergence gives exactly

```math
\int_0^h w(v)F_\sigma(Ke^v)\,dv
=m_0d_{\rho_0}K^{\lambda_0}, \tag{5}
```

where $`m_0`$ is the target multiplicity. For $`0<h\le\log2`$, put $`t=Ke^v`$, $`n=\lfloor t\rfloor`$. Uniformly in these variables,

```math
F_\sigma(t)-Q(n)
=O\big(K^{2\sigma-1}+K^{A_*-\nu}\log K+K^{A_*-1}\log^2 K\big). \tag{6}
```

The first term bounds zeros between the line and $`\sigma`$ absolutely. The second bounds the series above the *actual* endpoint $`n^\nu`$ using $`\sum_{|\gamma|>u}|d_\rho|\ll\log(2u)/u`$. The last follows by differentiating the finite sum below that endpoint between $`n`$ and $`t`$ and summing $`O((1+|\gamma|)^{-1})`$ up to $`n^\nu`$. For the arithmetic observable $`-S(n^2)/n`$, first use the same cutoff comparison, or apply (2) and the tent formula. The errors in (6) still suffice. None of these bounds assumes that the upper endpoint avoids a zero.

Take $`h=\log(1+1/\log\log K)`$. The samples in $`[K,Ke^h]`$ are exactly $`J_K`$, $`|J_K|\asymp Kh`$, and $`\log B=o(\log K)`$ for each fixed $`p<1`$. The logarithmic cell for a given integer has length at most $`1/K`$. Hence, by the $`L^\infty`$ bound for the density and Cauchy–Schwarz,

```math
\left|\int_0^h w(v)Q(\lfloor Ke^v\rfloor)\,dv\right|
\le \frac{2B}{Kh}\sum_{n\in J_K}|Q(n)|
\ll B\sqrt{V_{J_K}} .
```

Choose $`\rho_0`$ with $`a_0=2\Re\rho_0-1>\max(0,A_*-\nu)`$. All three errors in (6) times $`B`$ are $`o(K^{a_0})`$, since $`2\sigma-1<a_0`$ and $`A_*\le1`$. Equations (5)–(6) give $`\sqrt{V_{J_K}}\gg_{\rho_0,\sigma}K^{a_0}/B`$. Take zeros with real parts arbitrarily close to $`\Theta`$. The absolute upper bound $`|Q(n)|\ll K^{A_*}`$ on this interval proves (1), including when no zero attains $`\Theta`$. The same two bounds apply to the arithmetic observable. On the requested longer interval $`[K,M]`$ the ratio of its length to $`|J_K|`$ is only $`K^{o(1)}`$, so positivity of the sum of squares gives the same lower exponent there. If $`\Theta=1/2`$, the target sum is empty and the arithmetic observable is bounded by its absolutely convergent explicit formula.

More generally the argument works for $`J=[K,K+\lfloor K/(\log K)^a\rfloor]`$ if $`a\ge0`$ and $`\Theta>(1+3a)/(2+3a)`$. Choose $`\sigma<\Theta`$ sufficiently large that $`a<(1-p_0)/p_0`$, then $`p>p_0`$ close enough that $`ap/(1-p)<1`$. Now $`\log B=o(\log K)`$ again. The case $`a=0`$ can use any sufficiently small fixed $`h`$ inside $`[K,2K]`$ and length comparison. For example, a subpower arithmetic mean square on arbitrarily late intervals of length $`\lfloor K/(\log K)^{1/3}\rfloor`$ would prove $`\Theta\le2/3`$. No such arithmetic upper estimate is proved here.

## Prior work and verification

Stechkin and Popov's Theorems 7–8 already isolate an off-line zero to lower-bound the integral of the absolute ordinary prime-counting error on every fixed-ratio interval. In their proof, formula (39.4) constructs a canonical product on a sparse right-hand set omitting the target. Their later results on shrinking intervals also treat signed averages along sequences of scales. Brent, Platt and Trudgian treat the ordinary continuous dyadic mean square. Grosswald's estimate for the ordinary prime-counting error also uses the summability of inverse ordinates to the right of a fixed line. The family already established the full-scale equivalence for the tent. The specializations here are the moving upper cutoff, the cost in (4) as the support shrinks, the integer-square samples, and the bound on the runs that pass. The search found closely related results and left priority for these exact statements unconfirmed. [Stechkin and Popov](https://www.mathnet.ru/eng/rm1018) · [Brent, Platt and Trudgian](https://arxiv.org/abs/2008.06140) · [Grosswald's estimate as recorded by Zhao, equation (24)](https://arxiv.org/abs/2411.18903)

The unconditional pair-correlation theorem of Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh estimates a weighted sum over all pairs for $`x=T^\alpha`$ with $`0\le\alpha\le1`$. Here the phase comes from $`x=n^2`$, while the greatest included ordinate is $`T=n^\nu`$, giving $`\alpha=2000/397>5`$. Moreover the restriction to right-half zeros and the tent coefficients change the sum. Their Theorem 1 does not supply the missing upper bound. [Unconditional pair correlation, Theorem 1](https://arxiv.org/pdf/2306.04799)

The finite block endpoints and ratio bound were certified at two precisions. The endpoint check uses both integer bisection and the Lambert $`W`$ inverse. The numerical tests of the filter and moving boundary use synthetic exponents, including a close pair, two equal ordinates with distinct real parts, repeated terms and actual changes in the cutoff. Lean checks the finite filter algebra, the energy bound on the active samples, the discrete crossing lemma, the density-width inversion and exponent arithmetic. The infinite convolution, zero-density estimates and transfer to the sampled mean in (1) have written proofs. [Calculation](check_surviving_zeros.py) · [Lean lemmas](SurvivingZeros.lean) · [Replay record](CHECKS.txt)
