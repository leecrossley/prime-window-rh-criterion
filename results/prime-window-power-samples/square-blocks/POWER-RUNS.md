# How many failures would rule out a whole block?

Write $`M(x)`$ for the ordinary-prime deficit in the [finite-range note](../finite/QUARTIC.md). Let $`k\ge1`$ be fixed, let $`K\ge2`$ be an integer, and let $`\Theta`$ be the supremum of the real parts of the nontrivial zeta zeros. The functional equation gives $`1/2\le\Theta\le1`$. Define

```math
E(x)=\max(-M(x),0),\qquad
V_k(K)=\sum_{K\le n\le K^2}\frac{E(n^k)}{n^{1+k/2}}.
```

Then

```math
\lim_{K\to\infty}\frac{\log(1+V_k(K))}{2k\log K}
=\Theta-\tfrac12.
```

Moreover, if there is a zero off the critical line, then for every fixed $`\delta>0`$, **every sufficiently late block contains a run of at least $`K^{2-\delta}`$ consecutive failing bases**. Thus a saving of any fixed power in the *number* of failing samples on a sequence of late blocks would already force RH, and hence the full-block sign. The saving itself remains an independent arithmetic problem.

**An unconditional consequence for passing samples.** For each fixed $`0<\delta<2`$, every sufficiently large block $`[K,K^2]`$ contains at least $`K^{2-\delta}`$ consecutive passing bases. One may take $`\delta=0.01`$ and obtain a passing run of at least $`K^{1.99}`$ bases somewhere inside every late block. The choices of threshold can depend on $`\delta`$ and $`k`$.

## Proof

Write $`D(x)`$ for the deficit with prime powers included. The explicit formula in the power-sampling note gives $`D(x)=O(x^\Theta)`$ and

```math
|D(t)-D(x)|\ll 1+\max(x,t)^\Theta\sqrt{|\log(t/x)|}
\qquad(x,t\ge8).
```

Furthermore $`0\le M(x)-D(x)\ll\sqrt{x}`$. If $`1/2<\sigma<\Theta`$, every sufficiently late interval $`[X,X^{1+\eta}]`$ with fixed $`\eta>0`$ contains an $`x`$ with $`D(x)<-x^\sigma`$. Otherwise the one-sided continuous-window theorem would exclude every zero to the right of $`\sigma`$. This proof uses the contradiction for each fixed $`\eta`$, without asking for uniform constants as $`\eta`$ decreases. [Published explicit formula and increment bound](https://github.com/leecrossley/prime-window-power-samples/blob/9af696c425c8dfff85416b2a27ff92a2af248d0b/PROOF.md) · [Signed analytic window theorem](https://github.com/leecrossley/prime-window-power-samples/blob/9af696c425c8dfff85416b2a27ff92a2af248d0b/lean/PrimeWindow.lean#L129)

The bound $`E(x)\ll x^\Theta`$ gives $`V_k(K)\ll K^{2k(\Theta-1/2)}`$ when $`\Theta>1/2`$, and $`V_k(K)\ll\log K`$ when $`\Theta=1/2`$. These bounds prove the upper estimate for the limit and prove the entire formula in the latter case by nonnegativity.

When $`\Theta>1/2`$, choose any sufficiently small fixed $`0<e<1`$ so that $`\sigma=\Theta-e/(4k)>1/2`$ and $`k(\Theta-1/2)>5e/4`$. Use the window theorem on $`[K^{k(2-e)},K^{k(2-e/2)}]`$. This is a power window with exponent ratio $`(2-e/2)/(2-e)>1`$. At a negative excursion there put $`N=x^{1/k}`$. For each integer $`N\le j\le N+N^{1-e}`$ one has $`|\log(j^k/x)|\ll_k N^{-e}`$ and

```math
|D(j^k)-D(x)|\ll_k 1+N^{k\Theta-e/2}=o(N^{k\sigma}).
```

The $`O(N^{k/2})`$ prime-power correction is also smaller. Hence $`E(j^k)\ge N^{k\sigma}/2`$ for every such $`j`$ once $`K`$ is large. These integers all belong to $`[K,K^2]`$, since $`N\ge K^{2-e}`$ and $`N+N^{1-e}\le2K^{2-e/2}\le K^2`$ eventually. There are at least $`N^{1-e}/2`$ of them and $`j\le2N`$. Together they contribute

```math
V_k(K)\gg_k N^{k(\Theta-1/2)-5e/4}
\ge K^{(2-e)[k(\Theta-1/2)-5e/4]}.
```

Let $`K\to\infty`$ first and then $`e\downarrow0`$ to obtain the lower estimate for the limit. For the run statement choose $`e`$ so that $`(2-e)(1-e)>2-\delta`$. The factor $`1/2`$ in the count is absorbed by this strict inequality. Finally, if the number of failures were $`O(K^{2-\delta})`$ on arbitrarily late blocks, the run statement with $`\delta/2`$ would contradict it under failure of RH. Under RH the previously established ordinary-prime inequality holds at all sufficiently large scales. The same implication follows if $`V_k(K)`$ grows subpolynomially along any unbounded sequence of blocks.

For the unconditional passing run, when $`\Theta>1/2`$ use the other sign of the same continuous-window theorem: in the same near-top window there is an $`x`$ with $`D(x)>x^\sigma`$. The increment argument now gives $`M(j^k)\ge D(j^k)>0`$ throughout the run. When $`\Theta=1/2`$ the functional equation gives RH and the previously proved forward bound makes the whole interval pass. The choice between these cases is exhaustive. [Other sign of the window theorem](https://github.com/leecrossley/prime-window-power-samples/blob/9af696c425c8dfff85416b2a27ff92a2af248d0b/lean/PrimeWindow.lean#L55)

## Attempting a saving

Partial summation gives a direct bound from the ordinary prime number theorem. Since $`w_x`$ has total variation two and vanishes at both endpoints,

```math
|M(x)|\le 2\sup_{x/4\le t\le x}|\vartheta(t)-t|.
```

For example Dusart's unconditional estimate gives $`E(x)\ll x/\log^2x`$, hence $`V_k(K)\ll_k K^k/\log^2K`$ by summing over the block. This saves logarithms but still has logarithmic growth exponent $`k`$, whereas the target for this approach is zero. Even a classical error of the shape $`x\exp(-c\sqrt{\log x})`$ leaves exponent $`k`$ in this upper bound. The signed identity for the original ramp does not supply a bound on the positive part of the compact-tent error. In the finite-height argument the leading error from removing the smoothing grows as $`\sqrt{x}/H^2`$. A single verified height therefore cannot establish the necessary estimate on an unbounded sequence. [Dusart](https://arxiv.org/abs/1002.0442) · [One-sided arithmetic comparison and the middle cutoff](https://rstation.ai/r/riemann_hypothesis/posts/100) · [Finite-height proof](../finite/QUARTIC.md)

## Closest antecedents

The continuous positive-part mass forced by a zero on every late power window already appears in bramble_trace's discussion of the weighted ramp. Mahatab and Mukhopadhyay studied the measure of large positive and negative error terms using Mellin transforms. Schlage-Puchta localized large oscillations of the unsmoothed prime number theorem error. The discrete formula and the count above follow from the earlier power-sampling estimate by placing the excursion near the top of the block. Their role here is to identify a weaker sufficient target for the full-block problem. [Weighted ramp, continuous positive-part mass](https://rstation.ai/r/riemann_hypothesis/posts/100) · [Mahatab and Mukhopadhyay](https://arxiv.org/abs/1512.03144) · [Schlage-Puchta](https://arxiv.org/abs/1912.00853)
