# The sign of the dyadic unequal-pair sum

Lee Crossley · 21 November 2026 · Research notes

For $b_m=\Lambda(m)-1$ and the compact dyadic tent $W$, put

$$
c_n=\frac{1}{n^2}\sum_{m\ne j} b_mb_jW(m/n^2)W(j/n^2),\qquad
C_K=\sum_{K\le n\le K^2}c_n.
$$

Both orders of each unequal pair count. Under RH, the tent’s absolutely convergent explicit formula gives $C_K<0$ on every sufficiently late whole block. An arithmetic proof of $C_K\le0$ on an unbounded sequence of whole blocks remains open.

| Result obtained without assuming RH | Where to find the proof |
| --- | --- |
| Every individual $c_n$ is strictly negative on every block with $`2\le K\le1\,200\,000\,000\,000`$. A hypothetical first failure forces an off-line zero within an explicit height and real-part range. | [Finite bounds](FINITE.md) |
| Every sufficiently late $[B,4B\sqrt{\log B}]$ contains a run of at least $\lfloor\exp((\log B)^{3/5}/(5(\log\log B)^{1/5}))\rfloor$ consecutive negative $c_n$. | [Theta identity and runs](THETA.md) |
| Nonpositivity of the sum on arbitrarily late $[B,4B\sqrt{\log B}]$ is itself equivalent to RH. A filter for any one zero proves the converse directly, including for a zero of higher multiplicity. | [Short-block criterion](SHORT-BLOCKS.md) |

The exact divisor identity used here is $\sum_m(\Lambda(m)-1)G(m/x)=\sum_h(\log h-\tau(h))g(h/x)$ for a three-term theta weight $G$. One can evaluate the left side on the whole positive axis and use it to locate real zeros of the original $S(x)=\sum_m b_m W(m/x)$. The square of $S(n^2)$ controls the block sign. For a model oscillation from a zeta zero, its first theta average vanishes at every scale and the square has a strictly positive average. This is the remaining obstruction.

## Checks

The analytic theorems are written proofs. Lean 4.33.1 checked nine finite identities and inequalities, including the ordered-pair expansion, the arithmetic divisor identity at finite cutoffs, both hinge bounds and the weighted square-cell inequality used to transfer the continuous detector to integer samples. The module lists its axiom dependencies. The separate kernel replay accepted it. [Lean source](PairSignChecks.lean) · [Check transcript](CHECKS.txt)

The three certificates ran with CPython 3.12.14 and python-flint 0.9.0 at 160 and 256 bits. Both precisions gave the following outward bounds.

| Check | Outcome |
| --- | --- |
| Small bases by prime-power trial division | All $2\le n<32$ negative. Maximum $<-0.00504324$. Direct ordered pairs also agree at $2\le n\le8$. |
| Middle finite range | Centered square-root ratio $<0.293$, normalized diagonal $>0.108$. |
| Large finite range | Centered ratio $<0.441$, normalized diagonal $>0.219$. Endpoint height ratio $<0.943$. |
| Two arithmetic expressions for the theta sum | Enclosures overlap at $x=8,16,32,64$. |
| Three explicit dilations of the theta weight | Certified squared approximation error below $0.00410$ of the squared tent norm. |
| First-zero filter | The modulus of the unnormalized residue lies between $0.0000275384$ and $0.0000275385$. The divisor-side integral differs from it by less than $`2.75\%`$ at $X=128$. |

For the last check the arithmetic quantity compared with the residue is $\int_0^X S_G(t)t^{-\rho-1}dt$. The program integrates each of the three Gaussians by the upper incomplete gamma function, bounds the omitted integer tail and uses a separately evaluated $\zeta'(\rho)$ for the residue. The finite examples test signs and normalizations. The asymptotic and its use on all late blocks follow from the proof.

From this directory with python-flint installed, use

~~~sh
for bits in 160 256
do
    python3 -B check_pairs.py --bits "$bits"
    python3 -B check_theta.py --bits "$bits"
    python3 -B check_filter.py --bits "$bits"
done
~~~

For the Lean replay, set **pair_source** to this directory and run the following from the Mathlib checkout at commit **0df444a360eaa60ab8c11dca51a86af692955474**, using Lean commit **819816b2e0a3bf405af45ae5c7af2491d8f5bee6**.

~~~sh
pair_build=$(mktemp -d)
lake env lean -DautoImplicit=false -R "$pair_source" -o "$pair_build/PairSignChecks.olean" "$pair_source/PairSignChecks.lean"
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec leanchecker -v PairSignChecks' sh "$pair_build"
~~~

## Prior work and scope

The original tent, its explicit formula, the low-zero mass and the earlier square test with the tent centered at a square came from bramble_trace. The preceding release proves a finite one-sided bound for an ordinary-prime deficit through real scale $10^{45}$. The repository's earlier unconditional run theorem concerns that deficit. A positive ordinary-prime deficit does not give a two-sided bound on the centered prime-power sum. The Omega Institute independently treats an eventual one-sided bound for the cumulative Mangoldt remainder sampled at fourth powers. The quadratic pair statistic here uses square scales and a sum over a block. [Original tent](https://rstation.ai/r/riemann_hypothesis/posts/100#comment-61fubEt16h1nsGVD) · [Prior release](https://github.com/leecrossley/prime-window-power-samples/releases/tag/v1.1.1) · [Omega's fourth-power theorem](https://github.com/the-omega-institute/trureturing/blob/4e51eeaa9736a08ad0e9b8b79579e4b7ba80837e/Blueprint/D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling.md)

Büthe transfers finite zero verification to explicit bounds for prime counts. Cáceres studies finite two-sided margins and energy for a different logarithmic weight. Brent, Platt and Trudgian give upper and lower bounds for the integral of the square of $\psi(x)-x$ over a dyadic interval. Montgomery and Soundararajan study short-interval variance, where the interval length enters the arithmetic correlation. These are antecedents for the methods and the type of question. [Büthe](https://arxiv.org/abs/1410.7015) · [Cáceres](https://hexagonmath.org/pdf/2610.00661v2) · [Brent, Platt and Trudgian](https://arxiv.org/abs/2008.06140) · [Montgomery and Soundararajan](https://arxiv.org/abs/math/0409258)

The positive theta kernel for $\xi$ is classical. Convolution methods for mean-periodic functions associated to zeta functions are established. Pintz, Schlage-Puchta and Révész studied localization of prime-number-theorem oscillations from individual zeros, including effective tradeoffs between the size and the localization. Kaczorowski studied local sign changes for classical prime remainders. The Montgomery–Vorhauer factor $2.02$ for $\psi(x)-x$ assumes RH. The earlier 547/727 calculation uses a selected Dirichlet zero, compact averages and a different prime-ideal score. [Rodgers and Tao, equations (1)–(3)](https://arxiv.org/pdf/1801.05914) · [Fesenko, Ricotta and Suzuki](https://arxiv.org/abs/0803.2821) · [Schlage-Puchta, including Pintz's theorem](https://arxiv.org/pdf/1912.00853) · [Révész](https://arxiv.org/abs/2202.01837) · [Kaczorowski](https://matwbn.icm.edu.pl/ksiazki/aa/aa45/aa4517.pdf) · [Montgomery and Vorhauer](https://doi.org/10.7169/facm/1229442626) · [547/727 result](https://github.com/leecrossley/theta-race-waiting-bound/blob/9193ef9459374da9f68156ad6a1aa8db088882b0/PROOF.md)

The literature search covered the centred dyadic tent, finite-height bounds, squared prime sums on integer powers and localisation using the completed zeta function. It found no earlier statement of the explicit finite pair bound, the quantitative negative runs for this statistic or the short-block pair criterion. The whole-block sign follows under RH. Alpöge announced a Lean proof of RH on 20 November 2026, and Sutherland records the independent checks of that formal proof. [Alpöge’s announcement](https://alpo.ge/remark.pdf) [Sutherland’s verification record](https://math.mit.edu/~drew/grh/)