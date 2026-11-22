# Prime-counting errors on square samples

Lee Crossley · 21 November 2026

Edition 1.0.3 includes the five certificate programs and their checks for Python optimisation. [Versioned archive](https://doi.org/10.5281/zenodo.24438940) [Tagged paper and checks](https://github.com/leecrossley/prime-window-rh-criterion/tree/53d57c0a080f90c3945d43aa3f421ec045bcba16/results/prime-window-power-samples/square-blocks)

Put $`E_n=\pi(n^2)-\mathrm{li}(n^2)`$, $`J_K=\{K,\ldots,K+\lfloor K/\log\log K\rfloor\}`$ and let $`m_K`$ be any median of $`E_n`$ on $`J_K`$. Count the samples with $`|E_n-m_K|>K(\log K)^2`$. Write $`B_K`$ for that count.

**A median criterion for RH.** The following are equivalent.

1. RH holds.
2. There is a fixed $`\eta>0`$ such that $`B_K=O(K^{1-\eta})`$ along some unbounded sequence of integers $`K`$.

Under RH the count is eventually zero. If any zeta zero has real part above $`1/2`$, then $`\log B_K/\log K\to1`$ on all sufficiently late blocks. The converse isolates one zero on a shrinking interval, transfers the result to square samples, and subtracts any block median. An independent proof of the upper bound in 2 remains open here. [Isolation on shrinking intervals](SURVIVING-ZEROS.md) · [Passage to the median](SHORT-ARITHMETIC.md#cumulative-counts-between-consecutive-squares)

**Finite certificate and fluctuations within groups.** Every integer $`16\le K\le1\,290\,008\,597\,927\,572`$ has $`B_K=0`$, using Johnston's finite prime-counting estimates. At unbounded height divide $`J_K`$ into consecutive groups of $`\lfloor K^{1/8}\rfloor`$ samples. The groups on which the real range of $`\pi(t^2)-\mathrm{li}(t^2)`$ exceeds $`K^{127/128}`$ contain $`O(K^{31/32})`$ samples altogether. The group estimate uses the separate seven-eighths zero-free theorem. Concentration of the first samples of the groups around one centre would give the missing whole-block bound. [Proof, finite endpoint and grid criterion](MEDIAN-EXCEPTIONS.md) [Johnston](https://arxiv.org/abs/2109.02249) [Seven-eighths theorem](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)

**A sharp lower limit for weighted pairs.** Put $`b_m=\Lambda(m)-1`$. Use the continuous tent $`W(t)=2-1/(2t)`$ for $`1/4\le t\le1/2`$, $`W(t)=1/t-1`$ for $`1/2<t\le1`$, and zero outside. Write $`S(x)=\sum_m b_m W(m/x)`$. Let $`R(x)`$ be the ordered unequal-pair sum with this weight after subtracting the centred Hardy–Littlewood singular series at each separation and dividing by $`x`$. Then $`R(x)=S(x)^2/x+B+o(1)`$ with $`0.36160550<B<0.36160555`$. Moreover $`\liminf R(n^2)=B`$. This is an unconditional result for the aggregate over all separations, including prime powers. The odd and even subtotals also give a measurable cancellation ratio with logarithmic exponent $`2\Theta-2`$, where $`\Theta=\sup_\rho\Re\rho`$. [Lower-limit proof and exact normalisation](PAIR-DISCREPANCY.md) · [Parity calculation](SHIFT-CANCELLATION.md)

**Other consequences.** On every shrinking block in the off-line case the mean square of $`S(n^2)/n`$ has exponent $`4\Theta-2`$. Using the seven-eighths theorem, its signed mean is $`O(K^{-1/4})`$ on arbitrarily late shrinking blocks. On the longer $`[K,K^2]`$ blocks every fixed power has passing runs of length at least $`K^{2-\delta}`$ for each $`0<\delta<2`$ and all sufficiently large $`K`$. The last assertion follows by placing an excursion near the top of the earlier power-sampling window. [Shrinking-block proof](SURVIVING-ZEROS.md) · [Signed mean](SHORT-ARITHMETIC.md) · [Power runs and failure counts](POWER-RUNS.md)

## Prior work

The tent and an earlier square-sampling principle are due to bramble_trace. Stechkin and Popov isolated zeros for continuous prime-counting errors, including lower bounds on fixed-ratio intervals. Brent, Platt and Trudgian studied the continuous mean square on dyadic intervals. Bazzanella and Perelli studied exceptional sets for prime counts in short intervals. The new comparison here is the shrinking integer-square block, its freely chosen median, and the quantified concentration inside a fixed grid. Johnston supplies the finite input. The analytic proofs of the pair identity use the classical Cesàro formula for the singular series and prime-number-theorem estimates. The numerical constant and its attainment at squares belong to this specific weight. The primary sources reviewed did not contain these exact statements. Priority beyond that comparison is unconfirmed. [Original tent](https://rstation.ai/r/riemann_hypothesis/posts/100#comment-61fubEt16h1nsGVD) · [Stechkin and Popov](https://www.mathnet.ru/eng/rm1018) · [Brent, Platt and Trudgian](https://arxiv.org/abs/2008.06140) · [Bazzanella and Perelli](https://doi.org/10.1006/jnth.1999.2429) · [Goldston and Suriajaya](https://arxiv.org/abs/2007.14616) · [Kuperberg](https://arxiv.org/abs/2301.06095)

## Verification

Run the replay from this directory with Python 3.12, python-flint 0.9.0 and assertions enabled. The wrapper and each certificate program stop before checking any data if Python optimisation is on.

~~~sh
sh replay.sh
~~~

The replay checks the finite margins, medians, square samples and singular-series quadrature. Four Lean modules check 32 named supporting lemmas and two helper lemmas. The limiting assertions, zero isolation and zero-density estimates have written analytic proofs. The numerical checks cover finite inputs. [Replay transcript and Lean commands](CHECKS.txt)
