# Window criteria for the Riemann hypothesis

Open a result to read its statement, hypotheses and replay instructions. Run its verification commands from that result’s directory. The source link identifies the revision brought into this project. The publication and review links lead to the original records.

| Result | Source revision | Publication | Reviews |
| --- | --- | --- | --- |
| [An ordinary-prime window criterion for the Riemann hypothesis](README.md) | [ad0340a608](https://github.com/leecrossley/prime-window-rh-criterion/tree/ad0340a608081c71229ec60400b501eeceb1e424) | [Releases](https://github.com/leecrossley/prime-window-rh-criterion/releases) · [DOI](https://doi.org/10.5281/zenodo.24410878) | [Issues](https://github.com/leecrossley/prime-window-rh-criterion/issues) · [PRs](https://github.com/leecrossley/prime-window-rh-criterion/pulls) |
| [A delayed-difference window criterion for Dirichlet families](results/dirichlet-window-transfer/) | [45e94616ed](https://github.com/leecrossley/dirichlet-window-transfer/tree/45e94616edeec8df100b908ba2fceae78b2ab2db) | [DOI](https://doi.org/10.5281/zenodo.24410862) | [Issues](https://github.com/leecrossley/prime-window-rh-criterion/issues) · [PRs](https://github.com/leecrossley/prime-window-rh-criterion/pulls) |
| [Which positive dyadic filters can hide a frequency?](results/dyadic-filter-zeros/) | [51b8914291](https://github.com/leecrossley/dyadic-filter-zeros/tree/51b89142913f7fcf4c657a03f310643666086e84) | [DOI](https://doi.org/10.5281/zenodo.24410856) | [Issues](https://github.com/leecrossley/prime-window-rh-criterion/issues) · [PRs](https://github.com/leecrossley/prime-window-rh-criterion/pulls) |
| [A prime-window criterion for RH on perfect powers](results/prime-window-power-samples/) | [e53c23a265](https://github.com/leecrossley/prime-window-power-samples/tree/e53c23a2656ce0a410b332154e70f36f9f58b4ee) | [DOI](https://doi.org/10.5281/zenodo.24411620) | [Issues](https://github.com/leecrossley/prime-window-rh-criterion/issues) · [PRs](https://github.com/leecrossley/prime-window-rh-criterion/pulls) |

On fourth-power samples, a logarithmic bound for the negative part of a paired Möbius sum on arbitrarily late blocks is equivalent to RH. The finite certificate bounds the loss by $2(1+2\log m)$ for every $10{,}000\le m\le2{,}000{,}000$. A companion proves that a weighted sum over the zeros right of the critical line is nonnegative on a terminal interval of arbitrarily late square blocks, and leaves the full-interval bound open. [Möbius criterion and certificates](results/prime-window-power-samples/pairs/mobius/) · [Signed cutoffs](results/prime-window-power-samples/pairs/mobius/CUTOFFS.md)

The power-sampling result now also gives an $8/9$ upper bound for the mean square on every complete short block through $K=4\cdot10^{24}$, using OpenAI's Lean theorem for the zero-free half-plane $\Re s>7/8$. [Finite theorem and certificate](results/prime-window-power-samples/pairs/ODD-MEAN-SQUARE.md) [Release with both calibration checks](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/odd-shift-mean-square-v1.0.2)

The [square-sample median and pair-discrepancy results](results/prime-window-power-samples/square-blocks/) give an RH equivalence on shrinking blocks, a finite zero-exception range and a sharp lower limit for a weighted pair statistic. [All square-sample editions](https://github.com/leecrossley/prime-window-rh-criterion/releases?q=square-block-median) · [Hypotheses and verification (v1.0.2)](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/square-block-median-v1.0.2) · [Equation display fixes (v1.0.1)](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/square-block-median-v1.0.1) · [First edition (v1.0.0)](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/square-block-median-v1.0.0)

## Shared verification files

Each entry in [the shared-file list](shared-files.json) names the source to edit and its replayable copies. After a change, run `python3 tools/shared_files.py --sync`, replay each affected result and update its manifest. Each result can still be checked from its own directory.

## Checking the collection

Run `sh verify-collection.sh` from the repository root to check the result manifests. Each result’s README gives its mathematical replay and environment requirements. [Contribution and publication guidance](AGENTS.md)

## Edition DOIs

Each DOI identifies a fixed release. The final column identifies the archive with the proof files in this revision. A shared release can contain several papers. The fourth-power Möbius row gives both the original paper and the edition containing the separate kernel checks for the eleven result modules. The collection as archived on 21 November 2026 is available at [10.5281/zenodo.24426583](https://doi.org/10.5281/zenodo.24426583).

| Result | Published release | Version DOI | Current proof files |
| --- | --- | --- | --- |
| [An ordinary-prime window criterion for the Riemann hypothesis](README.md) | [v1.1.1](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/v1.1.1) | [10.5281/zenodo.24421600](https://doi.org/10.5281/zenodo.24421600) | [10.5281/zenodo.24426583](https://doi.org/10.5281/zenodo.24426583) |
| [A delayed-difference window criterion for Dirichlet families](results/dirichlet-window-transfer/README.md) | [v1.0.4](https://github.com/leecrossley/dirichlet-window-transfer/releases/tag/v1.0.4) | [10.5281/zenodo.24410863](https://doi.org/10.5281/zenodo.24410863) | [10.5281/zenodo.24426583](https://doi.org/10.5281/zenodo.24426583) |
| [Which positive dyadic filters can hide a frequency?](results/dyadic-filter-zeros/README.md) | [v1.0.4](https://github.com/leecrossley/dyadic-filter-zeros/releases/tag/v1.0.4) | [10.5281/zenodo.24412802](https://doi.org/10.5281/zenodo.24412802) | [10.5281/zenodo.24426583](https://doi.org/10.5281/zenodo.24426583) |
| [A prime-window criterion for RH on perfect powers](results/prime-window-power-samples/README.md) | [v1.2.1](https://github.com/leecrossley/prime-window-power-samples/releases/tag/v1.2.1) | [10.5281/zenodo.24414757](https://doi.org/10.5281/zenodo.24414757) | [10.5281/zenodo.24426583](https://doi.org/10.5281/zenodo.24426583) |
| [Odd-shift mean square](results/prime-window-power-samples/pairs/ODD-MEAN-SQUARE.md) | [odd-shift-mean-square-v1.0.2](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/odd-shift-mean-square-v1.0.2) | [10.5281/zenodo.24417740](https://doi.org/10.5281/zenodo.24417740) | Same edition |
| [Square-block median](results/prime-window-power-samples/square-blocks/README.md) | [square-block-median-v1.0.2](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/square-block-median-v1.0.2) | [10.5281/zenodo.24425367](https://doi.org/10.5281/zenodo.24425367) | [10.5281/zenodo.24426583](https://doi.org/10.5281/zenodo.24426583) |
| [Fourth-power Möbius criterion](results/prime-window-power-samples/pairs/mobius/README.md) | [fourth-power-mobius-v1.0.0](https://github.com/leecrossley/prime-window-rh-criterion/releases/tag/fourth-power-mobius-v1.0.0) | [10.5281/zenodo.24426583](https://doi.org/10.5281/zenodo.24426583) | [10.5281/zenodo.24428032](https://doi.org/10.5281/zenodo.24428032) |
