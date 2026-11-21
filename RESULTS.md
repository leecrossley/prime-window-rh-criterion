# Window criteria for the Riemann hypothesis

Open a result to read its statement, hypotheses and replay instructions. Run its verification commands from that result’s directory. The source link identifies the revision brought into this project. The publication and review links lead to the original records.

| Result | Source revision | Publication | Reviews |
| --- | --- | --- | --- |
| [An ordinary-prime window criterion for the Riemann hypothesis](README.md) | [ad0340a608](https://github.com/leecrossley/prime-window-rh-criterion/tree/ad0340a608081c71229ec60400b501eeceb1e424) | [Releases](https://github.com/leecrossley/prime-window-rh-criterion/releases) · [DOI](https://doi.org/10.5281/zenodo.24410878) | [Issues](https://github.com/leecrossley/prime-window-rh-criterion/issues) · [PRs](https://github.com/leecrossley/prime-window-rh-criterion/pulls) |
| [A delayed-difference window criterion for Dirichlet families](results/dirichlet-window-transfer/) | [45e94616ed](https://github.com/leecrossley/dirichlet-window-transfer/tree/45e94616edeec8df100b908ba2fceae78b2ab2db) | [Releases](https://github.com/leecrossley/dirichlet-window-transfer/releases) · [DOI](https://doi.org/10.5281/zenodo.24410862) | [Issues](https://github.com/leecrossley/dirichlet-window-transfer/issues) · [PRs](https://github.com/leecrossley/dirichlet-window-transfer/pulls) |
| [Which positive dyadic filters can hide a frequency?](results/dyadic-filter-zeros/) | [51b8914291](https://github.com/leecrossley/dyadic-filter-zeros/tree/51b89142913f7fcf4c657a03f310643666086e84) | [Releases](https://github.com/leecrossley/dyadic-filter-zeros/releases) · [DOI](https://doi.org/10.5281/zenodo.24410856) | [Issues](https://github.com/leecrossley/dyadic-filter-zeros/issues) · [PRs](https://github.com/leecrossley/dyadic-filter-zeros/pulls) |
| [A prime-window criterion for RH on perfect powers](results/prime-window-power-samples/) | [c231a263b7](https://github.com/leecrossley/prime-window-power-samples/tree/c231a263b73a03adb60717446e33b6bb08d8ef46) | [Releases](https://github.com/leecrossley/prime-window-power-samples/releases) · [DOI](https://doi.org/10.5281/zenodo.24411620) | [Issues](https://github.com/leecrossley/prime-window-power-samples/issues) · [PRs](https://github.com/leecrossley/prime-window-power-samples/pulls) |

## Shared verification files

Each entry in [the shared-file list](shared-files.json) names the source to edit and its replayable copies. After a change, run `python3 tools/shared_files.py --sync`, replay each affected result and update its manifest. Each result can still be checked from its own directory.

## Checking the collection

Run `sh verify-collection.sh` from the repository root to check the result manifests. Each result’s README gives its mathematical replay and environment requirements. [Contribution and publication guidance](AGENTS.md)
