# Verification of the eight-character bound

On 22 November 2026 the sign-row and ordinary-tower proofs each passed a clean source rebuild, standalone kernel replay and transitive dependency audit. Every target started with an empty local build directory. The signs use the pinned Mathlib. The tower adds the authenticated geometric archive. [Replay commands](README.md#replay) · [Pinned inputs](../../REPLAY.md)

| Theorem | Local sources checked | Named modules replayed by `leanchecker` | Reachable declarations |
| --- | ---: | ---: | ---: |
| `UnitSigns.row_counts` | 8 | 5 | 72,843 |
| `TameSigns.host_tower_three` | 27 | 14 | 100,303 |

The arithmetic audit requires the actual local Artin symbol, restriction from absolute to finite inertia, the global parity relations and cofinal descent. It excludes `sorryAx`, RH, Mizusawa’s rank theorem, the earlier nine-generator theorem and Ferrero–Washington. The axiom list consists of `propext`, `Classical.choice` and `Quot.sound`. The transcripts retain the compiler output and timestamps, with the temporary replay directory name replaced. [Sign-row transcript](evidence/rows-replay.txt) · [Tower transcript](evidence/tower-replay.txt) · [Name-set hashes](evidence/dependencies.json) · [Arithmetic audit](../../lean/AuditTameEight.lean)

The ordinary tower has at most eight everywhere-unramified quadratic characters. The standalone arithmetic proof reaches 100,303 declarations versus 77,321 for the previous closed bound of nine generators. The proved witness of three gives the cubic dependence of the window selector. [Three-generator input](../../lean/CyclotomicEight.lean) · [Previous tower measurements](../evidence/arithmetic.json) · [Selector calculation](../../lean/MizusawaSelector.lean)

An independent polynomial calculation tested the primes in $(3,7)$, $(11,23)$ and $(547,727)$ at conductors 16, 32, 64 and 128. The 24 in-range cases reproduce the three sign rows. At conductor 16 the outside prime 31 gives a square for all three units at every prime above it. [Calculation](check_residues.py) · [Output](evidence/residue-samples.txt)

Mizusawa proved the stronger freeness and rank-three theorem in 2010. The `bramble_trace` reading guide gives the sign vectors and an upper bound using norms and class groups. The formal addition here computes the explicit conjugate using Frobenius, evaluates its local Artin symbol and transfers that information to the tame generators of the geometric proof. A search of the earlier family and pinned contemporary proof trees found no matching formal derivation. Equivalent arguments under other names remain possible. [Mizusawa](https://www.numdam.org/item/10.5802/jtnb.707.pdf#page=13) · [Reading guide](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=29) · [Earlier family](https://github.com/leecrossley/prime-window-rh-criterion/tree/6ff0f17a7ce0f1a42ae75d60536a032f90153422/results/geometric-window-descent) · [Prior source inventory](../VERIFICATION.md#prior-work-checked-on-22-november-2026)
