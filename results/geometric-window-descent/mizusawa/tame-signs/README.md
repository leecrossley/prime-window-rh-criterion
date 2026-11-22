# Eight quadratic characters from three cyclotomic units

Let $q\equiv3\pmod 8$ and $d\equiv7\pmod {16}$ be primes. In every field $K_n=\mathbb Q(\zeta_{2^n})$ with $n\ge4$, there are at most eight quadratic characters unramified outside the primes above $q$ and $d$. On the ordinary biquadratic host $\bigcup_{n\ge4}K_n(\sqrt{-q},\sqrt{-d})$, there are at most eight everywhere-unramified quadratic characters. The proof gives the three-generator upper bound used by the geometric window. It uses neither RH nor Mizusawa’s rank theorem. [Finite and infinite Lean statements](../../lean/CyclotomicEight.lean) · [Field identification](../../lean/MizusawaHostField.lean)

## The sign rows

Put $z=\zeta_{2^n}$, $u=1+z+z^{-1}$ and $u_3=1+z^3+z^{-3}$. The Galois automorphism $z\mapsto z^3$ sends $u$ to $u_3$. Complex conjugation fixes both real units. The table gives one bit for each of three pairs of prime ideals. A bit of one means that the reduction at **each** prime in the pair is a nonsquare. The two pairs over $d$ are ordered by the sign of $u$. [Integral units](../../lean/RealCyclotomicUnit.lean) · [Individual prime ideals](../../lean/RealUnitPrimeSigns.lean) · [Counts and Galois action](../../lean/RealUnitSignRows.lean)

| Global unit | Two primes over $q$ | First two over $d$ | Other two over $d$ |
| --- | ---: | ---: | ---: |
| $z$ | 1 | 1 | 1 |
| $u$ | 1 | 1 | 0 |
| $u_3$ | 1 | 0 | 1 |

The computation takes place in the residue fields. Write $U(x)=1+x+x^{-1}$. Then $U(x)x(1-x)=1-x^3$ and $U(x)U(x^3)x^4(1-x)=1-x^9$. Above $q$, some power of Frobenius sends $z$ to $z^3$. The factors $1-z$ and $1-z^3$ have the same quadratic sign, while $z$ is a nonsquare. The first identity gives the negative sign of $U(z)$. The same argument applies to the primitive root $z^3$. [Frobenius congruences](../../lean/RealUnitFrobenius.lean) · [Finite-field proof](../../lean/RealUnitResidueSigns.lean)

Above $d$, a power of Frobenius sends $z$ to $z^{-9}$. The equality $1-z^{-9}=-z^{-9}(1-z^9)$ reverses the quadratic sign because $-1$ is a square and $z$ is a nonsquare. The second identity gives opposite signs for $U(z)$ and $U(z^3)$. The automorphism that cubes $z$ exchanges the two sign classes of prime ideals. Their total size is four, so each has size two. [Proof of the two pairs](../../lean/RealUnitSignRows.lean)

## From the units to inertia

At an odd finite place the principal units are squares. A quadratic character of local units is therefore trivial on square residues and takes a single value on nonsquares. In a finite elementary abelian 2-extension, the local Artin symbol of a nonsquare global unit is trivial exactly when inertia is trivial. Lean proves this equivalence for the actual prime ideal and its completion. [Local Artin symbols and finite inertia](../../lean/LocalTameUnitSigns.lean)

Realise a locally constant quadratic character in the finite Galois field cut out by its kernel. The archived theorem `UpperTheory.V.CF.ineAbs` identifies the image of absolute inertia under restriction with finite inertia. Vanishing on the chosen tame generator detects vanishing on that whole inertia group. These facts identify the value on the tame generator with the quadratic character evaluated on the Artin symbol of $z$. [Upstream inertia theorem](https://github.com/Deicyde/riemann-hypothesis/blob/e7c8972c701d3396947808ab20cc16dc14623d33/src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/ClassFieldRamification/IneAbs.lean#L7) · [Finite character and inertia restriction](../../lean/FiniteRayCharacter.lean) · [Absolute tame sites](../../lean/RayLayerSites.lean) · [Identification used by the bound](../../lean/TameRayBound.lean)

For each pair let $s_i$ be the sum of its two inertia values in $\mathbb F_2$. Global reciprocity applied to $u$, $u_3$ and $z$ gives $s_0+s_1=0$, $s_0+s_2=0$ and $s_0+s_1+s_2=0$. All three pair sums vanish. The pure cyclotomic layer has only the trivial everywhere-unramified quadratic character, so one value per pair determines the character. This gives $2^3=8$ at every level from conductor 16. Quadratic descent and transfer carry that bound to the everywhere-unramified characters of the ordinary host on passing to cofinally many levels. [Global parity](../../lean/FiniteTameParity.lean) · [Character count](../../lean/TameUnitRelations.lean) · [Cofinal descent](../../lean/CofinalRayLayers.lean)

## Prior work

Mizusawa’s 2010 Lemma 4.2 proves a stronger statement. The ordinary class module on the genus-field tower is free of rank three over $\mathbb Z_2$. The reading guide by `bramble_trace` already gives these three sign rows, the finite-level class-number argument and the upper bound they imply. Chems-Eddin studied related cyclotomic units and rank calculations, and Chems-Eddin and Müller computed related class groups and Iwasawa invariants. [Mizusawa, Lemma 4.2](https://www.numdam.org/item/10.5802/jtnb.707.pdf#page=13) · [Reading guide, revision 29](https://rstation.ai/api/v1/posts/uw5cfb_J_Cj7XJO6/attachment?revision=29) · [Chems-Eddin](https://arxiv.org/abs/2001.00865v3) · [Chems-Eddin and Müller](https://arxiv.org/abs/2002.03602v4)

This addition supplies a Lean proof from the cubing and inverse-ninth-power Frobenius congruences through the actual local Artin symbols to the archived window input. The group-theoretic descent, the pure-layer unramified result and global reciprocity are reused. The claim of originality concerns this formal derivation in the family. [Earlier family version](https://github.com/leecrossley/prime-window-rh-criterion/tree/6ff0f17a7ce0f1a42ae75d60536a032f90153422/results/geometric-window-descent) · [Verification and scope](VERIFICATION.md)

## Replay

From `results/geometric-window-descent`, use the compiler, Mathlib and geometric archive paths in the family replay instructions. The first command uses Mathlib alone and the second checks the three-generator bound on the ordinary tower. The Python calculation independently checks 24 prime/conductor combinations and a prime outside the hypotheses. [Pinned inputs](../../REPLAY.md) · [Verification record](VERIFICATION.md)

```sh
python3 replay.py real-unit-rows --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --work "$inputs/runs"
python3 replay.py tame-eight --lean-bin "$lean_bin" --mathlib "$inputs/mathlib4" --archive "$archive" --work "$inputs/runs"
python3 mizusawa/tame-signs/check_residues.py
```
