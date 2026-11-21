# Which positive dyadic filters can hide a frequency?

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24410856.svg)](https://doi.org/10.5281/zenodo.24410856)

The prime-power deficit of the dyadic tent can be combined at two scales, $aD_\Lambda(y)+bD_\Lambda(2y)$ with positive integers $a$ and $b$. Some combinations are blind to certain frequencies: the factor they introduce on the zero side, $a+b2^s$, vanishes at points of the critical strip, so a zeta zero there could go unseen. This repository says exactly when that happens. The factor has a zero in the open strip when $b<a<2b$, and in no other case.

Of the 91 coprime pairs with $1\le a,b\le12$, 22 are blind in this way. That matters when such sums are used to detect zeros, because a blind combination could hide one.

## Statement

For positive $a,b$, the additional multiplier $a+b2^s$ vanishes at a point of the open critical strip exactly when $b<a<2b$. In that case the missing frequencies are

$$
 s=\log_2(a/b)+i(2j+1)\pi/\log2,\quad j\in\mathbb Z.
$$

Among the 91 coprime pairs $1\le a,b\le12$:

| Position of the extra root | Pairs |
|---|---|
| Inside the open strip, a blind frequency | 22 |
| On a strip boundary | 2 |
| Strictly outside the strip | 67 |

Here, for real $y>0$, $D_\Lambda(y)=2y\log2-\sum_n\Lambda(n)W(n/y)$ is the prime-power deficit, with $\Lambda$ the von Mangoldt function and $W$ the dyadic tent:

$$
 W(t)=
 \begin{cases}
 2(1-1/t) & 1 < t\le2,\\
 4/t-1 & 2 < t < 4,\\
 0 & \text{otherwise}.
 \end{cases}
$$

## Proof

Take the prime-power deficits $aD_\Lambda(y)+bD_\Lambda(2y)$ with positive coprime integers $a,b\le12$. Their prime weights remain nonnegative. On the zero side the extra factor is $a+b2^s$. Its root has modulus $a/b$ in the variable $2^s$, so a frequency in the open strip disappears exactly when $b<a<2b$. The displayed frequencies follow by taking the modulus and argument of $2^s=-a/b$.

A blind frequency identifies where a combination could hide a pole of $\zeta'/\zeta$. The calculation locates roots of the filter. The dyadic RH criterion uses the unfiltered tent, whose multiplier has no interior root. [Dyadic criterion](https://github.com/leecrossley/prime-window-rh-criterion)

The tent-weighted sum $\sum_n\Lambda(n)W(n/y)$ is the three-scale combination $R(4y)-3R(2y)+2R(y)$ of ramps $R(y)=\sum_n\Lambda(n)(y/n-1)_+$, because $`W(t)=(4/t-1)_+-3(2/t-1)_++2(1/t-1)_+`$ for $t>0$. Cancelling the constant and linear parts forces the polynomial in the dilation variable to be a multiple of $(z-1)(z-2)$. The coefficients are therefore unique up to scale.

## Verification

The classification is the written argument above. The executable uses exact integer and rational arithmetic for two checks: it counts the 91 pairs by the criterion $b<a<2b$, and it confirms for each integer $y$ from 1 through 256 that the three-ramp combination reproduces the coefficient of each $\log p$ in the tent-weighted sum. [Exact enumeration and arithmetic comparison](verify.py)

```sh
bash verify-release.sh
```

This checks the [SHA-256 manifest](SHA256SUMS), reruns the arithmetic and compares its output with the [recorded result](evidence/check.txt). It needs Python 3.9 or later and only the standard library. The recorded run used Python 3.9.6 on arm64 macOS. [Latest release](https://github.com/leecrossley/dyadic-filter-zeros/releases/latest)
