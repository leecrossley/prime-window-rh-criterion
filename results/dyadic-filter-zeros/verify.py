"""Exhaust the stated filter family, then compare arithmetic weights exactly.

The latter check stores the rational coefficient of each log(p) separately.
It does not use approximations to primes, logarithms, or zeta zeros.
"""

from collections import Counter
from fractions import Fraction
from math import gcd


if not __debug__:
    raise SystemExit("Run with Python assertions enabled.")


def candidate_map(limit):
    groups = Counter()
    for a in range(1, limit + 1):
        for b in range(1, limit + 1):
            if gcd(a, b) != 1:
                continue
            # For a D(y) + b D(2y) the extra root of the symbol is -a/b.
            # Its radius lies in (1, 2) exactly when b < a < 2b.
            if b < a < 2 * b:
                groups["has an interior blind frequency"] += 1
            elif a == b or a == 2 * b:
                groups["extra root on a strip boundary"] += 1
            else:
                groups["extra root strictly outside the strip"] += 1
    print("Coprime positive pairs with a,b from 1 to", limit)
    for key, value in sorted(groups.items()):
        print(f"  {value:3} {key}")
    print("Total", sum(groups.values()))
    return groups


def tent(y, n):
    if y < n <= 2 * y:
        return 2 * (1 - Fraction(y, n))
    if 2 * y < n < 4 * y:
        return Fraction(4 * y, n) - 1
    return Fraction(0)


def prime_powers(bound):
    prime = [True] * (bound + 1)
    prime[:2] = [False, False]
    for p in range(2, bound + 1):
        if prime[p]:
            for multiple in range(2 * p, bound + 1, p):
                prime[multiple] = False
            n = p
            while n <= bound:
                yield p, n
                n *= p


def check_arithmetic(bound):
    powers = list(prime_powers(4 * bound))
    for y in range(1, bound + 1):
        ramp = Counter()
        band = Counter()
        for p, n in powers:
            if n > 4 * y:
                continue
            t = Fraction(y, n)
            ramp[p] += max(4 * t - 1, 0) - 3 * max(2 * t - 1, 0) + 2 * max(t - 1, 0)
            band[p] += tent(y, n)
        assert ramp == band
    print(f"Exact coefficients agree for each integer y from 1 through {bound}.")


if __name__ == "__main__":
    groups = candidate_map(12)
    assert groups == {
        "has an interior blind frequency": 22,
        "extra root on a strip boundary": 2,
        "extra root strictly outside the strip": 67,
    }
    check_arithmetic(256)
