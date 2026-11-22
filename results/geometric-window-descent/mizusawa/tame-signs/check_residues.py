#!/usr/bin/env python3
"""Check residue rows independently in F_p[X]/(X^(N/2)+1)."""
from collections import Counter


def product(left, right, p):
    m = len(left)
    result = [0] * m
    for i, a in enumerate(left):
        if a:
            for j, b in enumerate(right):
                degree = i + j
                if degree < m:
                    result[degree] += a * b
                else:
                    result[degree - m] -= a * b
    return [value % p for value in result]


def power(base, exponent, p):
    result = [1] + [0] * (len(base) - 1)
    while exponent:
        if exponent & 1:
            result = product(result, base, p)
        base = product(base, base, p)
        exponent //= 2
    return result


def trimmed(poly):
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def gcd_degree(left, right, p):
    left, right = trimmed(left[:]), trimmed(right[:])
    while right:
        inverse = pow(right[-1], -1, p)
        while len(left) >= len(right):
            shift = len(left) - len(right)
            scale = left[-1] * inverse
            for i, b in enumerate(right):
                left[i + shift] = (left[i + shift] - scale * b) % p
            trimmed(left)
        left, right = right, left
    return len(left) - 1


def counts(n, p):
    N = 2**n
    m = N // 2
    degree = 1
    while pow(p, degree, N) != 1:
        degree += 1
    z = [0, 1] + [0] * (m - 2)
    one = [1] + [0] * (m - 1)
    modulus = one + [1]

    def unit(a):
        return [(i + j + k) % p for i, j, k in
                zip(one, power(z, a, p), power(z, N - a, p))]

    exponent = (p**degree - 1) // 2
    tests = [power(element, exponent, p) for element in (z, unit(1), unit(3))]
    rows = Counter()
    for a in (-1, 1):
        for b in (-1, 1):
            for c in (-1, 1):
                # The product of the three projectors is nonzero exactly on this joint sign class.
                selector = one
                for sign, values in zip((a, b, c), tests):
                    selector = product(selector, [(i + sign*j) % p for i, j in zip(one, values)], p)
                total = m - gcd_degree(modulus, selector, p)
                count, remainder = divmod(total, degree)
                if remainder:
                    raise ValueError((n, p, total, degree))
                if count:
                    rows[a, b, c] = count
    return rows


if __name__ == "__main__":
    for n in range(4, 8):
        for q, d in [(3, 7), (11, 23), (547, 727)]:
            for p, expected in [(q, {(-1, -1, -1): 2}),
                                (d, {(-1, -1, 1): 2, (-1, 1, -1): 2})]:
                found = counts(n, p)
                if found != expected:
                    raise ValueError((n, p, found, expected))
                print(f"n={n} p={p} {sorted(found.items())}")

    # At conductor 16 the prime 31 is outside both congruence classes.
    control = counts(4, 31)
    if control != {(1, 1, 1): 4}:
        raise ValueError((4, 31, control))
    print(f"control n=4 p=31 {sorted(control.items())}")
