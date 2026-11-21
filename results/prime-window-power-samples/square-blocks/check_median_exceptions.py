"""Interval checks for an ordinary prime-count median on blocks of squares."""

import argparse
from itertools import product
from math import isqrt

from flint import acb, arb, ctx, fmpz

from check_discrepancy import primes_through


def unique_floor(value):
    integer = value.floor().unique_fmpz()
    if integer is None:
        raise ArithmeticError("undetermined integer endpoint")
    return int(integer)


def length(k):
    return unique_floor(arb(k)/arb(k).log().log())


def last_true(left, right, predicate):
    assert predicate(left) and not predicate(right)
    while right-left > 1:
        mid = (left+right)//2
        if predicate(mid):
            left = mid
        else:
            right = mid
    return left


def johnston_limit(coefficient):
    height = 3*10**12
    c = arb(coefficient)
    def inside(n):
        lhs = (c*n)**2
        rhs = height**2*(2*arb(n).log())**3
        assert lhs < rhs or lhs > rhs
        return lhs < rhs
    last = last_true(16, 10**17, inside)
    root = (-(arb(3)/2)*(-(c/height)**(arb(2)/3)/3).lambertw(-1)).exp()
    assert unique_floor(root) == last
    return last


def relative_margin(k, factor, multiplier):
    # Upper bound M / (K log² K) if n_end <= factor*K and
    # M <= multiplier*n_end*log(n_end).
    return multiplier*factor*(arb(k).log()+factor.log())/arb(k).log()**2


def finite_certificate():
    n1 = johnston_limit("1.19")
    n10 = johnston_limit("0.117")
    assert n1 == 1_471_729_207_270_810 and n10 == 16_551_346_706_300_673
    def centre_index(k):
        return k+(length(k)+1)//2
    last = last_true(16, n1+1, lambda k: centre_index(k) <= n1)
    assert last == 1_290_008_597_927_572
    assert centre_index(last) == n1 and centre_index(last+1) == n1+1
    assert last+length(last) == 1_653_449_816_614_048 < n10
    assert 10**15+length(10**15) <= n1
    assert (2*10**6)**2 < 1101*10**23
    assert arb(10**6).log().log() > arb(5)/2
    assert arb(10**15).log().log() > arb(10)/3
    r1 = relative_margin(52, arb(2), 1/(2*arb.pi()))
    r2 = relative_margin(10**6, arb(7)/5, 4)
    r3 = relative_margin(10**15, arb(13)/10, 22)
    assert max(r1, r2, r3) < 1
    print(f"Johnston last square roots {n1} and {n10}.")
    print(f"Last certified K {last}; H={length(last)}, upper sample {last+length(last)}.")
    print(f"Uniform threshold ratios on the three analytic ranges: "
          f"{r1.str(10)}, {r2.str(10)}, {r3.str(10)}.")


def prefix_counts(k, h):
    # Sieve only the interval used by this block. No primes before K² enter.
    lower = k*k+1
    upper = (k+h)**2
    primes = primes_through(isqrt(upper))
    endpoints = [n*n for n in range(k+1, k+h+1)]
    result = [0]
    total = 0
    index = 0
    while lower <= upper:
        stop = min(upper+1, lower+2**20)
        flags = bytearray([1])*(stop-lower)
        for p in primes:
            first = max(p*p, ((lower+p-1)//p)*p)
            if first < stop:
                flags[first-lower::p] = bytes((stop-1-first)//p+1)
        cursor = 0
        while index < h and endpoints[index] < stop:
            nxt = endpoints[index]-lower+1
            total += flags.count(1, cursor, nxt)
            result.append(total)
            cursor = nxt
            index += 1
        total += flags.count(1, cursor)
        lower = stop
    assert len(result) == h+1 and result[-1] == total
    return result


def median_range(values):
    ordered = sorted(values)
    assert all(x < y for x, y in zip(ordered, ordered[1:]))
    return ordered[(len(ordered)-1)//2], ordered[len(ordered)//2]


def check_data(k, direct=False):
    h = length(k)
    counts = prefix_counts(k, h)
    if direct:
        for j in range(k, k+h):
            assert counts[j-k+1]-counts[j-k] == sum(fmpz(m).is_prime()
                                                      for m in range(j*j+1, (j+1)**2))
    li0 = arb(k*k).li()
    values = [total-(arb(n*n).li()-li0) for n, total in zip(range(k, k+h+1), counts)]
    lo, hi = median_range(values)
    threshold = k*arb(k).log()**2
    for m in (lo, hi):
        assert all(abs(value-m) < threshold for value in values)
    if k < 52:
        return
    width = int(fmpz(k).root(8))
    assert width**8 <= k < (width+1)**8
    full = len(values)//width
    tiles = [values[j*width:(j+1)*width] for j in range(full)]
    spans = [max(tile)-min(tile) for tile in tiles]
    anchors = [tile[0] for tile in tiles]
    biggest = max(spans)
    assert biggest < arb(k)**(arb(127)/128)
    # Test the lifting inequality with active exceptions, at an observed scale.
    c = sum(median_range(anchors))/2
    errors = sorted(abs(y-c) for y in values)
    t = errors[3*len(errors)//4]
    spacing = sorted(spans)[len(spans)//3]
    bad_samples = sum(abs(y-c) > t+spacing for y in values)
    bad_tiles = sum(v > spacing or v.overlaps(spacing) for v in spans)
    bad_anchors = sum(abs(y-c) > t or abs(y-c).overlaps(t) for y in anchors)
    assert bad_samples <= (len(values)%width) + width*(bad_tiles+bad_anchors)
    print(f"K={k}, N={len(values)}, spacing={width}, largest within-cell range "
          f"{biggest.str(8)}, full median exceptions=0.")


def check_selected_tiles():
    k = 256
    width = 2
    a, b = k*k, (k+width)**2
    primes = [m for m in range(a+1, b) if fmpz(m).is_prime()]
    li_a = arb(a).li()
    continuous = [arb(0), len(primes) - (arb(b).li()-li_a)]
    for count, prime in enumerate(primes):
        before = count-(arb(prime).li()-li_a)
        continuous.extend((before, before+1))
    # Between successive jumps pi-li is strictly decreasing.
    continuous_span = max(continuous)-min(continuous)
    counts = prefix_counts(k, width)
    sampled = [count-(arb(j*j).li()-li_a) for count, j in zip(counts, range(k,k+width+1))]
    assert max(sampled)-min(sampled) < continuous_span < arb(k)**(arb(127)/128)
    print(f"Continuous prime-count error range at [{k}, {k+width}] "
          f"from {len(primes)} prime jumps: {continuous_span.str(9)}.")
    for k in (65_536, 390_625):
        width = int(fmpz(k).root(8))
        counts = prefix_counts(k, width)
        li_a = arb(k*k).li()
        sampled = [count-(arb(j*j).li()-li_a) for count,j in zip(counts, range(k,k+width+1))]
        span = max(sampled)-min(sampled)
        assert 0 < span < arb(k)**(arb(127)/128)
        print(f"Selected grid interval [{k}, {k+width}] contains {counts[-1]} primes "
              f"between its squared endpoints, integer-sample range {span.str(8)}.")


def finite_geometry():
    # Exercise even medians, ties, remainders, and a slowly moving array
    # whose local errors are small but whose global median has many outliers.
    seen = 0
    for values in product((-5, 0, 5), repeat=7):
        anchors = values[:6:2]
        middle = sorted(anchors)[1]
        good_groups = []
        for j, a in enumerate(anchors):
            pair = values[2*j:2*j+2]
            if max(pair)-min(pair) <= 1 and abs(a-middle) <= 1:
                good_groups.append(pair)
        if 4*len(good_groups) <= len(values):
            continue
        seen += 1
        median = sorted(values)[3]
        assert abs(median-middle) <= 2
        assert all(abs(v-median) <= 4 for pair in good_groups for v in pair)
    assert seen > 0
    for count in (6, 7):
        for values in product((-5, 0, 5), repeat=count):
            if 2*values.count(0) > count:
                ordered = sorted(values)
                assert ordered[(count-1)//2] == ordered[count//2] == 0
    ramp = list(range(1000))
    assert all(max(ramp[i:i+8])-min(ramp[i:i+8]) < 10 for i in range(0,1000,8))
    assert sum(abs(2*v-999) > 50 for v in ramp) == 950
    print(f"Exhaustive majority and grid tests passed, including {seen} strict-majority grids.")


def maximal_inequalities():
    exponents = [acb("1.1", 3), acb("1.6", 78), acb("1.5", 78), acb("1.7", -95)]
    coeffs = [acb(1), acb("0.4", "0.3"), acb("-0.6", "0.1"), acb("0.1", "0.9")]
    def value(u):
        return sum((a*(z*u).exp() for a, z in zip(coeffs, exponents)), acb(0))
    def integral(u, width, weights):
        result = acb(0)
        for a, z in zip(weights, exponents):
            for b, w in zip(weights, exponents):
                q = z+w.conjugate()
                result += a*b.conjugate()*(q*u).exp()*(q*width).expm1()/q
        assert result.imag.contains(0) and result.real > 0
        return result.real
    derivative = [a*z for a, z in zip(coeffs, exponents)]
    for j in range(12):
        u, width = arb(j)/21, arb(1)/21
        mass, energy = integral(u,width,coeffs), integral(u,width,derivative)
        samples = [value(u+width*r/16) for r in range(17)]
        assert all(abs(z)**2 < mass/width+2*(mass*energy).sqrt() for z in samples)
        assert all(abs(z-w)**2 < width*energy for z in samples for w in samples)
    print("Complex Gram integrals passed both local inequalities on 12 cells.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, choices=(128, 192), default=128)
    ctx.prec = parser.parse_args().bits
    finite_certificate()
    for k in range(16, 52):
        check_data(k, direct=True)
    print("Every block 16 <= K <= 51 passed for both endpoints of its median interval.")
    for k in (256, 4096, 6561):
        check_data(k, direct=k==256)
    check_selected_tiles()
    finite_geometry()
    maximal_inequalities()
    print(f"All checks passed at {ctx.prec} bits.")


if __name__ == "__main__":
    main()
