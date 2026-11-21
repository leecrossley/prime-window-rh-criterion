"""Enclose the dyadic pair-discrepancy constant and check its normalization."""

import argparse
from math import isqrt

from flint import arb, ctx


def overlap(shift, denominator):
    """Integral of W(t) W(t+u) for positive rational u=shift/denominator."""
    u = arb(shift) / denominator
    pieces = ((denominator // 4, denominator // 2, 2, -arb(1)/2),
              (denominator // 2, denominator, -1, arb(1)))
    result = arb(0)
    for lo, hi, a, b in pieces:
        for other_lo, other_hi, c, d in pieces:
            left = max(lo, other_lo - shift)
            right = min(hi, other_hi - shift)
            if right <= left:
                continue
            first = (arb(right)/left).log()
            second = (arb(right+shift)/(left+shift)).log()
            mixed = (arb(right*(left+shift))/(left*(right+shift))).log()
            result += a*c*arb(right-left)/denominator + b*c*first + a*d*second + b*d*mixed/u
    return result


def check_constant(bins):
    norm = 3 - 4*arb(2).log()
    width = arb(3)/4
    denominator = 8*bins
    integral = arb(0)
    for j in range(bins):
        shift = 3*(2*j+1)
        u = arb(shift)/denominator
        integral += (norm-overlap(shift, denominator))/u
    integral *= width/bins
    # G(u)=(I-F(u))/u has Lipschitz derivative, with constant at most 64.
    error = 64*width**3/(24*bins**2)
    integral += arb(0, error.abs_upper())
    constant = norm*(arb.const_euler()+(3*arb.pi()).log()) - integral
    assert constant > arb('0.36160550') and constant < arb('0.36160555')
    # Separate analytic bound from I-F(u) <= min(I, 7u^2/2).
    elementary = norm*(arb.const_euler()+(3*arb.pi()).log()
                        - arb(1)/2 - (width*(7/(2*norm)).sqrt()).log())
    assert elementary > arb('0.28')
    print('Integral of (I-F(u))/u', integral.str(16))
    print('Certified discrepancy constant', constant.str(16))
    print('Independent analytic lower bound', elementary.str(16))


def primes_through(limit):
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit)+1):
        if sieve[p]:
            count = (limit-p*p)//p + 1
            sieve[p*p::p] = b'\x00' * count
    return [p for p, flag in enumerate(sieve) if flag]


def weight(m, scale):
    if 4*m <= scale or m >= scale:
        return arb(0)
    if 2*m <= scale:
        return 2-arb(scale)/(2*m)
    return arb(scale)/m-1


def finite_check():
    limit = 100000
    primes = primes_through(limit)
    product = arb(1)
    for p in primes[1:]:
        product *= 1-arb(1)/(p-1)**2
    # Remaining product is between 1 - 1/(limit-1) and 1.
    radius = (product/(2*(limit-1))).abs_upper()
    twin_constant = product-radius+arb(0, radius)
    for scale in (16, 64, 256, 1024):
        b = [-arb(1) for _ in range(scale+1)]
        for p in primes:
            if p > scale:
                break
            m = p
            while m <= scale:
                b[m] += arb(p).log()
                m *= p
        w = [weight(m, scale) for m in range(scale+1)]
        terms = [v*y for v, y in zip(b,w)]
        square = sum(terms, arb(0))**2 / scale
        diagonal = sum((v*v for v in terms), arb(0)) / scale
        largest_gap = 3*scale//4
        singular = [2*twin_constant if h%2 == 0 else arb(0) for h in range(largest_gap+1)]
        for p in primes[1:]:
            if p > largest_gap:
                break
            for h in range(p, largest_gap+1, p):
                singular[h] *= arb(p-1)/(p-2)
        model = arb(0)
        direct = arb(0)
        for h in range(1, largest_gap+1):
            q = singular[h]-1
            lo, hi = scale//4+1, scale-h
            lag = sum((w[m]*w[m+h] for m in range(lo,hi)), arb(0))
            model += 2*q*lag/scale
            if scale <= 256:
                direct += 2*sum(((b[m]*b[m+h]-q)*w[m]*w[m+h]
                                 for m in range(lo,hi)), arb(0))/scale
        residual = square-diagonal-model
        if scale <= 256:
            assert residual.overlaps(direct)
        print(f'x={scale}  residual minus centered square', (-diagonal-model).str(12))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, default=160)
    parser.add_argument('--bins', type=int, default=16384)
    options = parser.parse_args()
    if options.bits < 96 or options.bins < 16384:
        parser.error('use at least 96 bits and 16384 midpoint cells')
    ctx.prec = options.bits
    print('Arb bits', ctx.prec, 'midpoint cells', options.bins)
    check_constant(options.bins)
    finite_check()
