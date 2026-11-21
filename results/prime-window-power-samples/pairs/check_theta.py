"""Interval checks for the theta comparison and its three explicit dilations."""

import argparse
from fractions import Fraction
from math import isqrt

from flint import arb, ctx
from check_pairs import power_base


def ball(value):
    return arb(value.numerator) / value.denominator


def error(radius):
    return arb(0, radius.abs_upper())


def theta_weight(t):
    if t < arb(1)/2:
        u, factor = 1/(4*t), 1/(2*t)
    else:
        u, factor = t, 1
    q = (-arb.pi()*u*u).exp()
    total = sum((q**(k*k)-2*q**(4*k*k) for k in range(1, 12, 2)), arb(0))
    tail = 3*q**169/(1-q)
    return factor*(total+error(tail))


def check_comparison():
    scales = list(map(ball, [Fraction(4, 5), Fraction(1), Fraction(5, 4)]))
    coeff = list(map(ball, [Fraction(-19, 16), Fraction(37, 8), Fraction(-95, 64)]))
    size = sum(map(abs, coeff))
    # The low-tail majorant exp(-pi/(16z^2))/(2z(1-exp(-3pi/(16z^2))))
    # increases on 0 < z <= 5/64.
    z = arb(5)/64
    q = (-arb.pi()/(16*z*z)).exp()
    lower_tail = (size*q/(2*z*(1-q**3)))**2/16
    # For t >= 4, |V(t)| <= 2*size*exp(-pi*(4t/5)^2).
    a = 2*arb.pi()*scales[0]**2
    upper_tail = 4*size**2*(-16*a).exp()/(8*a)
    bins = 4096
    total = arb(0)
    for j in range(bins//16, 4*bins):
        t = arb(2*j+1, 1)/(2*bins)
        if bins//4 <= j < bins//2:
            w = 2-1/(2*t)
        elif bins//2 <= j < bins:
            w = 1/t-1
        else:
            w = arb(0)
        v = sum((c*theta_weight(r*t) for r, c in zip(scales, coeff)), arb(0))
        total += (w-v).abs_upper()**2/bins
    ratio = (lower_tail+total+upper_tail)/(3-4*arb(2).log())
    assert ratio < arb('0.00410')
    print('Upper bound for squared L2 error / squared tent norm', ratio.str(16))


def check_divisors():
    leading = -21*arb(3).zeta()/(4*arb.pi())
    for x in (8, 16, 32, 64):
        n = 8*x
        from_primes, from_divisors = arb(0), arb(0)
        for m in range(1, n+1):
            t = arb(m)/x
            p = power_base(m)
            mangoldt = arb(p).log() if p else arb(0)
            divisors = 2*sum(m % j == 0 for j in range(1, isqrt(m)+1))
            divisors -= isqrt(m)**2 == m
            q = (-arb.pi()*t*t).exp()
            g = q-3*q**4+2*q**16
            from_primes += (mangoldt-1)*theta_weight(t)
            from_divisors += (arb(m).log()-divisors)*g
        q = (-8*arb.pi()/x).exp()
        tail = 12*q**(n+1)*((n+1)/(1-q)+q/(1-q)**2)
        p_value = (from_primes+error(tail))*x*x
        d_value = (from_divisors+error(tail))*x*x
        assert p_value.overlaps(d_value) and p_value < 0
        assert abs(p_value-leading) < arb(100)/x**2
        print('x =', x, 'scaled theta-weighted prime sum', p_value.str(13))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, default=160)
    args = parser.parse_args()
    if args.bits < 96:
        parser.error('use at least 96 bits')
    ctx.prec = args.bits
    print('Arb precision', ctx.prec, 'bits')
    check_divisors()
    check_comparison()
