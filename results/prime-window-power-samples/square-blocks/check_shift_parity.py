"""Check the parity split on rational scales and whole square-sample blocks."""

import argparse
from fractions import Fraction

from flint import arb, arb_poly, ctx

from check_discrepancy import primes_through


def tent(m, scale):
    if 4*m <= scale or m >= scale:
        return Fraction(0)
    if 2*m <= scale:
        return 2 - scale / (2*m)
    return scale / m - 1


def as_ball(q):
    return arb(q.numerator) / q.denominator


def check_dyadic_partition():
    scales = {Fraction(j, 13) for j in range(52, 4000)}
    for j in range(2, 18):
        for offset in (-1, 0, 1):
            scales.add(2**j + Fraction(offset, 997))
    for scale in sorted(x for x in scales if x >= 4):
        dyadic = Fraction(0)
        power = 2
        while power <= scale:
            dyadic += tent(power, scale)
            power *= 2
        assert dyadic == 1
    print('Exact rational dyadic partitions:', sum(x >= 4 for x in scales))


def arithmetic_tables(limit):
    cutoff = 1_000_000
    primes = primes_through(max(cutoff, limit))
    product = arb(1)
    for p in primes:
        if 2 < p <= cutoff:
            product *= 1 - arb(1)/(p-1)**2
    # The missing sum of 1/(p-1)^2 is at most 1/(cutoff-1).
    # For a product of factors 1-a, the lost proportion is at most sum(a).
    half_width = (product/(2*(cutoff-1))).abs_upper()
    twin_constant = product * (1 - arb(1)/(2*(cutoff-1))) + arb(0, half_width)
    b = [-arb(1) for _ in range(limit+1)]
    series = [2*twin_constant if h % 2 == 0 else arb(0) for h in range(limit+1)]
    for p in primes:
        if p > limit:
            break
        power = p
        logp = arb(p).log()
        while power <= limit:
            b[power] += logp
            power *= p
        if p > 2:
            factor = arb(p-1)/(p-2)
            for h in range(2*p, limit+1, 2*p):
                series[h] *= factor
    return b, series


def evaluated_scale(scale, b, series, direct=False):
    x = as_ball(scale)
    start = int(scale // 4) + 1
    stop = -((-scale.numerator) // scale.denominator)
    members = range(start, stop)
    w = [as_ball(tent(m, scale)) for m in members]
    z = [b[m]*v for m, v in zip(members, w)]
    even = sum((v for m, v in zip(members, w) if m % 2 == 0), arb(0))
    odd = sum(w, arb(0)) - even
    log_two = arb(2).log()
    mu = log_two/2
    assert abs(even - mu*x/2) < 6/x and abs(odd - mu*x/2) < 6/x
    centered_even = log_two - even
    s = sum(z, arb(0))
    assert centered_even < 0
    centered_odd = sum((value for m, value in zip(members, z) if m % 2), arb(0))
    class_product = 2*(centered_even*centered_odd + even*odd) / x
    # Linear polynomial convolution gives the two actual correlations at each lag.
    # This route to the odd-shift estimator never uses the full linear sum.
    overlap = arb_poly(w) * arb_poly(w[::-1])
    prime_overlap = arb_poly(z) * arb_poly(z[::-1])
    middle = len(w)-1
    odd_error = 2*sum((prime_overlap[middle+h]+overlap[middle+h]
                      for h in range(1, len(w), 2)), arb(0))/x
    assert abs(odd_error-class_product) < arb('1e-24')
    recovered = centered_even + (x*odd_error/2 - even*odd) / centered_even
    assert abs(recovered-s) < arb('1e-24')

    diagonal = sum((value**2 for value in z), arb(0)) / x
    proxy_margin = None
    if scale >= 8:
        estimator = (log_two**2-odd_error)/(mu*(1-4/x))
        assert abs(estimator-s) < 330/x
        assert abs(estimator**2/x-s**2/x) < 3700/x
        proxy_margin = diagonal - estimator**2/x
    model = 2*sum(((series[h]-1)*overlap[middle+h]
                   for h in range(1, len(w))), arb(0))/x
    net = s**2/x - diagonal - model
    even_error = net - odd_error
    if direct:
        sums = [arb(0), arb(0)]
        for h in range(1, len(w)):
            series_value = series[h]-1
            for i in range(len(w)-h):
                sums[h % 2] += z[i]*z[i+h] - series_value*w[i]*w[i+h]
        assert abs(2*sums[1]/x - odd_error) < arb('1e-28')
        assert (2*sums[0]/x).overlaps(even_error)
        assert abs(2*sums[0]/x - even_error) < arb('0.001')
    return net, abs(odd_error)+abs(even_error), -model, diagonal-s**2/x, proxy_margin


def block_check():
    intervals = {}
    for k in (2, 3, 4, 8, 12, 16, 24):
        last = (4*k*arb(k).log().sqrt()).floor().unique_fmpz()
        assert last is not None
        intervals[k] = range(k, int(last)+1)
    limit = max(bases.stop-1 for bases in intervals.values())**2
    b, series = arithmetic_tables(limit)
    for x in (Fraction(4), Fraction(5), Fraction(13, 2), Fraction(79, 8),
              Fraction(31, 2), Fraction(16), Fraction(129, 8), Fraction(421, 5)):
        evaluated_scale(x, b, series, direct=True)
    cache = {}
    for bases in intervals.values():
        for n in bases:
            if n not in cache:
                cache[n] = evaluated_scale(Fraction(n*n), b, series, direct=n<=12)
    for k, bases in intervals.items():
        net, total, threshold, margin = (
            sum((cache[n][j] for n in bases), arb(0))/len(bases) for j in range(4)
        )
        assert total > 0 and net > 0 and net < threshold and margin > 0
        assert (threshold-net).overlaps(margin)
        print(f'K={k} M={bases.stop-1} N={len(bases)} '
              f'net={net.str(9)} unsigned-parity={total.str(9)} '
              f'ratio={(net/total).str(9)} threshold={threshold.str(9)} '
              f'diagonal-minus-energy={margin.str(9)}')
        if k >= 3:
            proxy_margin = sum((cache[n][4] for n in bases), arb(0))/len(bases)
            tolerance = arb(3700)/((k-1)*len(bases))
            assert abs(proxy_margin-margin) < tolerance
            if k == 24:
                assert proxy_margin > tolerance
                print('K=24 odd-shift-only margin after the uniform error:',
                      (proxy_margin-tolerance).str(12))
    print('All odd lags checked by polynomial convolution on every tested scale.')
    print('Direct nested-loop checks: 8 chosen scales and every square from 2^2 to 12^2.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, default=160)
    options = parser.parse_args()
    if options.bits < 128:
        parser.error('use at least 128 bits')
    ctx.prec = options.bits
    print('Arb bits:', ctx.prec)
    log_two = arb(2).log()
    odd_square_threshold = (3-4*log_two)*log_two**2/2
    assert odd_square_threshold > arb('0.0546302168993')
    assert odd_square_threshold < arb('0.0546302168995')
    print('Leading odd-shift square threshold:', odd_square_threshold.str(16))
    mu = log_two/2
    error_coefficient = 36+2*log_two**2+12*mu+24*log_two/4+arb(144)/16
    assert 4*log_two < 3 and error_coefficient < 55
    assert 2*55/mu < 330 and 6*330+arb(330)**2/64 < 3700
    print('Parity expansion uniform error coefficient:', error_coefficient.str(16))
    check_dyadic_partition()
    block_check()
