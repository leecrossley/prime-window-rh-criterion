"""Finite bounds for the dyadic unequal-pair sum. Requires python-flint."""

import argparse
from fractions import Fraction
from math import isqrt

from flint import arb, ctx


def power_base(m):
    if m < 2:
        return 0
    p = next((j for j in range(2, isqrt(m) + 1) if m % j == 0), m)
    while m % p == 0:
        m //= p
    return p if m == 1 else 0


def check_small_bases():
    logs = [arb(p).log() if (p := power_base(m)) else arb(0) for m in range(32**2)]
    worst = arb(-1000)
    for n in range(2, 32):
        x = n*n
        terms = []
        for m in range(x//4 + 1, x):
            weight = 2 - arb(x)/(2*m) if 2*m <= x else arb(x)/m - 1
            terms.append((logs[m] - 1) * weight)
        total = sum(terms, arb(0))
        diagonal = sum((b*b for b in terms), arb(0))
        result = (total*total-diagonal) / x
        assert result < 0
        if n <= 8:
            direct = sum((a*b for i, a in enumerate(terms)
                          for j, b in enumerate(terms) if i != j), arb(0)) / x
            assert direct.overlaps(result) and direct < 0
        worst = worst.max(result)
    print('Thirty small bases passed. Largest individual sum', worst.str(16))


def check_transfer():
    h0 = arb(3 * 10**12)
    small = arb(32**2)
    split = arb(10)**42
    log_split = split.log()
    d = arb(1) / 1000
    variance = arb('12.1')
    kernel = arb('6.1')
    q = arb(3).log() - (arb.const_euler() + (4*arb.pi()).log()) / 3
    zeta_tail = (h0.log() + 1) / (arb.pi()*h0)
    low = 3/arb(2).sqrt() * (q + 4*zeta_tail)
    geom_ratio = (4*(2*d).exp()/small)**2
    trivial = geom_ratio / (3*(1-geom_ratio)*small.sqrt())
    integral = 3 - 4*arb(2).log()
    lattice = 2 / small.sqrt()
    # All terms increase with x or decrease with H, except the trivial term
    # and the lattice discrepancy, for which the lower endpoint was used.
    high_small = 12*kernel*zeta_tail*split.sqrt()/h0**2
    corner_small = (2*d).exp()*(log_split+d)*(
        3*split.sqrt()*variance/(4*h0**2) + 3*variance.sqrt()/h0)
    upper_small = low+trivial+high_small+corner_small+lattice
    lower_small = integral/2 - 5/small
    assert upper_small < arb('0.293') and lower_small > arb('0.108')
    print('Middle range |S| / sqrt(x) upper', upper_small.str(16))
    print('Middle range diagonal / x lower', lower_small.str(16))

    # In the large range H >= 8(x/log(x))^(1/4).
    # x^(-1/12)L^(1/4) and x^(-1/4)(L+d)^2 L^(1/4)
    # decrease for L=log(x) >= log(10^42).
    bt = arb('3.001')
    assert 3*(1+d/log_split) < bt
    assert log_split > 12 and 1/(4*log_split)+2/(log_split+d) < arb(1)/4
    displacement = split**(-arb(1)/12) * log_split**(arb(1)/4) / 8
    padding = 3*(displacement + 1/(h0*split.sqrt()))*variance.sqrt()
    prime_main = (2*d).exp()*bt*3*variance/(4*64)
    inv_height = log_split**(arb(1)/4)/(8*split**(arb(1)/4))
    higher_powers = (4*(5*d/2).exp()*variance.sqrt()*(log_split+d)**2
                     * inv_height/arb(2).log())
    high_coeff = 12*kernel*zeta_tail/64
    upper_large = (prime_main + high_coeff +
                   (low+trivial+bt*(2*d).exp()*padding+higher_powers+
                    2/split.sqrt()) / log_split.sqrt())
    log4 = arb(4).log()
    lower_large = ((1-(log4+2)/log_split)
                   * (integral-arb('0.4')/(log_split-log4)**2))
    assert upper_large < arb('0.441') and lower_large > arb('0.219')
    middle_loss = 12/arb(2).sqrt()*zeta_tail*arb(20).exp()
    assert middle_loss < arb('0.0131') and (upper_large+middle_loss)**2 < lower_large
    assert Fraction(45, 100)**2 - Fraction(21, 100) == -Fraction(3, 400)
    max_k = arb(1_200_000_000_000)
    fraction = 4096*max_k**4 / ((max_k**4).log()*h0**4)
    assert fraction < 1
    print('Large range |S| / sqrt(x log x) upper', upper_large.str(16))
    print('Large range diagonal / (x log x) lower', lower_large.str(16))
    print('Endpoint 4096 K^4 / (log(K^4) H0^4)', fraction.str(16))
    print('Extra allowance for middle zeros in witness test', middle_loss.str(16))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, default=160)
    args = parser.parse_args()
    if args.bits < 96:
        parser.error('use at least 96 bits')
    ctx.prec = args.bits
    print('Arb precision', ctx.prec, 'bits')
    check_small_bases()
    check_transfer()
