"""Evaluate the single-zero detector from divisors and from its zeta residue."""

import argparse
from flint import acb, acb_series, arb, ctx


def filtered_moment(x, rho):
    half_rho = rho/2
    n = 8*x
    divisor_count = [0]*(n+1)
    for d in range(1, n+1):
        for j in range(d, n+1, d):
            divisor_count[j] += 1
    # Integrate each of the three Gaussians exactly using upper incomplete
    # gamma. The same argument occurs for h, 2h and 4h in different rows.
    integrals = {}

    def gaussian(j):
        if j not in integrals:
            a = arb.pi()*j*j
            integrals[j] = a**(-half_rho)*acb(a/x**2).gamma_upper(half_rho)/2
        return integrals[j]

    result = acb(0)
    for j in range(1, n+1):
        g_integral = gaussian(j)-3*gaussian(2*j)+2*gaussian(4*j)
        result += (arb(j).log()-divisor_count[j])*g_integral
    # beta=1/2 for this certified zero. For j>8x,
    # int_1^infty u^(-1/2) exp(-pi*(j*u/x)^2) du <= exp(-pi*(j/x)^2).
    q = (-8*arb.pi()/x).exp()
    tail = 12*q**(n+1)*((n+1)/(1-q)+q/(1-q)**2)/arb(x).sqrt()
    radius = arb(0, tail.abs_upper())
    return result+acb(radius, radius)


def check():
    rho = acb.zeta_zero(1)
    assert rho.real == arb(1)/2
    derivative = acb_series([rho, 1], prec=2).zeta()[1]
    assert abs(derivative) > 0
    g_hat = (arb.pi()**(-rho/2)*(rho/2).gamma()*
             (1-2**(-rho))*(1-2**(1-rho))/2)
    residue = -g_hat*derivative
    magnitude = abs(residue)
    assert arb('0.0000275384') < magnitude < arb('0.0000275385')
    print('Magnitude of unnormalized first-zero residue', magnitude.str(14))
    for x, relative_limit in [(32, '0.95'), (64, '0.17'), (128, '0.0275')]:
        moment = filtered_moment(x, rho)
        relative = abs(moment-residue)/abs(residue)
        assert relative < arb(relative_limit)
        print('x =', x, 'relative discrepancy', relative.str(14))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, default=160)
    args = parser.parse_args()
    if args.bits < 96:
        parser.error('use at least 96 bits')
    ctx.prec = args.bits
    print('Arb precision', ctx.prec, 'bits')
    check()
