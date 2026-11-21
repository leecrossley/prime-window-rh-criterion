"""Enclose the mean-square bound on all shorter blocks through 4*10^24."""

import argparse
from fractions import Fraction

from flint import acb, arb, ctx, fmpz


def ball(rational):
    value = Fraction(rational)
    return arb(value.numerator) / value.denominator


def check_kernel():
    # With t=exp(-v), the triangular Gram entry is an ordinary Laplace integral.
    for real_part, frequency in ((0, 0), (0, 21), (Fraction(7, 5), 3)):
        z = acb(ball(real_part), frequency)
        stop = arb(42)
        part = acb.integral(lambda v, _: (-(z+1)*v).exp()*(1-(-v).exp()),
                            0, stop, rel_tol=arb('1e-20'), abs_tol=arb('1e-20'))
        tail = (-stop*(z.real+1)).exp()/(z.real+1)
        radius = arb(0, tail.abs_upper())
        expected = 1/((1+z)*(2+z))
        assert (part+acb(radius, radius)).overlaps(expected)
        assert abs(part-expected) < arb('1e-16')
    print('Triangular Gram integral overlaps its rational kernel at three frequencies.')


def check_actual_odd_block():
    k = 24
    last = int((4*k*arb(k).log().sqrt()).floor().unique_fmpz())
    limit = last**2
    centered = [-arb(1) for _ in range(limit+1)]
    for p in range(2, limit+1):
        if fmpz(p).is_prime():
            logp = arb(p).log()
            power = p
            while power <= limit:
                centered[power] += logp
                power *= p
    log_two = arb(2).log()
    modes = []
    for j in range(1, 65):
        rho = acb.zeta_zero(j)
        assert rho.real == arb(1)/2
        coefficient = (1-2**(-rho))*(2**(1-rho)-1)/(rho*(1-rho))
        modes.append((2*rho-1, coefficient))
    differences = arb(0)
    observed_squares = arb(0)
    for n in range(2, last+1):
        scale = n*n
        total_weight = [arb(0), arb(0)]
        centered_weight = [arb(0), arb(0)]
        diagonal = arb(0)
        for m in range(scale//4+1, scale):
            w = 2-arb(scale)/(2*m) if 2*m <= scale else arb(scale)/m-1
            value = centered[m]*w
            total_weight[m % 2] += w
            centered_weight[m % 2] += value
            if n < 32:
                diagonal += value**2
        if n < 32:
            assert sum(centered_weight, arb(0))**2 < 8*diagonal/9
        if n >= k:
            odd = 2*(centered_weight[0]*centered_weight[1]
                     + total_weight[0]*total_weight[1])/scale
            sample = (odd-log_two**2)/((log_two/2)*(1-arb(4)/scale)*n)
            spectral = 2*sum((coeff*(exponent*arb(n).log()).exp()).real
                             for exponent, coeff in modes)
            differences += (sample-spectral)**2
            observed_squares += sample**2
    rms = (differences/(last-k+1)).sqrt()
    data_rms = (observed_squares/(last-k+1)).sqrt()
    assert rms < arb('0.01') and 5*rms < data_rms
    print('Direct 8/9 margin at every base from 2 through 31.')
    print('K=24 actual calibrated odd-shift RMS', data_rms.str(14))
    print('K=24 arithmetic versus first 64 conjugate zero pairs, RMS difference', rms.str(14))


def strip_bound(start, end, coefficient, row_factor, mesh, log_scale, log_h, ratio):
    """Positive endpoint sums in beta, with the ordinate integral bounded analytically."""
    def moment(A, p, q):
        denominator = 4-p-(q+1)/log_h
        assert denominator > 0
        return 4*(log_h+8)*A*((p-4)*log_h).exp()*log_h**q / denominator

    all_zeros = moment(1/(2*arb.pi()), arb(1), arb(1))
    def count_moment(sigma):
        if sigma < Fraction(5, 8):
            return all_zeros
        s = ball(sigma)
        count = (moment(arb('21.77'), 3*(1-s)/(2-s), (7-5*s)/(2-s))
                 + moment(arb('8.290'), arb(0), arb(2))
                 + moment(arb('147.0'), arb(0), arb(1)))
        # Either published bound suffices when the two intervals overlap.
        return count if count < all_zeros else all_zeros

    left = int(start*mesh)
    right = int(end*mesh)
    assert Fraction(left, mesh) == start and Fraction(right, mesh) == end
    scale_power = ((4*ball(start)-2)*log_scale).exp()
    step = (4*log_scale/mesh).exp()
    total = scale_power*count_moment(start)
    for j in range(left, right):
        total += scale_power*(step-1)*count_moment(Fraction(j, mesh))
        scale_power *= step
    dilation = ball(Fraction(7, 5))
    gram_factor = ratio*dilation**2/(dilation-1)
    return (2*gram_factor*ball(coefficient)**2*ball(row_factor)*total).sqrt()


def check(mesh):
    log_two = arb(2).log()
    mu = log_two/2
    lower = arb(5*10**22)
    upper = arb(4*10**24)
    height = arb(3*10**12)
    log_h = height.log()
    p_max = 4*upper*upper.log().sqrt()+1
    log_scale = (ball(Fraction(7, 5))*p_max).log()
    ratio = ball(Fraction(21, 20))
    assert 4*lower.log().sqrt() > 28
    assert ball(Fraction(28, 27)) < ratio
    initial_max = (4*lower*lower.log().sqrt())**2
    assert 4096*initial_max < height**4*initial_max.log()
    assert arb('0.293')**2 < 8*arb('0.108')/9
    assert arb('0.441')**2 < 8*arb('0.219')/9
    ell = 2*lower.log()
    assert (1-(2*log_two+2)/ell)*(3-4*log_two-arb('0.4')/(ell-2*log_two)**2) > arb('0.219')

    # Chebyshev error on t >= lower^2/4 and interpolation between square samples.
    v = lower**2/4
    relative = arb('0.2')/v.log()**2 + v.log()**2/(v.sqrt()*log_two) + 1/v
    rounding = (3*(2+log_two)+2)*relative
    assert rounding < arb('0.001')
    tail = (log_h+1)/(arb.pi()*height)
    B2 = arb(3).log()-(arb.const_euler()+(4*arb.pi()).log())/3
    low = 3*(B2+4*tail)/arb(2).sqrt()
    calibration = 330/lower**3
    base_error = low + 12*tail + 3/lower + rounding + calibration
    assert base_error < arb('0.132841')
    assert base_error + calibration < arb('0.133')

    # Row comparisons with Re(1/(2+it-rho)); the row sum itself is <= (log t+8)/2.
    for lo, hi, d_bound, row in (
        (Fraction(1, 2), Fraction(4, 5), Fraction(21, 5), Fraction(3, 4)),
        (Fraction(4, 5), Fraction(7, 8), Fraction(17, 5), Fraction(1, 8)),
    ):
        a, b = ball(lo), ball(hi)
        assert (1+2**(-a))*(1+2**(1-a)) < ball(d_bound)
        factor = 2*row
        assert 2-lo <= factor*(4*lo-1)**2
        assert 1 <= 4*factor*(2-hi)
    first = strip_bound(Fraction(1, 2), Fraction(4, 5), Fraction(21, 5),
                        Fraction(3, 4), mesh, log_scale, log_h, ratio)
    second = strip_bound(Fraction(4, 5), Fraction(7, 8), Fraction(17, 5),
                         Fraction(1, 8), mesh, log_scale, log_h, ratio)
    odd_rms = base_error + first + second
    energy = (odd_rms+calibration)**2
    raw_odd_square = (mu*odd_rms)**2
    diagonal = 2*arb('0.219')*((28*lower).log()-1)
    assert energy < arb('20.829') and raw_odd_square < arb('2.502')
    assert diagonal > arb('23.914')
    assert energy < arb(8)*diagonal/9
    print('Normalized non-Gram RMS allowance', base_error.str(15))
    print('Lower real-part strip RMS allowance', first.str(15))
    print('Upper real-part strip RMS allowance', second.str(15))
    print('Calibrated odd-shift RMS upper bound', odd_rms.str(15))
    print('Raw centered odd-shift mean square upper bound', raw_odd_square.str(15))
    print('Prime mean square upper bound', energy.str(15))
    print('Mean diagonal lower bound', diagonal.str(15))
    print('Uniform energy/diagonal upper bound on the new range', (energy/diagonal).str(15))

    check_kernel()
    check_actual_odd_block()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, default=160)
    parser.add_argument('--mesh', type=int, default=4000)
    args = parser.parse_args()
    if args.bits < 128 or args.mesh < 4000 or args.mesh % 40:
        parser.error('use at least 128 bits and a mesh divisible by 40 and at least 4000')
    ctx.prec = args.bits
    print('Arb precision', ctx.prec, 'bits; beta mesh', args.mesh)
    check(args.mesh)
