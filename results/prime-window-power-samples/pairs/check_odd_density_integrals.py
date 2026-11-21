"""Independent ordinate-integral check of the finite odd-shift bound."""

from flint import arb, ctx


def check():
    ctx.prec = 192
    grid = 6000
    height = arb(3 * 10**12)
    log_h = height.log()
    end = arb(4 * 10**24)
    dilated = arb(7) / 5 * (4 * end * end.log().sqrt() + 1)

    def moment(p, q):
        # In y = log(T), -w'(T) T^p (log T)^q dT becomes
        # (4y + 31) y^q exp(-(4-p)y) dy.
        rate = 4 - p
        z = rate * log_h
        return (4 * z.gamma_upper(q + 2) / rate**(q + 2)
                + 31 * z.gamma_upper(q + 1) / rate**(q + 1))

    total_count = moment(arb(1), arb(1)) / (2 * arb.pi())
    fixed = arb('8.290') * moment(arb(0), arb(2)) + 147 * moment(arb(0), arb(1))

    def bound(i):
        if 8 * i < 5 * grid:
            return total_count
        s = arb(i) / grid
        p, q = 3 * (1-s) / (2-s), (7-5*s) / (2-s)
        by_density = arb('21.77') * moment(p, q) + fixed
        return by_density if by_density < total_count else total_count

    def strip(lo, hi, d, c):
        def power(i):
            return dilated**(4 * arb(i) / grid - 2)

        result = power(lo) * bound(lo)
        for i in range(lo, hi):
            result += (power(i+1) - power(i)) * bound(i)
        # Includes both signs and the half from the logarithmic derivative.
        integral_factor = arb(21) / 20 * arb(49) / 10
        return (integral_factor * d**2 * c * result).sqrt()

    low = strip(grid//2, 4*grid//5, arb(21)/5, arb(3)/2)
    high = strip(4*grid//5, 7*grid//8, arb(17)/5, arb(1)/4)
    # 0.133 encloses the low modes, interpolation and both calibration errors.
    energy = (arb('0.133') + low + high)**2
    ratio = energy / arb('23.914')
    assert energy < arb('20.83') and ratio < arb(8)/9
    print('192-bit independent upper incomplete gamma integration, mesh 6000')
    print('Lower strip RMS upper', low.str(15))
    print('Upper strip RMS upper', high.str(15))
    print('Prime energy upper', energy.str(15))
    print('Energy / diagonal upper', ratio.str(15))


if __name__ == '__main__':
    check()
