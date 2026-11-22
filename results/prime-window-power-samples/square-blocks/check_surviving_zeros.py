"""Interval and integer checks for the moving exceptional-zero sum."""

import argparse
from fractions import Fraction
from itertools import product

if not __debug__:
    raise SystemExit("Square-block certificates require Python assertions. Disable optimisation.")

from flint import acb, arb, ctx, fmpz


def last_sample(height):
    # For integer n the moving cutoff is inside the verified range exactly
    # when n^397 <= height^1000.
    power = fmpz(height) ** 1000
    last_n = int(power.root(397))
    assert last_n**397 <= power < (last_n + 1)**397
    return last_n


def height_endpoint(height):
    last_n = last_sample(height)
    def all_samples_covered(k):
        lhs = 16 * arb(k)**2 * arb(k).log()
        rhs = (last_n + 1)**2
        assert lhs < rhs or lhs > rhs
        return lhs < rhs

    lo, hi = 2, last_n
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if all_samples_covered(mid):
            lo = mid
        else:
            hi = mid
    assert all_samples_covered(lo) and not all_samples_covered(hi)
    # Solve 16 k^2 log(k) = (last_n+1)^2 independently. The binary search
    # above explicitly rules out an integral boundary.
    y = arb(last_n+1)**2/8
    real_boundary = (y.lambertw()/2).exp()
    assert real_boundary.floor().unique_fmpz() == lo
    print(f"Height {height}, last n {last_n}, last full block K {lo}")
    return lo, last_n


def count_allowance(height):
    # A right-half zero with positive ordinate uses a separate reflected
    # left-half zero. Hence the total on the right for both signs is at
    # most the ordinary positive-ordinate count in this shell.
    t = arb(height)
    main_term = t/(2*arb.pi())*((t/(2*arb.pi())).log()-1)
    error = arb("0.1038")*t.log() + arb("0.2573")*t.log().log() + arb("9.3675")
    return int((main_term+error-12_363_153_437_138).floor().unique_fmpz())


def finite_shell(h, known, extended):
    count = count_allowance(h+5000)
    k0, j0 = known
    k1, j1 = extended
    coefficient = ((1+1/arb(2).sqrt())*(1+arb(2).sqrt())
                   * arb(j1)**(arb(3)/4)/arb(h)**2)
    fraction = arb(j1-j0)/(j0+2-k1)
    lower_diagonal = (3-4*arb(2).log())/2-5/arb(k0+1)**2
    ratio = fraction*(count*coefficient)**2/lower_diagonal
    assert count == 21_411 and fraction > 0 and lower_diagonal > 0
    assert ratio < arb("0.509")
    print(f"Extra 5000 height units, at most {count} right-half terms, "
          f"upper bound on whole-block energy/diagonal {ratio.str(12)}")


def partitioned_shell(h, known, extended, step):
    k0, j0 = known
    k1, j1 = extended
    assert (k0+1)**2 > 10**42 and 45_000 % step == 0
    log_x = 2*arb(k0+1).log()
    log_four = arb(4).log()
    lower_diagonal = ((log_x-log_four-2) *
                      (3-4*arb(2).log()-arb("0.4")/(log_x-log_four)**2))
    assert lower_diagonal > 30
    denominator = (j0+2-k1)*lower_diagonal
    assert denominator > 0
    factor = (1+1/arb(2).sqrt())*(1+arb(2).sqrt())/arb(h)**2
    previous = j0
    energy = arb(0)
    for delta in range(step, 45_001, step):
        last = last_sample(h+delta)
        count = count_allowance(h+delta)
        assert last > previous and count > 0
        bound = count*factor*arb(last)**(arb(3)/4)
        energy += (last-previous)*bound**2
        previous = last
    assert previous == j1
    ratio = energy/denominator
    assert ratio < (arb("0.462") if step == 125 else arb(1)/2)
    print(f"Extra 45000 height units, {45_000//step} bins, "
          f"diagonal per sample > 30, upper ratio {ratio.str(12)}")


def tent(z):
    return (1 - 2**(-z)) * (2**(1-z) - 1) / (z*(1-z))


def projection_check():
    # Synthetic exponents. The target occurs twice, a neighbor has almost
    # the same ordinate, and another has exactly the same ordinate.
    target = acb(arb(3)/4, 11)
    modes = [
        (target, 2),
        (acb(arb(3)/4, 11 + arb(1)/10**5), 1),
        (acb(arb(2)/3, 11), 1),
        (acb(arb(13)/16, -9), 3),
        (acb(arb(5)/8, 130), 1),
        (acb(arb(7)/10, -210), 2),
    ]
    lam = 2*target-1
    atoms = []
    for index, (z, _) in enumerate(modes[1:]):
        delta = 2*z - 1 - lam
        if index < 3:
            t = arb(1)/1024
            r = (delta*t).exp()
            weights = (r/(r-1), -1/(r-1))
        else:
            t = arb.pi()/abs(delta.imag)
            r = (delta.real*t).exp()
            weights = (r/(1+r), 1/(1+r))
            assert weights[0] > 0 and weights[1] > 0
        assert abs(sum(weights)-1) < arb("1e-22")
        assert abs(weights[0]+weights[1]*(delta*t).exp()) < arb("1e-22")
        atoms.append((t, weights))

    x = arb(8192)
    total = acb(0)
    for choices in product((0, 1), repeat=len(atoms)):
        v = arb(0)
        weight = acb(1)
        for bit, (t, weights) in zip(choices, atoms):
            v += bit*t
            weight *= weights[bit]
        value = sum(m*tent(z)*((2*z-1)*(x.log()+v)).exp() for z, m in modes)
        total += weight*(-lam*v).exp()*value
    expected = 2*tent(target)*(lam*x.log()).exp()
    assert abs(total/expected-1) < arb("1e-13")
    print(f"32-atom model, relative projection error < 1e-13, "
          f"support width {sum(t for t, _ in atoms).str(10)}")


def moving_jump_check():
    # Decide inclusion as an integer inequality, even at an exact cutoff.
    nu = arb(397)/1000
    def included(n, ordinate_to_1000):
        return ordinate_to_1000 <= n**397

    exact_n = 2**1000
    exact_ordinate = (2**397)**1000
    assert not included(exact_n-1, exact_ordinate)
    assert included(exact_n, exact_ordinate) and included(exact_n+1, exact_ordinate)
    locations = [(5, 8, 1, 1), (7, 8, 9, 3), (2, 3, 10, 2),
                 (3, 4, 11, 1), (5, 8, 12, 1), (4, 5, 13, 2)]
    terms = []
    for top, bot, g, m in locations:
        z = acb(arb(top)/bot, g)
        terms.append((g**1000, 2*z-1, m*tent(z)))
    assert terms[0][0] == 1**397

    def subtotal(n, prefix):
        return sum(2*(c*(lam*arb(n).log()).exp()).real for _, lam, c in prefix)

    crossings = 0
    for n in range(150, 800):
        length = 1 + n % 9
        b = n+length
        common = [t for t in terms if included(n, t[0])]
        new = [t for t in terms if included(b, t[0]) and not included(n, t[0])]
        lhs = abs(subtotal(b, common+new)-subtotal(n, common))
        drift = sum(2*abs(c*lam)*arb(n)**(lam.real-1)*length for _, lam, c in common)
        edge = sum(2*abs(c)*arb(b)**lam.real for _, lam, c in new)
        assert lhs < drift+edge
        if new:
            crossings += 1
            for t, _, _ in new:
                assert arb(n)**nu < arb(t).root(1000) < arb(b)**nu
    assert crossings > 0
    print(f"650 two-endpoint variation bounds, {crossings} moving-edge cases")


def main(bits):
    ctx.prec = bits
    print(f"Arb precision {bits} bits")
    baseline = height_endpoint(3_000_000_000_000)
    exact = height_endpoint(3_000_175_332_800)
    extended = height_endpoint(3_000_175_337_800)
    assert extended[0] > exact[0] > baseline[0]
    finite_shell(3_000_175_332_800, exact, extended)
    farther = height_endpoint(3_000_175_377_800)
    assert farther[0] > extended[0]
    for step in (250, 125):
        partitioned_shell(3_000_175_332_800, exact, farther, step)
    projection_check()
    moving_jump_check()
    for s in (Fraction(51, 100), Fraction(2, 3), Fraction(3, 4), Fraction(7, 8)):
        p = 3*(1-s)/(2-s)
        a = (1-p)/p
        assert (1+3*a)/(2+3*a) == s and 0 < p < 1
    assert 2*Fraction(7, 8)-1-2*Fraction(397, 1000) == -Fraction(11, 250)
    assert (5-Fraction(3, 2)/Fraction(397, 1000))/3 == Fraction(485, 1191)
    print("Exact density-width inversion, cutoff exponent and height transfer verified")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--bits", type=int, default=192)
    main(parser.parse_args().bits)
