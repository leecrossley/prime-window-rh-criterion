"""Outward-rounded constants for the fourth-power certificate in FINITE.md."""

from flint import arb, ctx


def check(bits):
    ctx.prec = bits
    height = arb(3 * 10**12)
    smoothing = arb(1) / 1000
    low, high = arb(10)**42, arb(10)**56
    log_two = arb(2).log()
    tail = (height.log() + 1) / (arb.pi() * height)
    zero_mass = arb(3).log() - (arb.const_euler() + (4 * arb.pi()).log()) / 3
    ratio = 4 * (2 * smoothing).exp() / low
    variance_factor = arb(121) / 10
    root_variance = variance_factor.sqrt() / height

    line = 3 / arb(2).sqrt() * (zero_mass + 4 * tail)
    trivial = ratio**2 / (3 * low.sqrt() * (1 - ratio**2))
    padding = ((arb(3001) / 1000) * (2 * smoothing).exp() * 3
               * (high**(arb(1) / 6) + 1 / low.sqrt()) * root_variance)
    powers = 4 * (5 * smoothing / 2).exp() * (high.log() + smoothing)**2 / log_two * root_variance
    constant = line + trivial + padding + powers
    slope = arb(732) / 10 * tail + (arb(3001) / 1000) * (2 * smoothing).exp() * arb(3) / 4 * variance_factor
    assert constant < arb(155187) / 10**6 < arb(3) / 10
    assert slope < arb(27288598) / 10**6 < arb(55) / 2

    middle = arb(293) / 1000 + arb(2) / 10**8
    small = arb(293) / 1000 + arb(2) / 32
    assert middle < arb(3) / 10 and small < 1
    last_base = arb(57) * 10**11
    last = arb(3) / 10 + arb(55) / 2 * last_base**2 / height**2
    assert last < 100
    print(bits, "bits; constant", constant.str(21), "slope", slope.str(21),
          "middle", middle.str(15), "last square bound", last.str(18))

    root_cap = 69 * 10**19
    assert (26 * 10**9)**2 <= root_cap
    s = arb(root_cap)
    max_ratio = 4 * (2 * smoothing).exp() / 1024
    assert 0 < max_ratio < 1
    trivial_at_start = max_ratio**2 / (3 * 32 * (1 - max_ratio**2))
    smooth_at_end = line + trivial_at_start + (arb(732) / 10) * tail * s / height**2
    unsmooth_at_end = ((2 * smoothing).exp() * ((s**2).log() + smoothing)
                       * (3 * s * root_variance**2 / 4 + 3 * root_variance))
    fifth = smooth_at_end + unsmooth_at_end
    assert fifth < arb(199554261606147) / 10**15 < arb(1) / 5
    print("two-sided fifth majorant", fifth.str(26), "through x =", root_cap**2)

    for m in (arb(10**4), arb(10**6), arb(2 * 10**6)):
        majorant = arb(23) / 10 * (m.log() + 1 / m) + arb(55) / 4 * (m**4 + m**2) / height**2
        budget = 2 * (1 + 2 * m.log())
        assert majorant < budget
        print("m", m.str(9), "mass majorant", majorant.str(17), "budget", budget.str(17))


if __name__ == "__main__":
    for precision in (160, 256):
        check(precision)
