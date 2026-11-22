"""Replay finite arithmetic identities for the shrinking integer blocks."""

import argparse
from bisect import bisect_right
from fractions import Fraction

if not __debug__:
    raise SystemExit("Square-block certificates require Python assertions. Disable optimisation.")

from flint import acb, arb, ctx, fmpz

from check_discrepancy import primes_through, weight


def block_length(k):
    quotient = arb(k) / arb(k).log().log()
    result = quotient.floor().unique_fmpz()
    if result is None:
        raise ArithmeticError("ambiguous endpoint")
    return int(result)


def equal(left, right):
    error = arb(left) - right
    assert error.contains(0) and error.abs_upper() < arb(2) ** (-ctx.prec // 3), error


def kernel_num(a, b, x, m):
    if not a < m < b:
        return 0
    return (min(x, m) - a) * (b - max(x, m))


def rational_checks():
    for a, b in ((1, 3), (8, 25), (25, 64)):
        for x in range(a, b + 1):
            for m in range(a - 3, b + 4):
                chord = (b - x) * max(a - m, 0) + (x - a) * max(b - m, 0)
                assert chord - (b - a) * max(x - m, 0) == kernel_num(a, b, x, m)
    previous = Fraction(1)
    for m in (8, 16, 32, 64):
        grid_mean = Fraction(sum((min(i, j) * m - i * j)**2
                                 for i in range(m) for j in range(m)), m**6)
        error = abs(grid_mean - Fraction(1, 90))
        assert 0 < error < previous / 2
        previous = error
    limit = 10000
    endpoints = [k + block_length(k) for k in range(16, limit + 1)]
    gaps = {v - u for u, v in zip(endpoints, endpoints[1:])}
    assert gaps == {1, 2}
    print("Exact ramp at interior, exterior and endpoint knots; kernel grid and endpoint gaps passed.")


def check_filter():
    target = acb("0.56", 17)
    competitors = [acb(-3), acb(-1), acb("0.61", 17), acb("0.2", -19)]
    width = arb(1)/128
    weights = [acb(1)]
    for exponent in competitors:
        r = ((exponent-target)*width).exp()
        atoms = [acb(0) for _ in range(len(weights)+1)]
        for i, w in enumerate(weights):
            atoms[i] += w*r/(r-1)
            atoms[i+1] -= w/(r-1)
        weights = atoms
    for exponent, expected in [(target, 1)] + [(z, 0) for z in competitors]:
        transform = sum((w*((exponent-target)*width*i).exp()
                         for i, w in enumerate(weights)), acb(0))
        equal(transform.real, expected)
        equal(transform.imag, 0)
    print("Finite filter retains its target and annihilates both chord modes and two competitors.")


def check_count_integral(a, b, x, positions, median, expected):
    # Integrate the ordinary count error directly between consecutive jumps.
    # Between knots the triangular kernel is affine, and the count is constant.
    cuts = sorted({a, b, x, *positions})
    li_a = arb(a).li()
    value = arb(0)
    tol = arb(2)**(-ctx.prec//2)
    for lo, hi in zip(cuts, cuts[1:]):
        if hi <= x:
            slope, origin = arb(b-x)/(b-a), a
        else:
            slope, origin = -arb(x-a)/(b-a), b
        count = bisect_right(positions, lo)

        def integrand(t, analytic):
            if analytic and not (t.real > 1):
                return acb("nan")
            log_t = t.log(analytic=analytic)
            # Re(t)>1 ensures Re(log(t))>0 on the complex integration disks.
            ordinary_error = count - (log_t.ei() - li_a) - median
            return ordinary_error*slope*(log_t+(t-origin)/t)

        enclosure = acb.integral(integrand, lo, hi, rel_tol=tol, abs_tol=tol)
        assert enclosure.is_finite() and enclosure.imag.contains(0)
        value -= enclosure.real
    equal(value, expected)


def moment_table(atoms, marks):
    # Weighted mass, first moment, and three moments for squared weights.
    ordered = sorted(atoms.items())
    pos = 0
    sums = [arb(0) for _ in range(5)]
    table = {}
    for t in sorted(marks):
        while pos < len(ordered) and ordered[pos][0] <= t:
            m, w = ordered[pos]
            w2 = w*w
            for j, value in enumerate((w, m*w, w2, m*w2, m*m*w2)):
                sums[j] += value
            pos += 1
        table[t] = tuple(sums)
    return table


def original_tent(atoms, marks):
    mass = arb(0)
    reciprocal = arb(0)
    table = {0: (mass, reciprocal)}
    for m in range(1, max(marks) + 1):
        w = atoms.get(m, 0) - 1
        mass += w
        reciprocal += arb(w)/m
        if m in marks:
            table[m] = (mass, reciprocal)
    return table


def tent_at(n, table):
    x = n*n
    c0, r0 = table[x//4]
    c1, r1 = table[x//2]
    c2, r2 = table[x]
    return (2*(c1-c0) - x*(r1-r0)/2 + x*(r2-r1) - (c2-c1))/n


def local_sums(a, b, x, table):
    # On each side of x, G is affine as a function of the prime.
    left = [vx-va for va, vx in zip(table[a], table[x])]
    right = [vb-vx for vx, vb in zip(table[x], table[b])]
    d = b-a
    linear = ((b-x)*(left[1]-a*left[0]) + (x-a)*(b*right[0]-right[1]))/d
    second = ((b-x)**2*(left[4]-2*a*left[3]+a*a*left[2]) +
              (x-a)**2*(right[4]-2*b*right[3]+b*b*right[2]))/(d*d)
    return linear, second


def check_block(k, primes, powers, prime_table, power_table, tent_table):
    h = block_length(k)
    a, b = k*k, (k+h)**2
    d = b-a
    local = [(p, w) for p, w in primes.items() if a < p < b]
    proper = [(m, w) for m, w in powers.items() if a < m < b and m not in primes]
    assert any(m == int_root**2 for m, _ in proper for int_root in range(k+1, k+h))
    positions = sorted(p for p, _ in local)
    counts = [bisect_right(positions, j*j) for j in range(k, k+h+1)]
    li_values = [arb(j*j).li() for j in range(k, k+h+1)]
    prefix_errors = [count - (value-li_values[0]) for count, value in zip(counts, li_values)]
    rms_count = (sum((value*value for value in prefix_errors), arb(0))/(h+1)).sqrt()
    ordered = sorted(prefix_errors)
    assert all(u < v for u, v in zip(ordered, ordered[1:]))
    median = (ordered[h//2] + ordered[(h+1)//2])/2
    deviations = [abs(value-median) for value in prefix_errors]
    abs_mean = sum(deviations, arb(0))/(h+1)
    assert abs_mean < rms_count
    if k <= 25:
        for centre in ordered:
            difference = sum((abs(y-centre) for y in ordered), arb(0))/(h+1) - abs_mean
            assert difference > 0 or difference.contains(0)
    threshold = abs_mean/2
    assert all(d < threshold or d > threshold for d in deviations)
    tail_size = sum(d > threshold for d in deviations)
    assert 0 < tail_size < h+1
    assert abs_mean < threshold + max(deviations)*tail_size/(h+1)
    bin_errors = []
    increment_sum = arb(0)
    for j in range(k, k+h):
        r = j-k
        delta = counts[r+1]-counts[r]
        assert delta == sum(fmpz(m).is_prime() for m in range(j*j+1, (j+1)**2))
        increment_sum += delta - (li_values[r+1]-li_values[r])
        equal(increment_sum, prefix_errors[r+1])
        bin_errors.append((j*j, 2*arb(j).log()*delta-(2*j+1)))
    width = 2*(k+h)-1
    prime_mass = sum((w for _, w in local), arb(0))
    bin_bound = width*(prime_mass+d) + arb(d)*len(local)/(2*k)
    prefix_bound = (arb(b).log() + arb(d)/(4*a))*(
        width*(h+1)*abs_mean + d*width*(1+1/arb(a).log()))
    fvalues, values, diagonals = [], [], []

    def riesz(x):
        mass, first = power_table[x][:2]
        return x*mass - first - arb(x*x)/2

    for n in range(k, k+h+1):
        x = n*n
        f = tent_at(n, tent_table)
        if k <= 48 and n in (k, k+h//2, k+h):
            direct = sum(((powers.get(m, 0)-1)*weight(m, x)
                          for m in range(x//4+1, x)), arb(0))/n
            equal(f, direct)
        fvalues.append(f)
        prime_sum, prime_square = local_sums(a, b, x, prime_table)
        all_sum, _ = local_sums(a, b, x, power_table)
        centre = arb((x-a)*(b-x))/2
        binned = sum((w*kernel_num(a, b, x, m) for m, w in bin_errors), arb(0))/d
        assert abs(prime_sum-centre-binned) < bin_bound
        assert abs(prime_sum-centre) < prefix_bound
        chord = ((b-x)*riesz(a) + (x-a)*riesz(b))/d - riesz(x)
        equal(all_sum-centre, chord)
        raw_powers = sum((w*kernel_num(a, b, x, m) for m, w in proper), arb(0))/d
        equal(all_sum-prime_sum, raw_powers)
        if n in (k, k+h//2, k+h):
            summands = [w*kernel_num(a, b, x, p)/d for p, w in local]
            equal(prime_sum, sum(summands, arb(0)))
            equal(prime_square, sum((s*s for s in summands), arb(0)))
            if k == 24 and n == k+h//2:
                unequal = 2*sum((s*t for i, s in enumerate(summands)
                                  for t in summands[i+1:]), arb(0))
                equal((prime_sum-centre)**2 - prime_square,
                      unequal - 2*centre*prime_sum + centre**2)
                check_count_integral(a, b, x, positions, median, prime_sum-centre)
        values.append((prime_sum-centre)/n**3)
        diagonals.append(prime_square/n**6)
    for endpoint in (values[0], values[-1], diagonals[0], diagonals[-1]):
        equal(endpoint, 0)
    mean_f = sum(fvalues, arb(0))/(h+1)
    energy_f = sum((f*f for f in fvalues), arb(0))/(h+1)
    equal(energy_f, mean_f**2 + sum(((f-mean_f)**2 for f in fvalues), arb(0))/(h+1))
    energy = sum((t*t for t in values), arb(0))/(h+1)
    diagonal = sum(diagonals, arb(0))/(h+1)
    print(f"K={k}, H={h}, interior primes={len(local)}, proper powers={len(proper)}, "
          f"mean F={mean_f.str(9)}, mean F²={energy_f.str(9)}, "
          f"mean T²={energy.str(9)}, repeated-prime term={diagonal.str(9)}, "
          f"count errors/K (rms={(rms_count/k).str(9)}, "
          f"mean distance from median={(abs_mean/k).str(9)})")
    return mean_f


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, choices=(128, 192), default=128)
    ctx.prec = parser.parse_args().bits
    rational_checks()
    check_filter()
    ks = (24, 25, 48, 120, 400)
    squares = {n*n for k in ks for n in range(k, k+block_length(k)+1)}
    limit = max(squares)
    primes = {p: arb(p).log() for p in primes_through(limit)}
    powers = {}
    for p, w in primes.items():
        m = p
        while m <= limit:
            powers[m] = w
            m *= p
    prime_table = moment_table(primes, squares)
    power_table = moment_table(powers, squares)
    tent_table = original_tent(powers, squares | {x//2 for x in squares} | {x//4 for x in squares})
    means = [check_block(k, primes, powers, prime_table, power_table, tent_table) for k in ks]
    assert means[0] < 0 and means[1] > 0
    print(f"All finite cross-checks passed at {ctx.prec} bits.")


if __name__ == "__main__":
    main()
