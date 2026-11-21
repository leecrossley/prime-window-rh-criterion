"""Exact rational checks for the taper, and the grid correction."""

from fractions import Fraction
from math import comb


def taper(order, u):
    return sum(comb(2*order, k) * u**k * (1-u)**(2*order-k)
               for k in range(order, 2*order+1))


def check_taper():
    for order in range(2, 13):
        for j in range(17):
            u = Fraction(j, 16)
            value = taper(order, u)
            assert 0 <= value <= 1
            if u > 0:
                assert value > 0
            middle = comb(2*order, order) * (u*(1-u))**order
            assert value + taper(order, 1-u) == 1 + middle
            if 2*u >= 1:
                assert 2*value >= 1
        coefficients = [0]*(2*order+1)
        for k in range(order, 2*order+1):
            for j in range(2*order-k+1):
                coefficients[k+j] += comb(2*order, k)*comb(2*order-k, j)*(-1)**j
        assert not any(coefficients[:order])
        assert coefficients[order] == comb(2*order, order)
    print("binomial taper: 187 rational points, positive central half, exact reflection")


def check_prefix_correction():
    # Two manufactured real modes on an ordinary grid, with exact telescoping
    # for unit step. The actual sampled progression changes from node to node.
    a = 20
    nodes = list(range(80, a*a+1, 8))
    center = Fraction(sum(nodes), len(nodes))
    scale = nodes[-1]-nodes[0]

    def first(n):
        return (n-center)/scale

    variance = sum(first(b)**2 for b in nodes)/len(nodes)

    def second(n):
        return first(n)**2-variance

    def prefix(mode, b, step, residue):
        indices = range(a+(residue-a) % step, b+1, step)
        return sum((n-a+1)*mode(n)-(n-a)*mode(n-1) for n in indices)/len(indices)

    columns = []
    for j, b in enumerate(nodes):
        step = 1+j % 3
        residue = (2*j+1) % step
        for mode in (first, second):
            assert prefix(mode, b, 1, 0) == mode(b)
        columns.append((prefix(first, b, step, residue), prefix(second, b, step, residue)))

    aa = sum(u*u for u, v in columns)
    ab = sum(u*v for u, v in columns)
    bb = sum(v*v for u, v in columns)
    sa = sum(u for u, v in columns)
    sb = sum(v for u, v in columns)
    determinant = aa*bb-ab*ab
    assert determinant > 0 and (sa != 0 or sb != 0)
    c1 = (bb*sa-ab*sb)/determinant
    c2 = (aa*sb-ab*sa)/determinant
    weights = [1-c1*u-c2*v for u, v in columns]
    assert max(abs(w-1) for w in weights) < Fraction(1, 4)
    mass = sum(weights)
    probabilities = [w/mass for w in weights]
    assert min(probabilities) > 0 and sum(probabilities) == 1
    for i in (0, 1):
        values = [pair[i] for pair in columns]
        assert min(values) < 0 < max(values)
        assert sum(w*v for w, v in zip(probabilities, values)) == 0
        assert sum(w*abs(v) for w, v in zip(probabilities, values)) == 2*sum(
            w*max(-v, 0) for w, v in zip(probabilities, values))
    print(f"manufactured integer prefixes: {len(nodes)} nodes, 2 exact zero means,"
          " positive weights, both signs in both columns")


if __name__ == "__main__":
    check_taper()
    check_prefix_correction()
