"""Enclose the constants in the finite-height quartic transfer using Arb."""

from argparse import ArgumentParser
from flint import arb, ctx


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def verify(bits):
    with ctx.workprec(bits):
        H = arb(3 * 10**12)
        d = arb(1) / 1000
        X0 = arb(10**30)
        C = arb(81000)
        pi = arb.pi()
        two = arb(2)
        r = 64 / (pi * (H * d)**3)
        tail_first = 96 / (pi * H**3 * d**2)
        variance_scaled = (2*d).exp() * 12 / (1-r)
        transform_scaled = (H**2*(r+tail_first) + 6*d.exp()) / (1-r)
        require(variance_scaled < arb("12.1"), "variance bound")
        require(transform_scaled < arb("6.1"), "transform bound")
        require(d.exp() < 2 and X0*(-2*d).exp()/2 > 2, "sieve endpoints")

        S = (H.log() + 1) / (pi*H)
        require(arb("0.43")*H.log()/H < (1+(2*pi).log())/(2*pi),
                "zero-count simplification")
        B2 = arb(3).log() - (arb.const_euler() + (4*pi).log())/3
        low = 3/two.sqrt() * (B2 + 4*S)
        high = 12 * arb("6.1") * S / C.sqrt()
        first_prime = (-d).exp() * X0.sqrt()/2
        require(first_prime > 3594641, "Dusart threshold")
        square = (-d).exp() * (3*two.sqrt() - 4 - arb("0.4")/first_prime.log()**2)
        padding = 1/(H.root(3)*C.root(6)) + 1/H
        corner = 9*(2*d).exp() * (arb("12.1")/(4*C.sqrt()) +
                                   arb("12.1").sqrt()*padding)
        require(square > 0, "square reserve sign")
        margin = square - low - high - corner
        require(margin > arb("0.012"), "claimed uniform margin")
        middle_cap = 12/two.sqrt() * S * arb(20).exp()
        require(margin > middle_cap, "zero displacement 20/log(x/2)")
        require(margin*two.sqrt()/12 > arb("0.00155"), "required zero weight")
        require((3*10**12)**4 == 81000 * 10**45, "finite endpoint")
        for name, value in (
            ("H² Var(U) upper bound", variance_scaled),
            ("H² high transform upper bound", transform_scaled),
            ("normalized square lower bound", square),
            ("low-zero loss upper bound", low),
            ("high-zero loss upper bound", high),
            ("middle-corner loss upper bound", corner),
            ("normalized final lower bound", margin),
            ("middle-zero loss under displacement cap", middle_cap),
            ("margin after middle-zero allowance", margin-middle_cap),
        ):
            print(f"{name}: {value.str(22)}")
        print(f"{bits} bits: all comparisons certified")


if __name__ == "__main__":
    p = ArgumentParser(description=__doc__)
    p.add_argument("--bits", type=int, default=160)
    args = p.parse_args()
    verify(args.bits)
