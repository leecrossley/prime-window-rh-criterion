"""Check the finite theorem with rational arithmetic and no external packages."""

from fractions import Fraction as F
from math import comb, factorial, isqrt


def log_small(x):
    """Enclose log(x) by the atanh series, for 1 <= x <= 2."""
    assert 1 <= x <= 2
    z = (x-1)/(x+1)
    lower = 2*sum(z**j/j for j in range(1, 60, 2))
    return lower, lower + 2*z**61/(61*(1-z*z))


def log_bounds(x):
    x = F(x)
    count = 0
    while x > 2:
        x /= 2
        count += 1
    lo, hi = log_small(x)
    lo2, hi2 = log_small(F(2))
    return lo + count*lo2, hi + count*hi2


def atan_bounds(x):
    upper = sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(13))
    return upper-x**27/27, upper


def constants():
    H = 3*10**12
    C = 81000
    d = F(1,1000)
    pi_lo = F(314159,100000)
    a, _ = atan_bounds(F(1,5))
    _, b = atan_bounds(F(1,239))
    assert pi_lo < 16*a-4*b   # Machin's formula
    # Trapezoid bounds for the integral of 1/t on each [j,j+1] give
    # H_n - log(n) - gamma <= (1/n - 0)/2 after summing the tail.
    gamma_lo = sum(F(1,n) for n in range(1,1025)) - log_bounds(1024)[1] - F(1,2048)
    B2_hi = log_bounds(3)[1] - (gamma_lo + log_bounds(4*pi_lo)[0])/3
    sqrt2_lo = F(141421,100000)
    sqrtC_lo = F(2846,10)
    assert sqrt2_lo**2 < 2 and sqrtC_lo**2 < C
    assert 14420**3 < H and F(13,2)**6 < C
    assert F(3479,1000)**2 > F(121,10)
    logH_hi = log_bounds(H)[1]
    assert F(43,100)*logH_hi/H < F(1,7)   # 1/(2*pi) > 1/7
    assert 16*atan_bounds(F(1,5))[1]-4*atan_bounds(F(1,239))[0] < F(7,2)
    S_hi = (logH_hi+1)/(pi_lo*H)
    mass = 64/(pi_lo*(H*d)**3)
    first = 96/(pi_lo*H**3*d**2)
    assert 12/((1-2*d)*(1-mass)) < F(121,10)
    assert (H**2*(mass+first)+6/(1-d))/(1-mass) < F(61,10)

    log_min = 15*log_bounds(10)[0]-log_bounds(2)[1]-d
    assert (1-d)*10**15/2 > 3594641 and log_min > 33
    reserve_lo = (1-d)*(3*sqrt2_lo-4-F(2,5)/log_min**2)
    low_hi = 3*(B2_hi+4*S_hi)/sqrt2_lo
    high_hi = 12*F(61,10)*S_hi/sqrtC_lo
    padding_hi = 1/(14420*F(13,2)) + F(1,H)
    loss_hi = 9/(1-2*d)*(F(121,10)/(4*sqrtC_lo) + F(3479,1000)*padding_hi)
    margin_lo = reserve_lo-low_hi-high_hi-loss_hi
    # Test the printed decimal floor as an integer inequality.
    assert margin_lo > F(12,1000)
    exp_one_hi = sum(F(1,factorial(j)) for j in range(14)) + F(15,14*factorial(14))
    middle_hi = 12*S_hi*exp_one_hi**20/sqrt2_lo
    assert margin_lo > middle_hi and margin_lo*sqrt2_lo/12 > F(155,100000)
    print("Rational lower bound on the margin, rounded down to millionths:",
          (margin_lo*10**6).__floor__(), "/ 1000000")
    assert H**4 == C*10**45 and C < 17**4
    max_k = isqrt(isqrt(10**45))
    assert max_k**4 <= 10**45 < (max_k+1)**4
    print("Largest covered integer K for square samples:", max_k)
    print("Required zero weight > 0.00155; displacement exceeds 20/log(x/2).")


def four_uniforms(t, order):
    """Density of four independent U[-1,1] variables, with derivatives."""
    numerator = sum((-1)**j*comb(4,j)*max(t+4-2*j,0)**(3-order)
                    for j in range(5))
    return F(numerator, 16*factorial(3-order))


def kernel_and_hinges():
    zero = F(0)
    assert four_uniforms(zero,0) == F(1,3)
    assert -four_uniforms(zero,2)/four_uniforms(zero,0) == F(3,4)
    for i in range(16,65):
        for sign in (-1,1):
            for order in (0,1):
                assert four_uniforms(sign*F(i,4),order) == 0
    checks = 0
    for m in range(1,18):
        for j in range(1, 16*m+5):
            x = F(j,4)
            if x < m or x > 4*m:
                direct = 0
            elif x <= 2*m:
                direct = x/m-1
            else:
                direct = 2-x/(2*m)
            coeffs = ((m,F(1,m)), (2*m,F(-3,2*m)), (4*m,F(1,2*m)))
            assert direct == sum(c*max(x-y,0) for y,c in coeffs)
            for h in (F(-2,3),F(3,5)):
                for y,_ in coeffs:
                    gap = max(x+h-y,0)-max(x-y,0)-h*(x>y)
                    if h >= 0:
                        integral = max(h-(y-x),0) if y>=x else 0
                    else:
                        integral = max(-h-(x-y),0) if y<x else 0
                    assert gap == integral and gap >= 0
                    checks += 1
    print("Four-uniform kernel support and variance identities verified.")
    print("Exact one-sided hinge checks:", checks)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O so every rational check is active.")
    constants()
    kernel_and_hinges()
