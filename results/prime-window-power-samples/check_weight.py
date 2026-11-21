"""Compare the tent, its signed ramps and their interval slopes in exact arithmetic."""
from fractions import Fraction


def tent(x, m):
    if x / 4 < m <= x / 2:
        return 2 - x / (2 * m)
    if x / 2 < m < x:
        return x / m - 1
    return 0


def ramp(x, m):
    return max(0, x / m - 1)


def interior_slope(x, m):
    if m < x < 2 * m:
        return Fraction(1, m)
    if 2 * m < x < 4 * m:
        return Fraction(-1, 2 * m)
    return 0


def check():
    count = 0
    for j in range(1, 257):
        left, right = Fraction(j, 2), Fraction(j + 1, 2)
        middle = (left + right) / 2
        for m in range(1, 131):
            value = tent(left, m)
            ramps = ramp(left, m) - 3 * ramp(left / 2, m) + 2 * ramp(left / 4, m)
            if value != ramps or not 0 <= value <= 1:
                raise ArithmeticError(f"weight mismatch at x={left}, m={m}")
            if tent(right, m) - value != (right - left) * interior_slope(middle, m):
                raise ArithmeticError(f"interval slope mismatch at x={middle}, m={m}")
            count += 1
    print(f"Exact tent, signed-ramp and interval-slope checks passed for {count} pairs.")


if __name__ == "__main__":
    check()
