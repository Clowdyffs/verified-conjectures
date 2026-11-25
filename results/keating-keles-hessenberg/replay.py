"""Exact arithmetic controls for the Keating–Keleş determinant question."""
from fractions import Fraction
from itertools import product


def comparator(n):
    a = [[2 if i == j + 1 else int(i <= j and (j-i) % 2 == 0)
          for j in range(n)] for i in range(n)]
    a[0][0], a[1][0] = a[1][0], a[0][0]
    a[-1][-2], a[-1][-1] = a[-1][-1], a[-1][-2]
    a[0], a[1] = a[1], a[0]
    for row in a:
        row[-1], row[-2] = row[-2], row[-1]
    return a


def determinant(a):
    """Bareiss elimination with pivoting and checked exact division."""
    b = [row.copy() for row in a]
    previous, sign = 1, 1
    n = len(b)
    for j in range(n-1):
        pivot = next((i for i in range(j, n) if b[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            b[j], b[pivot] = b[pivot], b[j]
            sign = -sign
        for i in range(j+1, n):
            for t in range(j+1, n):
                num = b[j][j]*b[i][t] - b[i][j]*b[j][t]
                b[i][t], remainder = divmod(num, previous)
                assert remainder == 0
            b[i][j] = 0
        previous = b[j][j]
    return sign*b[-1][-1]


def exhaustive(n):
    positions = [(i, j) for i in range(n) for j in range(i, n)]
    a = [[2*int(i == j+1) for j in range(n)] for i in range(n)]
    best = count = 0
    for bits in product((0, 1), repeat=len(positions)):
        for (i, j), value in zip(positions, bits):
            a[i][j] = value
        best = max(best, abs(determinant(a)))
        count += 1
    assert count == 2**(n*(n+1)//2)
    return best


def main():
    prev, current = 12, 32
    a = b = Fraction(1)
    for n in range(4, 65):
        d = determinant(comparator(n))
        assert d == 2**(n-1)*(a+b/2)
        expected = prev if n == 4 else current
        assert d == expected
        if n >= 5:
            prev, current = current, current+4*prev
        if n <= 5:
            assert exhaustive(n) == d
            print(f"D_{n} = {d}")
        a, b = b+a/2, a
    tie = [[1, 1, 0, 1], [2, 0, 1, 0], [0, 2, 1, 0], [0, 0, 2, 1]]
    assert tie != comparator(4) and determinant(tie) == -12
    print("Distinct order-four maximizer has determinant -12.")
    print("Exact source determinants and recurrence agree for orders 4 through 64.")


if __name__ == "__main__":
    main()
