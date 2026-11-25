"""Exact checks of the complete run list, half-length recurrence, and equality matrices."""
from fractions import Fraction
from itertools import groupby, permutations, product


def forms(m, r):
    u, v = m // 2, (m + 1) // 2
    balanced = {(u, v), (v, u)}
    d = r.numerator // r.denominator
    if r.denominator == 1:
        if m >= 2*d + 2:
            return {(a,) + (1,)*(m-a-b) + (b,)
                    for a in (d, d+1) for b in (d, d+1) if a+b <= m}
        if m == 2*d + 1:
            return balanced | {(m,), (d, 1, d)}
        if m in (2*d, 2*d-1):
            return balanced | {(m,)}
        return balanced
    k = d + 1
    if m > 2*k:
        return {(k,) + (1,)*(m-2*k) + (k,)}
    return {(m,)} if u < r < v else balanced


def word_check(m, r):
    """Carry unnormalized integer masses to avoid rational reductions at each edge."""
    a, b = r.numerator, r.denominator
    words = set()
    best = -1
    for directions in product((0, 1), repeat=m):
        p, q = 1, 0
        for direction in directions:
            p, q = (a*p+b*q, a*q) if direction else (a*p, a*q+b*p)
        val = max(p, q)
        if val >= best:
            if val > best:
                best = val
                words.clear()
            words.add((directions, p, q))
    actual = set()
    for word, p, q in words:
        assert word[0] == 0
        assert (p > q) if word[-1] else (q > p)
        actual.add(tuple(len(tuple(g)) for _, g in groupby(word)))
    assert actual == forms(m, r), (m, r, actual)
    maximum = Fraction(best, b**m)
    assert maximum == recurrence_maximum(m, r), (m, r, maximum)
    return maximum


def recurrence_maximum(m, r):
    """Clear denominators in the two-ended recurrence for the unit upper box."""
    a, b = r.numerator, r.denominator
    x, y = 1, 0
    for _ in range(m//2):
        x, y = sorted((a*x, a*y+b*x), reverse=True)
    midpoint = (x*x+y*y if m % 2 == 0 else
                max(a*(x*x+y*y)+b*x*y, 2*a*x*y+b*x*x))
    return Fraction(midpoint, b**m)


def corner_check(n, r):
    """Direct signed Leibniz formula, independent of the row-coefficient identity."""
    positions = [(i, j) for i in range(n) for j in range(i, n)]
    ix = {ij: k for k, ij in enumerate(positions)}
    terms = []
    for perm in permutations(range(n)):
        if any(i > j+1 for i, j in enumerate(perm)):
            continue
        mask = sum(1 << ix[i, j] for i, j in enumerate(perm) if i <= j)
        sub = sum(i == j+1 for i, j in enumerate(perm))
        odd = sum(x > y for i, x in enumerate(perm) for y in perm[i+1:]) % 2
        weight = r.numerator**sub * r.denominator**(n-sub) * (-1)**odd
        terms.append((mask, weight))
    maximum, winners = -1, set()
    for mask in range(1 << len(positions)):
        value = abs(sum(v for term, v in terms if mask & term == term))
        if value >= maximum:
            if value > maximum:
                maximum, winners = value, set()
            winners.add(mask)
    patterns = set()
    for lengths in forms(n-1, r):
        colors = [1]
        for i, length in enumerate(lengths):
            colors.extend([i % 2]*length)
        colors.append(1-colors[-1])
        mask = sum(1 << k for k, (i, j) in enumerate(positions) if colors[i] != colors[j+1])
        patterns.add(mask)
    assert patterns == winners, (n, r, winners ^ patterns)
    for mask in winners:
        signs = {v > 0 for term, v in terms if mask & term == term}
        assert len(signs) == 1
    assert Fraction(maximum, r.denominator**n) == word_check(n-1, r)
    return Fraction(maximum, r.denominator**n), sorted(mask.bit_count() for mask in winners)


def main():
    ratios = sorted({Fraction(a, b) for b in range(1, 4) for a in range(1, 9*b+1)})
    for m in range(2, 13):
        for r in ratios:
            word_check(m, r)
    print(f'Complete maximizing-word sets agree in {11*len(ratios)} exact parameter–length cases.')
    for n in (3, 4, 5):
        for r in map(Fraction, ('1/2', '1', '3/2', '2', '5/2', '3')):
            corner_check(n, r)
    assert corner_check(4, Fraction(2)) == (12, [6, 6, 6])
    assert corner_check(5, Fraction(2)) == (32, [8, 9])
    # Observation 5.1 prints these two order-six matrices at ratio 100.
    source_rows = {('110001', '001110', '001110', '000001', '000001', '000001'),
                   ('111001', '000110', '000110', '000110', '000001', '000001')}
    matrices = set()
    for a, b in forms(5, Fraction(100)):
        c = [1] + [0]*a + [1]*b + [0]
        matrices.add(tuple(''.join(str(int(i <= j and c[i] != c[j+1])) for j in range(6))
                           for i in range(6)))
    assert matrices == source_rows
    assert word_check(5, Fraction(100)) == 10006000000
    headline = recurrence_maximum(99, Fraction(3))
    assert headline == 1713375887978742313831553218518627384145538342870273952
    assert len(forms(99, Fraction(3))) == 4
    print(f'{headline} = max |det A| at (n,s,t) = (100,3,1)')
    print('D_6(100) = 10006000000')
    print('D_4(2) = 12')
    print('D_5(2) = 32')
    print('Upper ones at order five and ratio two: 8 and 9.')


if __name__ == '__main__':
    main()
