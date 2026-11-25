"""Exact replay from the MSX sign matrices with Python's standard library.

Use polynomial quotient fields, fraction-free elimination of the full sign
matrix, and triangle counts on its actual Gram blocks. No CAS is needed.
"""
import argparse
import csv
from fractions import Fraction
from itertools import product
from math import isqrt
from pathlib import Path


def factor(n):
    factors = []
    for p in range(2, isqrt(n) + 1):
        if n % p == 0:
            exponent = 0
            while n % p == 0:
                n //= p
                exponent += 1
            factors.append((p, exponent))
    if n > 1:
        factors.append((n, 1))
    return factors


def remainder(poly, monic, p):
    work = list(poly)
    for i in range(len(work) - 1, len(monic) - 2, -1):
        lead = work[i]
        for j, coefficient in enumerate(reversed(monic)):
            work[i-j] = (work[i-j] - lead*coefficient) % p
    return work[:len(monic)-1]


class Field:
    """Elements encoded by polynomial coefficients in base p, constant first."""
    def __init__(self, p, degree):
        self.p = p
        self.order = p**degree
        self.period = self.order-1
        divisors = [coeffs + (1,) for k in range(1, degree//2+1)
                    for coeffs in product(range(p), repeat=k)]
        # Every reducible degree-d polynomial has a factor of degree at most d/2.
        for number in range(1, self.order):
            coeffs = [(number//p**i) % p for i in range(degree)] + [1]
            if all(any(remainder(coeffs, f, p)) for f in divisors):
                self.modulus = coeffs
                break
        else:
            raise ArithmeticError('no irreducible modulus')
        self.digits = [tuple((a//p**i) % p for i in range(degree))
                       for a in range(self.order)]
        primes = [l for l, _ in factor(self.period)]
        z = next(z for z in range(2, self.order) if
                 all(self.raw_power(z, self.period//l) != 1 for l in primes))
        self.exp = [1]
        for i in range(1, self.period):
            self.exp.append(self.multiply_raw(self.exp[-1], z))
        self.log = {a: i for i, a in enumerate(self.exp)}
        assert len(self.log) == self.period and self.multiply_raw(self.exp[-1], z) == 1

    def encode(self, coefficients):
        value = 0
        for c in reversed(coefficients):
            value = value*self.p + c
        return value

    def add(self, a, b):
        return self.encode([(x+y) % self.p for x, y in zip(self.digits[a], self.digits[b])])

    def multiply_raw(self, a, b):
        left, right = self.digits[a], self.digits[b]
        coeffs = [0]*(2*len(left)-1)
        for i, x in enumerate(left):
            for j, y in enumerate(right):
                coeffs[i+j] += x*y
        return self.encode([c % self.p for c in remainder(coeffs, self.modulus, self.p)])

    def raw_power(self, a, n):
        result = 1
        while n:
            if n % 2:
                result = self.multiply_raw(result, a)
            a = self.multiply_raw(a, a)
            n //= 2
        return result

    def generator_power(self, e):
        return self.exp[e % self.period]


def source_matrices(q, p, degree):
    field = Field(p, 2*degree)
    v, m = (q+1)//2, (q-1)//2
    # Exponents of a primitive element in GF(q²). Its (q+1)-th power
    # generates the q-element subfield's multiplicative group.
    gen = field.generator_power
    def sign(yes):
        return 1 if yes else -1

    for direction in (1, -1):
        def trace_square(e):
            t = field.add(gen(e), gen(q*e))
            return sign(t != 0 and field.log[t] % (2*(q+1)) == 0)

        def block(i, j, multiplier):
            return trace_square(direction*(2*(q-1)*(j-i) + multiplier*v))
        matrix = []
        for i in range(v):
            matrix.append([block(i,j,0) for j in range(v)] + [block(i,j,1) for j in range(v)])
        for i in range(v):
            matrix.append([block(j,i,1) for j in range(v)] + [-block(j,i,0) for j in range(v)])
        yield '4', matrix

    minus_one = gen(field.period//2)
    for family, c in [('5', 1), ('6', -1)]:
        def member(i, j, translate):
            value = field.add(gen((q+1)*(2*(j-i)-translate)), minus_one)
            if value == 0:
                return -1
            log = field.log[value]
            assert log % (q+1) == 0
            return sign((log//(q+1)) % 2 == int(family == '5'))

        A = [[member(i,j,0) for j in range(m)] for i in range(m)]
        B = [[member(i,j,1) for j in range(m)] for i in range(m)]
        matrix = [[1]*v + [c]*v]
        matrix.extend([1] + A[i] + [1] + B[i] for i in range(m))
        matrix.append([1]*v + [-c]*v)
        matrix.extend([c] + [c*B[j][i] for j in range(m)] +
                      [-c] + [-c*A[j][i] for j in range(m)] for i in range(m))
        yield family, matrix


def determinant(matrix):
    a = [row.copy() for row in matrix]
    n = len(a)
    denominator, sign = 1, 1
    for k in range(n-1):
        if not a[k][k]:
            i = next((i for i in range(k+1,n) if a[i][k]), None)
            if i is None:
                return 0
            a[k], a[i] = a[i], a[k]
            sign = -sign
        pivot = a[k][k]
        for row in a[k+1:]:
            left = row[k]
            for j in range(k+1,n):
                row[j], rem = divmod(pivot*row[j]-left*a[k][j], denominator)
                assert rem == 0
        denominator = pivot
    return sign*a[-1][-1]


def cubic_trace(matrix):
    n = len(matrix)
    v = n//2
    masks = [sum((x == 1) << i for i,x in enumerate(row)) for row in matrix]
    gram = [[n-2*(a^b).bit_count() for b in masks] for a in masks]
    assert all(gram[i][j+v] == 0 and gram[i][j] == gram[i+v][j+v]
               for i in range(v) for j in range(v))
    assert all(gram[i][j] == n if i == j else abs(gram[i][j]) == 2
               for i in range(v) for j in range(v))
    return 6*sum((gram[i][j]//2)*(gram[j][k]//2)*(gram[k][i]//2)
                 for i in range(v) for j in range(i) for k in range(j))


def check_moment(v, trace):
    r = Fraction(1, v)
    t = Fraction(trace, 3*v**3)
    lhs = Fraction(4701,10000)-1+r*r/2
    rhs = -(1-r)/2+t-Fraction(3,8)*(2*v-1)*r*r*(1-r)
    assert lhs <= rhs


def replay():
    results = []
    for q in range(29, 125, 4):
        factors = factor(q)
        if len(factors) != 1:
            continue
        W = 2*q*(q-1)**((q-1)//2)
        choices = []
        for family, matrix in source_matrices(q, *factors[0]):
            signed = determinant(matrix)
            if q == 29:
                assert (signed > 0) == (family == '6')
            d = abs(signed)
            trace = cubic_trace(matrix)
            assert 5*d >= 4*W
            check_moment((q+1)//2, trace)
            choices.append((family, d, trace))
        # Character labels can exchange under field isomorphism. Order Class 4
        # by decreasing determinant to make the table independent of a generator.
        for family, d, trace in sorted(choices, key=lambda item:(item[0],-item[1])):
            results.append((q, family, d, trace))
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-check', type=Path, required=True)
    args = parser.parse_args()
    results = replay()
    with Path(__file__).with_name('certificates.tsv').open() as f:
        reference = [(int(q), family, int(d), int(t))
                     for q, family, d, t in list(csv.reader(f, delimiter='\t'))[1:]]
    if results != reference:
        raise ValueError('independent source-matrix replay disagrees with certificates.tsv')
    controls = [d for q, _, d, _ in results if q == 29]
    assert len(results) == 56 and len(controls) == 4
    W = 58*28**14
    assert [(2000*d+W)//(2*W) for d in controls] == [844,817,846,823]
    code = ['import Conjectures.NearHadamard', 'open NearHadamard.Small',
            'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
            '#check NearHadamard.problem15', '#print axioms NearHadamard.problem15']
    for name in ['admissible_order30','source_decimals','class4_order30',
                 'class4_inverse_order30','class5_order30','class6_order30']:
        code.append('#print axioms NearHadamard.Controls.' + name)
    for q in sorted({r[0] for r in results}):
        a,b,c,d = [row[3] for row in results if row[0] == q]
        traces = [min(a,b), max(a,b), c, d]
        code.append(f'example : Q{q}.certificateTraces = {traces} := by decide +kernel')
    args.lean_check.write_text('\n'.join(code)+'\n')
    print('14 prime powers, 56 full determinants and cubic traces matched')
    print('Order 30 absolute determinants (Class 4, inverse, Class 5, Class 6)')
    for d in controls:
        print(d)
    print('Published ratios at order 30: 0.844, 0.846, 0.823')


if __name__ == '__main__':
    main()
