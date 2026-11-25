"""Independent replay from the two source sign sequences, using exact integer arithmetic."""
import csv
import runpy
from fractions import Fraction
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
earlier = runpy.run_path(str(HERE.parent / 'momihara-suda-xiang-determinant/replay.py'))
factor = earlier['factor']
remainder = earlier['remainder']
source_matrices = earlier['source_matrices']
determinant = earlier['determinant']


def cube_passes(q, trace):
    v = (q+1)//2
    r = Fraction(1, v)
    return (Fraction(4928, 10000)-1+r*r/2 <=
            -(1-r)/2+Fraction(trace, 3*v**3)-Fraction(3,8)*(2*v-1)*r*r*(1-r))


class Field:
    """Coefficient tuples modulo a trial-division-certified irreducible polynomial."""
    def __init__(self, p, k):
        self.p, self.k = p, k
        divisors = [c+(1,) for j in range(1, k//2+1) for c in product(range(p), repeat=j)]
        candidates = (self.digits(i)+(1,) for i in range(1,p**k))
        self.modulus = next(f for f in candidates if all(any(remainder(f,d,p)) for d in divisors))
        self.one = self.digits(1)
        n = p**k-1
        primes = [s for s, _ in factor(n)]
        candidates = (self.digits(i) for i in range(2,n+1))
        self.z = next(z for z in candidates if all(self.power(z,n//s) != self.one for s in primes))
        assert self.power(self.z,n) == self.one

    def digits(self, a):
        return tuple(a//self.p**i%self.p for i in range(self.k))

    def add(self, a, b):
        return tuple((i+j)%self.p for i,j in zip(a,b))

    def mul(self, a, b):
        k = self.k
        c = [0]*(2*k-1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i+j] += x*y
        return tuple(x%self.p for x in remainder(c, self.modulus, self.p))

    def power(self, a, n):
        r = self.one
        while n:
            if n%2:
                r = self.mul(r,a)
            a = self.mul(a,a)
            n //= 2
        return r

    def orbit(self, step, n):
        x = self.one
        for _ in range(n):
            yield x
            x = self.mul(x,step)
        assert x == self.one


def gram_trace(a, b, border):
    """Derive the Gram first row by Hamming distances of cyclic shifts of the source rows."""
    m = len(a)
    mask = (1 << m)-1
    def rotate(x, i):
        return ((x << i) | (x >> (m-i))) & mask
    def bits(row):
        return sum((x == 1) << i for i,x in enumerate(row))
    aa, bb = bits(a), bits(b)
    signed = [0]
    for j in range(1,m):
        distance = (aa^rotate(aa,j)).bit_count() + (bb^rotate(bb,j)).bit_count()
        s = m-distance+int(border)
        assert abs(s) == 1
        signed.append(s)
    assert signed[1:] == signed[:0:-1]
    # For j != 0 the two rows have zeros in different positions. Products on
    # their other m-2 coordinates are +/-1. Remove the mismatches at the zeros.
    signs = bits(signed)
    dot = 0
    for j in range(1,m):
        mismatches = (signs^rotate(signs,j)).bit_count() - 2*(signed[j] == 1)
        dot += signed[j]*(m-2-2*mismatches)
    return m*(dot+3*sum(signed)*int(border))


def source_traces(q, p, k):
    e = Field(p, 2*k)
    v, m = (q+1)//2, (q-1)//2
    z, one = e.z, e.one
    w = e.power(z,q+1)
    squares = set(e.orbit(e.mul(w,w),m))
    assert len(squares)==m
    group = list(e.orbit(e.power(z,2*(q-1)),v))
    assert len(set(group))==v
    sign = lambda yes: 1 if yes else -1
    def trace(x):
        return e.add(x,e.power(x,q))
    a = [sign(trace(x) in squares) for x in group]
    torus = []
    for exp in (v, q*q-1-v):
        alpha = e.power(z,exp)
        b = [sign(trace(e.mul(alpha,x)) in squares) for x in group]
        torus.append(gram_trace(a,b,False))
    minus_one = tuple(-x%p for x in one)
    wi = e.power(w,q-2)
    assert e.mul(w,wi)==one
    h = list(e.orbit(e.mul(w,w),m))
    shifted = [[e.add(e.mul(s,x), minus_one) for x in h] for s in (one,wi)]
    bordered = []
    for is_square in (False,True):
        a,b = [[sign(any(y) and (y in squares)==is_square) for y in row] for row in shifted]
        assert (sum(a),sum(b)) == ((-2,0) if is_square else (0,0))
        bordered.append(gram_trace(a,b,True))
    return sorted(torus)+bordered


def main():
    with (HERE/'certificates.tsv').open() as stream:
        table = {int(r[0]):r[1:] for r in list(csv.reader(stream, delimiter='\t'))[1:]}
    orders = [q for q in range(5,2159,4) if len(factor(q))==1]
    assert list(table) == orders
    minima = {}
    for q in orders:
        p,k = factor(q)[0]
        t = source_traces(q,p,k)
        assert t == list(map(int,table[q][:4])), q
        if q>149:
            assert all(cube_passes(q,x) for x in t)
            assert table[q][4:]==['']*4
            continue
        ds = [abs(determinant(m)) for _,m in source_matrices(q,p,k)]
        ds[:2] = sorted(ds[:2])
        assert ds==list(map(int,table[q][4:])), q
        w = 2*q*(q-1)**((q-1)//2)
        for fam,d in zip([4,4,5,6],ds):
            r = Fraction(d,w)
            for lo in (0,30):
                if q+1>=lo:
                    minima.setdefault((lo,fam),[]).append((r,q+1))
    expected = [('841/1053',14),('4/5',6),('13/16',10),
                ('16067122183125/19668469112621',30),('690199704608000/846441320833557',38),
                ('13602934789834170625/16620815899787526144',50)]
    for (key,rs),(value,n) in zip(sorted(minima.items()),expected,strict=True):
        rs.sort()
        assert rs[0] == (Fraction(value),n) and rs[0][0] < rs[1][0]
        assert rs[0][0] < Fraction(81844,100000)
        print(f'order >= {key[0]}, Class ({key[1]}): {value}, attained at n={n}')
    proper = sorted((r,n) for r,n in minima[0,5] if n>6)
    assert proper[0]==(Fraction(441,544),18) and proper[0][0]<proper[1][0]
    assert proper[0][0]<Fraction(81844,100000)
    print('Class (5), nonordinary leaves only: 441/544, attained at n=18')
    print(f'{len(orders)} field sizes covered; {4*sum(q<=149 for q in orders)} full determinants replayed.')

if __name__=='__main__':
    main()
