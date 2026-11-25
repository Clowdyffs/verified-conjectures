"""Regenerate the exact finite certificate using FLINT's Conway fields and resultants."""
import csv
import sys
from flint import fmpz, fmpz_poly, fq_default_ctx

def cube_passes(q, trace):
    """Clear the denominators in the log comparison by multiplying by 15000 v³."""
    v = (q + 1) // 2
    return 108*v**3 + 625*((9 - 6*v)*(v - 1) + 8*trace) >= 0

def generator(field):
    """Find a generator and verify its order, also for nonprime base fields."""
    size = int(field.order())
    p = int(field.characteristic())
    divisors = [int(l) for l, _ in fmpz(size - 1).factor()]
    for code in range(1, size):
        digits = []
        value = code
        while value:
            value, digit = divmod(value, p)
            digits.append(digit)
        a = field(digits)
        if all(a ** ((size - 1) // l) != 1 for l in divisors):
            return a
    raise ArithmeticError("missing primitive element")


def orbit(step, length):
    a = step ** 0
    for _ in range(length):
        yield a
        a *= step
    assert a == 1


def signed_rows(p, k, q):
    v = (q + 1) // 2
    field = fq_default_ctx(p, 2*k)
    z = generator(field)
    alpha = z**v
    row = []
    for t in orbit(z**(2*(q-1)), v):
        x = alpha*t
        tr = x + x**q
        row.append(0 if tr == 0 else (-1 if tr**(v-1) == 1 else 1))
    yield '4', row
    yield '4', [-x for x in row]

    field = fq_default_ctx(p, k)
    w = generator(field)
    row = [0 if x == 1 else (1 if (x-1)**(v-1) == 1 else -1)
           for x in orbit(w*w, v-1)]
    yield '5', row
    yield '6', [-x for x in row]


def reference():
    for q in range(5, 2159, 4):
        factors = fmpz(q).factor()
        if len(factors) != 1:
            continue
        p, k = map(int, factors[0])
        traces = []
        ds = []
        for family, row in signed_rows(p, k, q):
            m = len(row)
            poly = fmpz_poly(row)**3
            t = m*sum(int(poly[i]) for i in (0, m, 2*m))
            if family != '4':
                t += 3*m*sum(row)
            traces.append(t)
            if q<=149:
                gram = fmpz_poly([q+1]+[2*x for x in row[1:]])
                if family=='4':
                    modes = fmpz_poly([-1]+[0]*(m-1)+[1])
                    det = modes.resultant(gram)
                else:
                    modes = fmpz_poly([1]*m)
                    det = modes.resultant(gram)*((q-1)**2 if family=='5' else q*q+2*q+5)
                ds.append(int(det))
        traces[:2] = sorted(traces[:2])
        if q <= 149:
            ds[:2] = sorted(ds[:2])
        elif not all(cube_passes(q, t) for t in traces):
            raise ValueError(f'Insufficient cubic certificate at q={q}')
        yield [q, *traces, *(ds or ['']*4)]


if __name__ == '__main__':
    writer = csv.writer(sys.stdout, delimiter='\t', lineterminator='\n')
    writer.writerow('q torus_min_cube torus_max_cube five_cube six_cube torus_min_det torus_max_det five_det six_det'.split())
    writer.writerows(reference())
