#!/usr/bin/env python3
"""Exact exterior calculation of the actual genus-three secant seed character.

Domain: Q(d)[u]/(u^2+d), d nonzero. No sheaf existence is inferred by code.
The accompanying geometric construction supplies the sheaf; this calculates
the GRR character of its fixed kernel and the explicit exceptional term.
"""
from fractions import Fraction
from math import factorial
import platform


class LaurentQ:
    """Exact sparse Laurent polynomials, reduced by u^2=-d.

    Exponent order is d,u,a,b; the u exponent is always 0 or 1.
    Division is deliberately limited to monomials. No heuristic simplifier,
    floating point, symbolic assumptions, or generic-rank evaluation is used.
    """
    def __init__(self, value=0):
        if isinstance(value, LaurentQ):
            self.terms = value.terms.copy()
        elif isinstance(value, dict):
            self.terms = {e: Fraction(c) for e,c in value.items() if c}
        else:
            self.terms = {(0,0,0,0): Fraction(value)} if value else {}

    @staticmethod
    def variable(index):
        e=[0,0,0,0];e[index]=1
        return LaurentQ({tuple(e):1})

    def __add__(self, other):
        out=self.terms.copy()
        for e,c in LaurentQ(other).terms.items():
            out[e]=out.get(e,Fraction(0))+c
            if not out[e]:del out[e]
        return LaurentQ(out)
    __radd__=__add__

    def __neg__(self):
        return LaurentQ({e:-c for e,c in self.terms.items()})

    def __sub__(self, other):return self+-LaurentQ(other)
    def __rsub__(self, other):return LaurentQ(other)+-self

    def __mul__(self, other):
        out={}
        for e,c in self.terms.items():
            for f,h in LaurentQ(other).terms.items():
                ex=[e[i]+f[i] for i in range(4)]
                pairs,ex[1]=divmod(ex[1],2)
                ex[0]+=pairs
                key=tuple(ex)
                out[key]=out.get(key,Fraction(0))+(-1)**pairs*c*h
                if not out[key]:del out[key]
        return LaurentQ(out)
    __rmul__=__mul__

    def __truediv__(self, other):
        other=LaurentQ(other)
        if len(other.terms)!=1:raise ValueError('Only monomial division is implemented')
        e,c=next(iter(other.terms.items()))
        ex=[-v for v in e]
        if ex[1]==-1:
            ex[1]=1;ex[0]-=1;c=-c
        return self*LaurentQ({tuple(ex):1/c})

    def __rtruediv__(self, other):return LaurentQ(other)/self

    def __pow__(self, n):
        if n<0:return (LaurentQ(1)/self)**(-n)
        out=LaurentQ(1)
        for _ in range(n):out=out*self
        return out

    def __eq__(self, other):return self.terms==LaurentQ(other).terms
    def __bool__(self):return bool(self.terms)
    def has_u(self):return any(e[1] for e in self.terms)

    def __str__(self):
        if not self.terms:return '0'
        parts=[]
        for e,c in sorted(self.terms.items(),reverse=True):
            powers=[v if n==1 else f'{v}^{n}' for v,n in zip(['d','u','a','b'],e) if n]
            parts.append(str(c)+(' * '+' * '.join(powers) if powers else ''))
        return ' + '.join(parts)
    __repr__=__str__


d,u,a,b=[LaurentQ.variable(i) for i in range(4)]


def reduce_q(expr):return LaurentQ(expr)


def add(*polys):
    out = {}
    for p in polys:
        for mask, coeff in p.items():
            out[mask] = out.get(mask, 0) + coeff
    return {m: reduce_q(c) for m, c in out.items() if reduce_q(c) != 0}


def scale(poly, coeff):
    return {m: coeff*c for m, c in poly.items() if coeff*c != 0}


def sign_wedge(left, right):
    return -1 if sum((right & ((1 << i)-1)).bit_count()
                     for i in range(left.bit_length()) if left & (1 << i)) % 2 else 1


def wedge(left, right):
    out = {}
    for m, c in left.items():
        for n, e in right.items():
            if m & n:
                continue
            key = m | n
            out[key] = out.get(key, 0) + sign_wedge(m, n)*c*e
    return {m: reduce_q(c) for m, c in out.items() if reduce_q(c) != 0}


def clean(poly):
    out = {m: reduce_q(c) for m, c in poly.items()}
    return {m: c for m, c in out.items() if c != 0}


def product(polys):
    out = {0: LaurentQ(1)}
    for p in polys:
        out = wedge(out, p)
    return out


def power(poly, n):
    return product([poly]*n)


def homogeneous(poly, codim):
    return {m: c for m, c in poly.items() if m.bit_count() == 2*codim}


def generator(i):
    return {1 << i: LaurentQ(1)}


def assert_zero(poly, name):
    residual = clean(poly)
    assert not residual, (name, residual)
    print('PASS:', name, flush=True)


def one_pair_gaussian():
    # Order x1,x2,w1,w2,y1,y2. The second-factor pullback is a^*:
    # z1 -> -w2, z2 -> w1. Integrate y1*y2 in that orientation.
    x1, x2, w1, w2, y1, y2 = map(generator, range(6))
    thx = wedge(x1, x2)
    thw = wedge(w1, w2)
    cross = add(wedge(x1, w2), scale(wedge(x2, w1), -1))
    raw = product([
        add({0: 1}, scale(wedge(add(x1, y1), add(x2, y2)), a)),
        add({0: 1}, scale(wedge(y1, y2), b)),
        add({0: 1}, wedge(y1, w2)),
        add({0: 1}, scale(wedge(y2, w1), -1)),
    ])
    fiber = (1 << 4) | (1 << 5)
    integrated = {m ^ fiber: c for m, c in raw.items() if m & fiber == fiber}
    expected = add({0: a+b}, scale(thx, a*b), scale(cross, -a),
                   scale(thw, -1), scale(wedge(thx, thw), -a))
    # This identity is polynomial in a,b, independent of the quadratic quotient.
    residual = add(integrated, scale(expected, -1))
    assert all(reduce_q(c) == 0 for c in residual.values()), residual
    print('PASS: one-pair oriented Fourier integral H(a,b)', flush=True)


def block_data(pair):
    x1, x2, w1, w2 = map(generator, range(4*pair, 4*pair+4))
    thx, thw = wedge(x1, x2), wedge(w1, w2)
    cross = add(wedge(x1, w2), scale(wedge(x2, w1), -1))
    return x1, x2, w1, w2, thx, thw, cross


def main():
    print('Python:', platform.python_version(), 'exact standalone Laurent/Fraction engine', flush=True)
    one_pair_gaussian()
    blocks = [block_data(i) for i in range(3)]
    thx = add(*(row[4] for row in blocks))
    thw = add(*(row[5] for row in blocks))
    cross = add(*(row[6] for row in blocks))
    theta = add(scale(thx, d), thw)
    beta = {}
    for s in [1, -1]:
        for v in [1, -1]:
            av, bv = s*u, v*u
            cp, cq = (1-s*u/d)/2, (1-v*u/d)/2
            hblocks = []
            for row in blocks:
                tx, tw, cr = row[4:]
                hblocks.append(add({0: av+bv}, scale(tx, av*bv),
                                   scale(cr, -av), scale(tw, -1),
                                   scale(wedge(tx, tw), -av)))
            beta = add(beta, scale(product(hblocks), -cp*cq))
    beta = clean(beta)
    assert beta.get(0, 0) == 8*d
    print('PASS: actual GRR rank beta_0 = 8*d', flush=True)
    expected_first = add(scale(cross, -4*d), scale(theta, -2*(d-1)))
    assert_zero(add(homogeneous(beta, 1), scale(expected_first, -1)),
                'beta_1 = -4*d*R - 2*(d-1)*theta')

    ch_e = {m: (-1)**(m.bit_count()//2)*c for m, c in beta.items()}
    e1, e2, e3 = [homogeneous(ch_e, k) for k in [1, 2, 3]]
    kappa3 = clean(add(e3, scale(wedge(e1, e2), -1/(8*d)),
                       scale(power(e1, 3), 1/(3*(8*d)**2))))
    omegas = []
    for s in [1, -1]:
        factors = []
        for row in blocks:
            factors.extend([add(scale(row[0], s*u), row[2]),
                            add(scale(row[1], s*u), row[3])])
        om = clean(product(factors))
        omegas.append(om)
        assert_zero(wedge(om, theta), f'Omega_{s} wedge theta = 0')
        assert_zero(wedge(om, add(scale(thx, s*u), scale(cross, Fraction(1,2)))),
                    f'Omega_{s} absorbs the mixed normalization exponential')
    alpha = (d+1)/(4*d)
    ambient = (d-1)*(d+1)**2/(24*d**2)
    expected3 = add(scale(power(theta, 3), ambient),
                    scale(add(*omegas), -alpha))
    assert_zero(add(kappa3, scale(expected3, -1)),
                'kappa_3(E) = ambient*theta^3 - (d+1)/(4d)*(Omega_+ + Omega_-)')
    rational_weil = clean(scale(add(*omegas), -alpha))
    assert rational_weil
    assert all(not c.has_u() for c in rational_weil.values())
    all_w = sum((1 << (4*i+2)) | (1 << (4*i+3)) for i in range(3))
    assert rational_weil[all_w] == -(d+1)/(2*d)
    print('PASS: all-w coefficient = -(d+1)/(2*d), nonzero for every d>0', flush=True)
    print('PASS: exceptional component is rational and nonzero; coefficients:',
          len(rational_weil), flush=True)
    q = (d-1)/(4*d)
    ap, am = 4*d+2*u*(d-1), 4*d-2*u*(d-1)
    coeffs = [reduce_q((ap*(-q-u/(2*d))**j + am*(-q+u/(2*d))**j)
                      /factorial(j)) for j in range(7)]
    assert all(not c.has_u() for c in coeffs)
    assert coeffs[:2] == [8*d, 0]
    assert reduce_q(coeffs[3]-ambient) == 0
    print('Ambient normalized character coefficients j=0..6:')
    for j, c in enumerate(coeffs):
        print(j, str(c))
    print('RESULT: exact source-character identities; geometric sheaf construction and period transport are separate proof steps.')


if __name__ == '__main__':
    main()
