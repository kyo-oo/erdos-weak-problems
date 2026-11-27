#!/usr/bin/env python3
"""Exact rational CM Weil-class projector, all p formula; audit p=1..8.

Geometry:
  A/C is a Weil-type abelian 2p-fold with Q(i) multiplication,
  H^1(A,Q) free rank 2p over Q(i) and balanced signature (p,p).
  The genuine algebraic isogeny f=[2+i] acts on the complex sigma
  and bar-sigma eigenspaces of H^1 by lambda=2+i, mu=2-i.

On H^(2p)(A,Q) = exterior^(2p) H^1(A,Q), eigenvalues are
  e_r=lambda^r mu^(2p-r), r=0,...,2p,
  with multiplicities C(2p,r)^2.
The two rank-one pure exterior eigenspaces r=0,2p are Hodge (p,p)
by balanced signature. Their rational sum is the Weil subspace.

Since (lambda/mu)=(3+4i)/5 is NOT a root of unity (its rational
trace is 6/5, not an integer), eigenvalues e_r are distinct.
Each conjugate pair gives
  G_r(t)=t^2-2 Re(e_r)t+5^(2p) in Z[t],
and the central eigenvalue is e_p=5^p.

Let G_0 be the conjugate pair defining the Weil eigenspace, and
N_p(t)=(t-5^p) product_{r=1}^{p-1} G_r(t).
Reduce N_p modulo G_0: N_p ≡ A+B t.
Writing G_0=t^2-2a t+n, n=5^(2p), the polynomial
  L_p(t)=[(A+2aB)-B t]/[A(A+2aB)+n B^2]
is the INVERSE of N_p modulo G_0.
Then P_p(t)=L_p(t) N_p(t) is the unique rational idempotent
projector degree <= 2p with
  P_p(e_r)=1 for r=0,2p and 0 for other r.

This projector is an algebraic-correspondence action because
T=f* is induced by an actual algebraic isogeny, so each T^k
is represented by transpose graph of f^k on A x A.
The polynomial projector is cohomologically idempotent on H^(2p);
it does not by itself produce an algebraic cycle on A for a
prescribed exceptional Weil class. Kernel CI checks below are exact
finite evidence, not a proof of any all-X Hodge surjectivity.
"""
from fractions import Fraction
from math import comb

def mul(a, b):
    z = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            z[i+j] += x*y
    return z

def value(a, x):
    out = 0
    for c in reversed(a):
        out = out*x + c
    return out

def cmul(x, y):
    return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])

def cpow(base, n):
    out = (1,0)
    for _ in range(n):
        out = cmul(out, base)
    return out

def rem_quad(a, lin, constant):
    v = list(a)
    for k in range(len(v)-1, 1, -1):
        c = v[k]
        v[k] = 0
        v[k-1] -= lin*c
        v[k-2] -= constant*c
    return v[:2] + [Fraction(0)]*max(0,len(v)-2)

def audit(p):
    m=2*p
    lam=(2,1); mu=(2,-1)
    eig=[cmul(cpow(lam,r),cpow(mu,m-r)) for r in range(m+1)]
    norm=5**m
    assert eig[p]==(5**p,0)
    assert all(eig[r]==(eig[m-r][0],-eig[m-r][1]) for r in range(m+1))
    assert all(abs(e[0])+abs(e[1])>0 for e in eig)
    assert len(set(eig))==m+1

    quad=lambda r: [Fraction(norm),Fraction(-2*eig[r][0]),Fraction(1)]
    w=quad(0)
    N=[Fraction(-5**p),Fraction(1)]
    for r in range(1,p):
        N=mul(N,quad(r))
    a=eig[0][0]
    rr=rem_quad(N,w[1],w[0])
    A,B=rr[0],rr[1]
    determinant=A*(A+2*a*B)+norm*B*B
    assert determinant!=0
    inv=[(A+2*a*B)/determinant,-B/determinant]
    projector=mul(inv,N)
    assert len(projector)==m+1
    assert rem_quad(projector,w[1],w[0])[:2]==[1,0]
    for r in range(1,p):
        assert rem_quad(projector,*[quad(r)[1],quad(r)[0]])[:2]==[0,0]
    assert value(projector,Fraction(5**p))==0
    M=mul(w,N)
    assert all(v==0 for v in rem_monic(
        [x-y for x,y in zip(mul(projector,projector),
          projector+[0]*(len(mul(projector,projector))-len(projector)))],
        M))
    multiplicities=[comb(m,r)**2 for r in range(m+1)]
    assert sum(multiplicities)==comb(2*m,m)
    assert multiplicities[0]+multiplicities[-1]==2
    return len(projector), len(str(projector[0])), sum(multiplicities)

def rem_monic(a, divisor):
    assert divisor[-1]==1
    out=list(a)
    for k in range(len(out)-1,len(divisor)-2,-1):
        factor=out[k]
        if factor:
            offset=k-len(divisor)+1
            for j,c in enumerate(divisor):
                out[offset+j]-=factor*c
    return out[:len(divisor)-1]

def main():
    for p in range(1,9):
        n, digits, dim=audit(p)
        print(f"p={p}: H^{2*p} dimension={dim}, "
              f"projector degree={n-1}, Weil rank=2, "
              f"constant coefficient digits={digits} [PASS]")
    print("PASS: 8 exact rational polynomial CRT Weil CM projectors.")
    print("PASS: projector idempotence modulo full Hodge spectral polynomial.")
    print("UNIFORM all-p proof: eigenvalues distinct via non-root-of-unity trace 6/5.")
    print("SCOPE: algebraic-correspondence projector; not an algebraic Weil-class witness.")

if __name__ == "__main__":
    main()
