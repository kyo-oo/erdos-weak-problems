#!/usr/bin/env python3
"""Exact CM Weil projector for every imaginary-quadratic d>0 on H^4.

T is pullback by the genuine isogeny [d+1+u], u^2=-d.
Weil eigenfactor G_W(t)=t^2-2*r*t+q^4, where
 m=d+1, q=m^2+d, r=m^4-6*d*m^2+d^2.
Mixed factor G_M(t)=t^2-2*s*t+q^4, s=q*(m^2-d).
Central eigenvalue is q^2. Let N(t)=(t-q^2)*G_M(t).

The CRT rational algebraic projector is
 P(t)=N(t)*(A+2*r*B-B*t)/D,
 A=2*(s-r)*q^4, B=2*(r-s)*(2*r-q^2),
 D=A*(A+2*r*B)+q^4*B^2
  =256*d^3*(d+1)^2*q^6*(3*d^2+5*d+3)^2 > 0.

This script performs independent *exact rational arithmetic*.
The uniform identities are proved algebraically in the mathematical
record, with the reduction and inverse verified in existing GST Lean.
No arbitrary target algebraic-cycle preimage is assumed.
"""
from fractions import Fraction as F

def add(a,b):
    o=[F(0)]*max(len(a),len(b))
    for i,c in enumerate(a): o[i]+=c
    for i,c in enumerate(b): o[i]+=c
    return o
def neg(a): return [-x for x in a]
def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return out
def mod_monic(a,b):
    assert b[-1]==1
    out=list(a)
    for i in range(len(out)-len(b),-1,-1):
        k=out[i+len(b)-1]
        for j,coeff in enumerate(b): out[i+j]-=k*coeff
    return out[:len(b)-1]
def test(d):
    d=F(d); assert d>0
    m=d+1; q=m*m+d; r=m**4-6*d*m*m+d*d
    s=q*(m*m-d); n=q**4
    gw=[n,-2*r,F(1)]
    gm=[n,-2*s,F(1)]
    nc=mul([-q*q,F(1)],gm)
    A=2*(s-r)*n
    B=2*(r-s)*(2*r-q*q)
    remainder=mod_monic(nc,gw)
    assert remainder==[A,B]
    D=A*(A+2*r*B)+n*B*B
    Dfactor=256*d**3*m**2*q**6*(3*d*d+5*d+3)**2
    assert D==Dfactor and D>0
    numerator=mul(nc,[A+2*r*B,-B])
    P=[x/D for x in numerator]
    assert mod_monic(add(P,[-F(1)]),gw)==[F(0),F(0)]
    assert mod_monic(P,gm)==[F(0),F(0)]
    def val(p,x):
        acc=F(0)
        for a in reversed(p): acc=acc*x+a
        return acc
    assert val(P,q*q)==0
    full=mul(gw,nc)
    assert mod_monic(add(mul(P,P),neg(P)),full)==[F(0)]*5
    return len(P)-1,D
def main():
    samples=[F(i) for i in range(1,65)]
    samples+=[F(1,2),F(3,7),F(5,9),F(100,3),F(13,41)]
    for d in samples:
        degree,den=test(d)
        assert degree==4 and den>0
    print(f"PASS: {len(samples)} exact rational Weil projector checks")
    print("PASS: identity on Weil quadratic, zero on central/mixed sectors")
    print("PASS: polynomial idempotence in complete H^4 spectral quotient")
    print("PASS: positive denominator for tested d; uniform factorization proves all d>0")
    print("SCOPE: genuine algebraic correspondence; nonzero source still required.")
if __name__=="__main__":
    main()
