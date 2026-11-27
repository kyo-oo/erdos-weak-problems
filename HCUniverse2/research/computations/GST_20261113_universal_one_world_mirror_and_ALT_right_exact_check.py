"""Exact finite tests for the GST universal one-world primitive mirror hit.

Not a proof of Hodge algebraicity or the GST single-fold hypothesis.
The dimension-uniform theorem is derived using the rational Lefschetz sl2
decomposition; finite symbolic tests cover sample dimensions.
"""
from math import comb
import sympy as sp

def primitive(d,k):
    a,b=d,d+d%2
    n=d-2*k
    s=(a+b-n)//2
    target=a+b-s+1
    ran=range(max(0,target-b),min(a,target)+1)
    mat=sp.Matrix([[comb(n+1,i-j) if 0<=i-j<=n+1 else 0
                    for j in range(s+1)] for i in ran])
    ker=mat.nullspace()
    assert len(ker)==1
    w=ker[0]
    c=sum(w[i]*w[j]*comb(n,a-i-j)
          for i in range(s+1) for j in range(s+1)
          if 0<=a-i-j<=n)
    assert c!=0
    return a,b,n,s,w,c

for d in range(1,10):
    for k in range(d//2+1):
        a,b,n,s,w,c=primitive(d,k)
        assert a+b-n==2*s and s<=min(a,b)
print('PASS: exact rational projective primitive kernels, dimensions 1..9')

h,t=sp.symbols('h t')
for n in range(13):
    poly=sp.expand(sum((-1)**j*h**j*t**(n-j) for j in range(n+1)))
    assert sp.expand((h+t)*poly-t**(n+1)-(-1)**n*h**(n+1))==0
    assert poly.coeff(t,n)==1
    assert sp.expand(poly**2).coeff(h,n).coeff(t,n)==(-1)**n*(n+1)
print('PASS: +/- telescoping, return and polarization, n=0..12')

h1,h2,u,v=sp.symbols('h1 h2 u v')
H=h1+h2
w0=u-v;w1=u*u-u*v+v*v
sigma=sp.expand(w0*((u+v)**2-H*(u+v)+H**2))
beta=sp.expand((h1-h2)*w1)
assert sigma.xreplace({h1:h2,h2:h1})==sigma
assert beta.xreplace({h1:h2,h2:h1})==-beta
assert sp.expand(sigma*w0).coeff(u,2).coeff(v,2)==-2
assert sp.expand(beta*w1).coeff(u,2).coeff(v,2)==3*(h1-h2)
print('PASS: symmetry obstruction and original-X readouts (-2,+3)')

Li=sp.Matrix([[0,-1,0,0],[1,0,0,0],[0,0,0,-1],[0,0,1,0]])
Lj=sp.Matrix([[0,0,-1,0],[0,0,0,1],[1,0,0,0],[0,-1,0,0]])
Ri=sp.Matrix([[0,-1,0,0],[1,0,0,0],[0,0,0,1],[0,0,-1,0]])
s,r=sp.symbols('s r')
T=Lj+s*Ri+r*Li
e=sp.Matrix([1,0,0,0])
def kry(A): return sp.Matrix.hstack(e,A*e,A**2*e,A**3*e)
assert sp.expand(kry(T).det()+4*s**2*(s**2-r**2-1))==0
F=T+T*T
assert sp.expand(kry(F).det()+4*s**2*(4*s**2+1)*(4*r**2+5)*(s**2-r**2-1))==0
assert kry(F.subs({s:1,r:1})).det()==180
print('PASS: ALT-right mirror second-order cyclic block, det=180')

A=sp.Matrix.hstack(sp.Matrix([1,1,0]),sp.Matrix([1,0,1]))
normal=sp.Matrix([1,-1,-1])
assert normal.T*A==sp.zeros(1,2)
assert normal.dot(sp.Matrix([1,0,0]))**2/normal.dot(normal)==sp.Rational(1,3)
print('PASS: rational algebraic-source subspace has positive distance gap')
print('STATUS: finite checks all pass; universal GST fold operator not constructed')
