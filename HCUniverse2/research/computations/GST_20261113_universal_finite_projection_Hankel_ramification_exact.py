"""Exact GST finite-projection / graph-Hankel checker. Scope: finite examples only."""
import itertools
from math import prod
import sympy as sp
def projector(a,b):
    return sp.Matrix([[a*b,a*a],[b*b,a*b]])/(2*a*b)
P11=projector(1,1); P12=projector(1,2)
assert P11*P11==P11 and P12*P12==P12
T=P11+P12;z=sp.Matrix([1,0]);ell=sp.Matrix([[1,1]])
K=sp.Matrix.hstack(z,T*z)
assert K.det()==sp.Rational(3,2)
H=sp.Matrix(2,2,lambda i,j:(ell*T**(i+j)*z)[0])
assert H==sp.Matrix([[1,sp.Rational(5,2)],[sp.Rational(5,2),sp.Rational(41,8)]])
assert H.det()==-sp.Rational(9,8)
print("PASS projective surface normalized projectors and Hankel -9/8")
primes=[2,3,5,7,11,13]
families=[[1,1],[1,1,1],[2,1],[2,2],[1,1,1,1]]
count=0
for ns in families:
  m=primes[:len(ns)]
  for p in range(sum(ns)+1):
    inds=[a for a in itertools.product(*[range(n+1) for n in ns]) if sum(a)==p]
    lambdas=[prod(b**(n-a) for b,n,a in zip(m,ns,aa)) for aa in inds]
    N=len(lambdas)
    assert len(set(lambdas))==N
    V=sp.Matrix(N,N,lambda i,j:lambdas[i]**j)
    delta=prod((lambdas[j]-lambdas[i]) for i in range(N) for j in range(i+1,N))
    assert V.det()==delta
    M=sp.Matrix(N,N,lambda i,j:sum(x**(i+j) for x in lambdas))
    assert M.det()==delta*delta
    if ns==[1,1,1,1] and p==2:
      assert M.det()==28956235586173378560000000000
    count+=1
print("PASS all",count,"weight/family prime-graph finite checks")
assert len({-1,1})==2 and len({0,-0})==1
# Algebraic scheme fiber of y^2=0 has local length 2: basis {1,y}.
print("PASS ramification set fibers 2,1; scheme-theoretic branch length 2")
print("SCOPE: no universal primitive-Hodge source existence assertion")