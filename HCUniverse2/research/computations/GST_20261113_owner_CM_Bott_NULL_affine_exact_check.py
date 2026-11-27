"""Exact GST CM/Clifford/Bott/affine tests; not a universal GST proof."""
from itertools import combinations
from math import comb
import sympy as sp
I=sp.I
S1=sp.Matrix([[0,1],[1,0]]);S2=sp.Matrix([[0,-I],[I,0]]);S3=sp.diag(1,-1)
J=sp.Matrix([[0,1],[-1,0]]);M=sp.diag(0,2);C=J*M-M*J
assert S1==C/2 and S2==-I*J and S3==sp.eye(2)-M

def kron(xs):
    z=xs[0]
    for x in xs[1:]:z=sp.kronecker_product(z,x)
    return z
def gamma(p):
    gs=[]
    for j in range(p):
        gs += [kron([S3]*j+[S1]+[sp.eye(2)]*(p-j-1)),
               kron([S3]*j+[S2]+[sp.eye(2)]*(p-j-1))]
    return gs+[kron([S3]*p)]

for p in range(1,4):
    gs=gamma(p);n=2**p;Id=sp.eye(n)
    for g in gs: assert g*g==Id
    for i,j in combinations(range(2*p+1),2):
        assert gs[i]*gs[j]+gs[j]*gs[i]==sp.zeros(n)
    P=Id
    for g in gs:P=P*g
    assert sp.trace(P)==2**p*I**p
    xs=sp.symbols('x0:'+str(2*p+1))
    S=sum((xs[j]*gs[j] for j in range(len(gs))),sp.zeros(n))
    e=(Id+S)/2
    assert sp.simplify(e*e-e-(sum(x*x for x in xs)-1)*Id/4)==sp.zeros(n)
    north={xs[0]:1,**{x:0 for x in xs[1:]}}
    assert sp.trace(e.subs(north))==2**(p-1)
    coeff=sp.factorial(2*p)*sp.trace(P)/2**(2*p+1)
    vol=2*sp.pi**(sp.Rational(2*p+1,2))/sp.gamma(sp.Rational(2*p+1,2))
    charge=sp.simplify(coeff*vol/(sp.factorial(p)*(2*sp.pi*I)**p))
    assert charge==1
    print('PASS Bott p=',p,'size=',n,'rank=',n//2,'normalized charge=',charge)
# Smooth affine U=(P1)^4\D, with D of multidegree (1,1,1,1).
edges=list(combinations(range(4),2))
G=sp.Matrix([[int(j in edge) for j in range(4)] for edge in edges])
beta_sq=sp.Matrix([-2 if edge==(0,1) else 0 for edge in edges])
assert G.rank()==4 and G.row_join(beta_sq).rank()==5
print('PASS projective-origin algebraic beta=(h1-h2)|U has beta^2 != 0')
# Newton smooth idempotent iteration is not finite algebraic exactness.
t=sp.symbols('t');f=lambda x:sp.expand(3*x*x-2*x*x*x)
assert sp.factor(f(t)**2-f(t))==sp.factor(-(t*t-t)**2*(3-2*t)*(2*t+1))
x=t
for k in range(4):
    assert sp.expand(x*x-x)!=0 and sp.degree(x,t)==3**k
    x=f(x)
print('PASS Newton defect-square identity and failure of finite exactness')
print('LIMIT: no alpha-sensitive universal algebraic idempotent solver proved')
