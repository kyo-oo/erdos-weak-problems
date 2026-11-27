"""Exact GST+ / ALT- / NULL wave-curvature-cancellation experiment.

All arithmetic is exact SymPy. Geometric claims about Gr(2,4) rely on
standard Schubert/Chern identities and are not established solely by
matrix computations. No assertion about the universal Hodge conjecture.
"""
import sympy as sp

x, y, b = sp.symbols('x y b')
J = sp.Matrix([[0, 1], [-1, 0]])
M = sp.diag(0, 2)
C = J*M - M*J
assert C == sp.Matrix([[0,2],[2,0]])
E12 = J/2 + C/4
E21 = -J/2 + C/4
assert E12 == sp.Matrix([[0,1],[0,0]])
assert E21 == sp.Matrix([[0,0],[1,0]])
Qplus = x*E12 + y*E21
Qminus = x*E12 - y*E21
assert Qplus**2 == x*y*sp.eye(2)
assert Qminus**2 == -x*y*sp.eye(2)

Sigma = sp.diag(1,-1)
D = sp.kronecker_product(Qplus,sp.eye(2)) + sp.kronecker_product(Sigma,Qminus)
assert D**2 == sp.zeros(4)
even, odd = [0,3], [1,2]
d0 = D.extract(odd,even)
d1 = D.extract(even,odd)
assert d0 == sp.Matrix([[-y,x],[y,-x]])
assert d1 == sp.Matrix([[x,x],[y,y]])
assert d0*d1 == sp.zeros(2) and d1*d0 == sp.zeros(2)
assert d0*sp.Matrix([x,y]) == sp.zeros(2,1)
assert d1*sp.Matrix([1,-1]) == sp.zeros(2,1)

# Exact syzygies for the regular sequence (x,y):
# ker d0=R*(x,y)=im d1; ker d1=R*(1,-1);
# im d0=(x,y)*R*(1,-1). Hence H_even=0,H_odd=R/(x,y).
for vx,vy in [(1,1),(1,0),(0,1),(0,0),(2,3)]:
    matrix = D.subs({x:vx,y:vy})
    assert matrix**2 == sp.zeros(4)
    assert matrix.rank() == (0 if (vx,vy)==(0,0) else 2)

# Original two fixed cells from the 12-cell physical GST fold.
T = sp.Matrix([[1,1+2*b],[2*b-1,3]])
F = sp.expand(T+T*T)
seed = sp.Matrix([1,0])
K = sp.Matrix.hstack(seed,F*seed)
assert sp.simplify(K.det()-5*(2*b-1)) == 0
for bv in [0,1]:
    assert K.subs(b,bv).rank()==2
    assert K.subs(b,bv).det()==(-5 if bv==0 else 5)

# For Gr(2,4), a=c2(S*), d=c2(Q) have intersection Gram I2;
# h²=a+d and primitive P=d-a, from Schubert calculus.
ample = sp.Matrix([1,1])
primitive = sp.Matrix([-1,1])
assert (ample.T*primitive)[0]==0
assert (primitive.T*primitive)[0]==2
assert sp.Matrix.hstack(ample,primitive).det()==2

# Physical OFF/ON wave recovery of primitive P from the ONE source a.
assert sp.simplify((-sp.Rational(4,5)*seed-sp.Rational(1,5)*F.subs(b,0)*seed)-primitive) == sp.zeros(2,1)
assert sp.simplify((-2*seed+sp.Rational(1,5)*F.subs(b,1)*seed)-primitive) == sp.zeros(2,1)

print("PASS: original J,M,[J,M] reconstruct two opposite curved waves")
print("PASS: NULL four-channel differential has D^2=0")
print("PASS: source syzygy generators and finite-rank tests")
print("PASS: physical navigation OFF/ON two-step determinants -5/+5")
print("PASS: Gr(2,4) primitive P has pairing 2 using Schubert identities")
print("D0 =",d0.tolist())
print("D1 =",d1.tolist())
print("F_OFF =",F.subs(b,0).tolist())
print("F_ON =",F.subs(b,1).tolist())
