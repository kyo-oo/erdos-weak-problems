#!/usr/bin/env python3
"""Independent exact original 12-cell GST U/J/M/CM audit.

No Wolfram output consumed. Rebuild from original 4x3 Wave-I definitions:
source shuffle, signed CM mirror, SURVIVE rule, curvature commutator.
Verify both physical Navigation states and Krylov determinants.
All arithmetic exact SymPy integers/rationals, no numerical tolerance.
This does not prove original-X Hodge algebraicity by itself.
"""
import sympy as sp

cells = [(i,k) for i in range(4) for k in range(3)]
idx = {v:i for i,v in enumerate(cells)}
U, J, M = sp.zeros(12), sp.zeros(12), sp.zeros(12)
for row,(i,k) in enumerate(cells):
    U[row,idx[((i+4*k)//3,(i+4*k)%3)]] = 1
    J[row,idx[(3-i,2-k)]] = (1 if i+4*k in [0,1,3,4,5,9] else -1)
    p = (i//2+2*k)%3
    q = (i%2+2*p)%3
    M[row,row] = int(k==2 and p==2) + int(p==2 and q==2)

F0 = U+J+M
F1 = F0+J*M-M*J
z = sp.symbols("z")
p0 = sp.factor(F0.charpoly(z).as_expr())
p1 = sp.factor(F1.charpoly(z).as_expr())
q0 = sp.cancel(p0/(z-2)**2)
q1 = sp.cancel(p1/(z*(z-4)))

assert U**5 == sp.eye(12)
assert J**2 == -sp.eye(12)
assert U*J == J*U
assert q0.subs(z,2) == 1192
assert q1.subs(z,4) == 707131

v = sp.Matrix([int(c in ((0,0),(0,1))) for c in cells])
k0 = sp.Matrix.hstack(*[F0**i*v for i in range(12)])
k1 = sp.Matrix.hstack(*[F1**i*v for i in range(12)])
assert k0.det() == -1149656584000
assert k1.det() == -445265540949

assert sp.factor(p0) == (z-2)**2*q0
assert sp.factor(p1) == z*(z-4)*q1

print({"U5": True, "J2": True, "U_J_commute": True,
       "off_char": str(p0), "on_char": str(p1),
       "off_q_at_2": int(q0.subs(z,2)),
       "on_q_at_4": int(q1.subs(z,4)),
       "off_krylov_det": int(k0.det()),
       "on_krylov_det": int(k1.det()),
       "allPassed": True})
