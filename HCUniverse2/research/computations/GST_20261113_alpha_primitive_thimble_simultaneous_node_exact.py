"""Exact independent algebra audit: arbitrary-X alpha-directed GST primitive carry
and simultaneous-node local relation obstruction.
This code verifies universal polynomial instances and the full m=3 rational model;
geometric theorems are proved in companion LaTeX, not inferred from samples.
"""
import sympy as sp

x, z = sp.symbols('x z')
for r in range(0, 31):
    phi = sum((-1)**j * x**j * z**(r-j) for j in range(r+1))
    assert sp.expand((x+z)*phi-z**(r+1)-(-1)**r*x**(r+1)) == 0
    # pi_* selects the coefficient of z^r
    assert sp.expand(phi).coeff(z, r) == 1
print('PASS alpha-carry polynomial and original-X projection for r=0..30')
print('GENERAL PROOF: finite geometric telescoping and projective dimension')

Q = sp.Matrix([[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]])
assert Q.det() == 1 and Q.T == -Q
delta = sp.Matrix.hstack(sp.eye(4)[:,0],sp.eye(4)[:,0],sp.eye(4)[:,1])
B = delta.T * Q.T
assert delta.rank() == B.rank() == 2
assert delta.nullspace() == [sp.Matrix([-1,1,0])]
assert B == sp.Matrix([[0,0,-1,0],[0,0,-1,0],[0,0,0,-1]])
c=sp.Matrix([1,0,0])
k=sp.Matrix([-1,1,0])
assert (k.T*c)[0] == -1
assert (delta*k) == sp.zeros(4,1)
assert sp.Matrix.hstack(B,c).rank()>B.rank()
for i in range(3):
    assert sp.Matrix.hstack(B[i,:].T,sp.Matrix([c[i]])).rank()==B[i,:].rank()
print('PASS 3-hole local relation, nonzero carry, no simultaneous potential')

# Combined one-parameter aggregate may erase the nonzero local obstruction.
N=delta*B
Dc=delta*c
assert sp.Matrix.hstack(N,Dc).rank() == N.rank()
print('PASS aggregate one-parameter transfer can hide simultaneous nonsplit carry')

# General local carry identity for arbitrary symplectic V and all relation matrices:
# dim(Q^m/im B) == dim ker D because Q is invertible.
for m in range(1,9):
    for r in range(1,5):
        dim=2*r
        sym=sp.zeros(dim)
        for i in range(r):
            sym[i,r+i]=1
            sym[r+i,i]=-1
        # arbitrary list of isotropic e_1,...,e_r, repetitions allowed
        D=sp.zeros(dim,m)
        for j in range(m):
            D[j%r,j]=1
        B=D.T*sym.T
        assert B.rank()==D.rank()
        assert m-B.rank()==len(D.nullspace())
        for k in D.nullspace():
            assert k.T*B == sp.zeros(1,dim)
print('PASS all selected rectangular relation dimensions (m=1..8, rank 2..8)')
print('NONCLAIM: tests and local quotient do not construct Chow cycles on arbitrary X')
