"""Exact finite tests for full-Chow one-seed cyclic fold and Hankel determinant.

Does not construct arbitrary-X algebraic cycles: the full Chow action is
geometrically available once true Hodge spanning cycles and duals are given.
"""
import sympy as sp
for n in range(1,13):
    T=sp.zeros(n)
    for j in range(n-1): T[j+1,j]=1
    seed=sp.eye(n)[:,0]
    ell=sp.eye(n)[:,n-1]
    orbit=[seed]
    for _ in range(2*n-2): orbit.append(T*orbit[-1])
    H=sp.Matrix(n,n,lambda i,j:(ell.T*orbit[i+j])[0])
    assert H==sp.eye(n)[::-1,:]
    assert H.det()==(-1)**(n*(n-1)//2)
    assert sp.Matrix.hstack(*orbit[:n])==sp.eye(n)
    print('PASS n',n,'det',H.det())
print('STATUS: exact finite tests; no universal alpha-dependent source constructed')
