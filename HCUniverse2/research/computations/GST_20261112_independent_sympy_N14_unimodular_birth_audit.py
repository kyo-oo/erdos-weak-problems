#!/usr/bin/env python3
"""Independent exact GST N14 birth law audit.

Rebuild original 4x3 U/J/M/CM from cell formulas; do NOT read Wolfram
matrices, Smith bases, Krylov determinants, or fitted coefficients.
The two birth channels have the seven original-GST sparse couplings:
 B[4,1]=B[5,1]=B[6,1]=B[10,1]=-1; B[12,2]=1;
 C[1,11]=C[2,12]=1 (one-based).
The same birth channels are used for BOTH physical Navigation states.
Check exact integer lattice invertibility; all powers follow from det=1.
This does not construct a missing original-X Chow representative.
"""
import sympy as sp

CELLS = [(i,k) for i in range(4) for k in range(3)]
INDEX = {c:j for j,c in enumerate(CELLS)}
U, J, M = sp.zeros(12), sp.zeros(12), sp.zeros(12)

for row,(i,k) in enumerate(CELLS):
    U[row, INDEX[((i+4*k)//3, (i+4*k)%3)]] = 1
    J[row, INDEX[(3-i,2-k)]] = (
        1 if i+4*k in (0,1,3,4,5,9) else -1)
    p = (i//2+2*k)%3
    q = (i%2+2*p)%3
    M[row,row] = int(k==2 and p==2) + int(p==2 and q==2)

CURVATURE = J*M-M*J
B = sp.zeros(12,2)
for row in (3,4,5,9):
    B[row,0] = -1
B[11,1] = 1
C = sp.zeros(2,12)
C[0,10] = 1
C[1,11] = 1

SEED = sp.Matrix([int(c in ((0,0),(0,1))) for c in CELLS]+[0,0])

def rank_mod_prime(mat,prime):
    arr = [[int(x)%prime for x in row] for row in mat.tolist()]
    nr, nc = mat.shape
    pivot_row = 0
    for col in range(nc):
        pivot = next((i for i in range(pivot_row,nr)
                      if arr[i][col]%prime!=0), None)
        if pivot is None: continue
        arr[pivot_row],arr[pivot] = arr[pivot],arr[pivot_row]
        inv = pow(arr[pivot_row][col],-1,prime)
        arr[pivot_row] = [(x*inv)%prime for x in arr[pivot_row]]
        for i in range(nr):
            if i==pivot_row: continue
            factor=arr[i][col]
            arr[i] = [(a-factor*b)%prime
                      for a,b in zip(arr[i],arr[pivot_row])]
        pivot_row += 1
        if pivot_row==nr: break
    return pivot_row

assert U**5==sp.eye(12)
assert J**2==-sp.eye(12)
assert U*J==J*U
results=[]
for charge in (0,1):
    F=U+J+M+charge*CURVATURE
    G=F.row_join(B).col_join(C.row_join(sp.zeros(2)))
    states=[SEED]
    for _ in range(13): states.append(G*states[-1])
    detk=sp.Matrix.hstack(*states).det()
    prime=2 if charge==0 else 3
    result={
       'charge':charge,
       'originalDet':int(F.det()),
       'originalRankModObstructingPrime':rank_mod_prime(F,prime),
       'obstructingPrime':prime,
       'N14Det':int(G.det()),
       'N14OriginalSeedKrylovDet':int(detk),
       'N14AllIntegerEntries':all(x.q==1 for x in G),
       'N14IntegerInverse':all(x.q==1 for x in G.inv()),
       'unchangedOriginalF':G[:12,:12]==F,
    }
    assert result['originalRankModObstructingPrime']==10
    assert result['N14Det']==1
    assert result['N14AllIntegerEntries']
    assert result['N14IntegerInverse']
    assert result['unchangedOriginalF']
    assert detk != 0
    results.append(result)
assert [r['originalDet'] for r in results] == [16,0]
assert [r['N14OriginalSeedKrylovDet'] for r in results] == [
    -823658646480,14979092529]
# Independent exact ALL-parameter symbolic determinant, not sampling.
AA, BB = sp.symbols("AA BB")
Fsymbolic = U+J+AA*M+BB*CURVATURE
Gsymbolic = Fsymbolic.row_join(B).col_join(
    C.row_join(sp.zeros(2)))
symbolic_determinant = sp.factor(Gsymbolic.det(method='domain-ge'))
assert sp.simplify(symbolic_determinant-(AA+BB*(BB-1)**2))==0

print({'states':results,
       'symbolic14det':str(symbolic_determinant),
       'allParameterPolynomialVerified':True,'allPassed':True})
