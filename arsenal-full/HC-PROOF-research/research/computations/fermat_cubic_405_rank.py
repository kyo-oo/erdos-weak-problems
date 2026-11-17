#!/usr/bin/env python3
"""Exact 405-plane Gram certificate on the Fermat cubic fourfold.

For two projective planes in a smooth cubic fourfold, intersection
numbers are 3 (same plane), -1 (shared line), +1 (transverse point)
and 0 (disjoint). Each plane is defined by three pair equations
z_b = -omega^k z_a with omega^3=1, from a perfect matching on 6 indices.
"""
from itertools import product
from math import comb
import hashlib

PRIMES = (101, 103)
WITNESS = (0,1,2,3,4,9,10,12,13,27,28,36,37,81,82,84,85,108,109,189,190)

def matchings(items):
    if not items:
        yield ()
        return
    a = items[0]
    for j in range(1,len(items)):
        for rest in matchings(items[1:j]+items[j+1:]):
            yield ((a,items[j]),)+rest

def affine_intersection_dimension(A,B):
    adj=[[] for _ in range(6)]
    for pairs,powers in (A,B):
        for (a,b),k in zip(pairs,powers):
            adj[a].append((b,1,k))
            adj[b].append((a,1,-k % 3))
    values=[None]*6
    dim=0
    for root in range(6):
        if values[root] is not None:
            continue
        values[root]=(0,0)
        stack=[root]
        consistent=True
        while stack:
            u=stack.pop()
            parity,phase=values[u]
            for v,sign,k in adj[u]:
                expected=((parity+sign)%2,(phase+k)%3)
                if values[v] is None:
                    values[v]=expected
                    stack.append(v)
                elif values[v]!=expected:
                    consistent=False
        dim+=int(consistent)
    return dim

def affine_intersection_dimension_mod7(A,B):
    """Independent six-equation geometric intersection calculation over F7.

    The finite field has primitive cube roots 2 and 4. The six linear
    equations have the same incidence pattern as over Q(omega).
    """
    rows=[]
    for pairs,powers in (A,B):
        for (a,b),k in zip(pairs,powers):
            row=[0]*6
            row[a]=pow(2,k,7)
            row[b]=1
            rows.append(row)
    rank=0
    for col in range(6):
        pivot=next((i for i in range(rank,6) if rows[i][col]%7),None)
        if pivot is None:
            continue
        rows[rank],rows[pivot]=rows[pivot],rows[rank]
        inv=pow(rows[rank][col],-1,7)
        rows[rank][col:]=[(inv*v)%7 for v in rows[rank][col:]]
        for i in range(rank+1,6):
            factor=rows[i][col]
            if factor:
                rows[i][col:]=[(x-factor*y)%7 for x,y in zip(rows[i][col:],rows[rank][col:])]
        rank+=1
    return 6-rank

def gram_matrix():
    match=list(matchings(tuple(range(6))))
    assert len(match)==15
    planes=[(pairs,powers) for pairs in match
            for powers in product(range(3),repeat=3)]
    assert len(planes)==405
    G=[[0]*405 for _ in range(405)]
    counts=[0]*4
    for i in range(405):
        for j in range(i,405):
            dim=affine_intersection_dimension(planes[i],planes[j])
            assert dim==affine_intersection_dimension_mod7(planes[i],planes[j]),(i,j,dim)
            assert 0<=dim<=3
            counts[dim]+=1
            G[i][j]=G[j][i]=(0,1,-1,3)[dim]
    assert counts==[45360,31590,4860,405],counts
    assert all(G[i][i]==3 for i in range(405))
    return G

def rank_mod_p(G,p):
    rows=[[int(v)%p for v in row] for row in G]
    rank=0
    pivots=[]
    for c in range(len(rows[0])):
        pivot=next((i for i in range(rank,len(rows)) if rows[i][c]),None)
        if pivot is None:
            continue
        rows[rank],rows[pivot]=rows[pivot],rows[rank]
        inv=pow(rows[rank][c],-1,p)
        rows[rank][c:]=[(inv*x)%p for x in rows[rank][c:]]
        for i in range(rank+1,len(rows)):
            coef=rows[i][c]
            if coef:
                ri,rr=rows[i],rows[rank]
                ri[c:]=[(x-coef*y)%p for x,y in zip(ri[c:],rr[c:])]
        pivots.append(c)
        rank+=1
        if rank==len(rows):
            break
    return rank,tuple(pivots)

def bareiss_det(matrix):
    A=[list(row) for row in matrix]
    n=len(A)
    if n==0:
        return 1
    prev=1
    sign=1
    for k in range(n-1):
        if not A[k][k]:
            swap=next((j for j in range(k+1,n) if A[j][k]),None)
            assert swap is not None
            A[k],A[swap]=A[swap],A[k]
            sign*=-1
        pivot=A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=A[i][j]*pivot-A[i][k]*A[k][j]
                quotient,remainder=divmod(numerator,prev)
                assert remainder==0
                A[i][j]=quotient
            A[i][k]=0
        prev=pivot
    return sign*A[-1][-1]

def main():
    G=gram_matrix()
    minor=[[G[i][j] for j in WITNESS] for i in WITNESS]
    det=bareiss_det(minor)
    assert det==27,det
    # Twenty explicit primitive cycles C_i=[P_i]-[P_0], i=1,...,20.
    # Their h^2 pairing is 1-1=0; their Gram is the difference matrix.
    primitive_gram=[
        [minor[i][j]-minor[i][0]-minor[0][j]+minor[0][0]
         for j in range(1,21)]
        for i in range(1,21)
    ]
    primitive_det=bareiss_det(primitive_gram)
    assert primitive_det==81,primitive_det
    for p in PRIMES:
        rank,pivots=rank_mod_p(G,p)
        assert rank==21 and pivots==WITNESS,(p,rank,pivots)
        print(f'405-plane integer Gram rank over F_{p}: {rank}')
    # Jacobian ring of Fermat cubic: R=Q[z0,...,z5]/(zi^2);
    # dim primitive (2,2) = # squarefree degree-3 monomials = 20;
    # add the rational hyperplane-square direction.
    assert comb(6,3)+1==21
    digest=hashlib.sha256(
        ''.join(','.join(map(str,row))+';' for row in G).encode()
    ).hexdigest()
    assert digest=='ba97d18902a7ecf4a6675ef0f7a664ccdd1f77895bbf3ea38efa8085c5cd1df2'
    print('21x21 principal minor determinant:',det)
    print('20 primitive plane differences determinant:',primitive_det)
    print('Complex (2,2) dimension:',comb(6,3)+1)
    print('Selected plane indices:',','.join(map(str,WITNESS)))
    print('Full Gram SHA256:',digest)
    print('PASS: explicit 21 independent plane classes span H^(2,2)')

if __name__=='__main__':
    main()
