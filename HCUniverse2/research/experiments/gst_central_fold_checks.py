#!/usr/bin/env python3
"""Exact whole-space exterior cohomology. No Lean compilation.
Command: python research/experiments/gst_central_fold_checks.py
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb
import json

CHECKS=0
def check(v):
    global CHECKS
    CHECKS+=1
    if not v: raise AssertionError(CHECKS)

def sparse_rank(columns):
    pivots={}
    for column in columns:
        v={i:Q(a) for i,a in column.items() if a}
        while v:
            i=min(v)
            if i not in pivots:
                a=v[i]
                pivots[i]={j:b/a for j,b in v.items()}
                break
            a=v[i]
            for j,b in pivots[i].items():
                v[j]=v.get(j,Q(0))-a*b
                if not v[j]: del v[j]
    return len(pivots)

def dmask(mask,m,r,K):
    out=defaultdict(int)
    for a in range(r):
        u=2*m+2*a
        if not mask>>u&1: continue
        rest=mask^(1<<u)
        position=(mask&((1<<u)-1)).bit_count()
        for j in range(m):
            pair=(1<<(2*j))|(1<<(2*j+1))
            if not rest&pair:
                # The adjacent two-form crosses any prefix with even sign.
                out[rest|pair]+=(-1)**(position+1)*K[a][j]
    return {i:a for i,a in out.items() if a}

def dpoly(poly,m,r,K):
    out=defaultdict(int)
    for mask,a in poly.items():
        for target,b in dmask(mask,m,r,K).items(): out[target]+=a*b
    return {i:a for i,a in out.items() if a}

def row_rank(K,m):
    return sparse_rank([{j:a for j,a in enumerate(row) if a} for row in K])

def spectrum(m,r,K):
    n=2*(m+r)
    bases=[[sum(1<<i for i in c) for c in combinations(range(n),k)]
           for k in range(n+1)]
    ranks=[]
    for basis in bases:
        columns=[dmask(mask,m,r,K) for mask in basis]
        for col in columns: check(not dpoly(col,m,r,K))
        ranks.append(sparse_rank(columns))
    betti=[len(bases[k])-ranks[k]-(ranks[k-1] if k else 0)
           for k in range(n+1)]
    check(betti==betti[::-1])
    check(sum((-1)**k*b for k,b in enumerate(betti))==(1 if n==0 else 0))
    rho=row_rank(K,m)
    if n:
        check(betti[1]==2*m+2*r-rho)
        check(betti[1]-2*(m+r-rho)==rho)
    return [m,r,K,betti,ranks,rho,m+r-rho]

def bn(n,k): return comb(n,k) if 0<=k<=n else 0
def convolution(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
def one_handle_formula(m,t):
    a=[max(bn(2*t,k)-bn(2*t,k-2),0)+
       max(bn(2*t,k-1)-bn(2*t,k+1),0) for k in range(2*t+2)]
    closed=2*(m-t)+1
    return convolution(a,[comb(closed,j) for j in range(closed+1)])

def pairing(K,x,y): return [sum(a*b*c for a,b,c in zip(row,x,y)) for row in K]
def plus(x,y):return [a+b for a,b in zip(x,y)]
def multiply(K,p,q):
    x,y,s=p;xx,yy,ss=q
    return plus(x,xx),plus(y,yy),plus(plus(s,ss),pairing(K,x,yy))

def run():
    rows=[spectrum(0,0,[]),spectrum(1,0,[]),spectrum(0,1,[[]])]
    for m in range(5):
        for t in range(m+1):
            K=[[1 if j<t else 0 for j in range(m)]]
            row=spectrum(m,1,K)
            check(row[3]==one_handle_formula(m,t))
            rows.append(row)
    for m,K in [(2,[[1,0],[0,1]]),(2,[[1,1],[2,2]]),
                (2,[[1,0],[-1,0]]),(3,[[1,0,1],[0,1,1]])]:
        rows.append(spectrum(m,len(K),K))
    check(spectrum(2,1,[[1,0]])[3]==[1,5,11,14,11,5,1])
    check(spectrum(2,1,[[1,1]])[3]==[1,5,9,10,9,5,1])
    even=next(row for row in rows if row[0:3]==[2,2,[[1,0],[0,1]]])
    check(even[3][1]==6 and even[6]==2 and even[5]==2)
    histogram=[0,0,0]
    points=[([0,0],[0,0],[0,0]),([1,0],[0,1],[1,-1]),
            ([0,1],[-1,0],[2,1]),([1,-1],[1,1],[-1,2])]
    for entries in product([-1,0,1],repeat=4):
        K=[list(entries[:2]),list(entries[2:])]
        rho=row_rank(K,2);histogram[rho]+=1
        d1=sparse_rank([dmask(1<<i,2,2,K) for i in range(8)])
        check(d1==rho)
        check((8-d1)-2*(4-rho)==rho)
        inverse=[[-x for x in row] for row in K]
        total=[[a+b for a,b in zip(row,other)] for row,other in zip(K,inverse)]
        check(total==[[0,0],[0,0]])
        for p,q,s in product(points,repeat=3):
            check(multiply(K,multiply(K,p,q),s)==multiply(K,p,multiply(K,q,s)))
    return {'all_passed':True,'assertion_count':CHECKS,'spectral_rows':rows,
            'matrix_rank_histogram_2x2':histogram,
            'bounds':{'one_handle':'m=0..4, every active rank t=0..m',
                      'full_spectra':'22 declared fixtures, real dimensions 0..10',
                      'all_curvature_matrices':'81 integer 2x2 matrices, entries -1..1',
                      'associativity':'all ordered triples of four declared points for each matrix'},
            'interpretation':'Finite exact support for the hand whole-space theorem; not Lean or a universal Chow-source proof'}

if __name__=='__main__':print(json.dumps(run(),separators=(',',':')))
