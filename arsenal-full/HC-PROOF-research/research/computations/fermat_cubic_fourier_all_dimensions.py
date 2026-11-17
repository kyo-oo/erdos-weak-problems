#!/usr/bin/env python3
"""Exact finite audit of the uniform Fermat cubic maximal-plane Fourier mechanism.

For n=m+1, the cubic has complex dimension 2m. A chosen perfect matching
of its 2n projective coordinates yields 3^n native maximal planes with
intersection convolution K(g)=(1-(-2)^c)/3, c=#zero coordinates of g∈(Z/3)^n.
Its Fourier spectrum and the opposite-color character pairing are uniform.
"""
from itertools import product
from math import comb

OMEGA_PAIR=((1,0),(0,1),(-1,-1))

def intersection_kernel(g):
    c=sum(x==0 for x in g)
    num=1-(-2)**c
    assert num%3==0
    return num//3

def fourier_eigenvalue(n,frequency):
    a=b=0
    for g in product(range(3),repeat=n):
        u,v=OMEGA_PAIR[sum(x*y for x,y in zip(g,frequency))%3]
        k=intersection_kernel(g)
        a+=k*u
        b+=k*v
    return a,b

def rank_mod_p(A,p=101):
    A=[[x%p for x in row] for row in A]
    n=len(A)
    r=0
    for col in range(n):
        pivot=next((i for i in range(r,n) if A[i][col]),None)
        if pivot is None:
            continue
        A[r],A[pivot]=A[pivot],A[r]
        inv=pow(A[r][col],-1,p)
        A[r][col:]=[(x*inv)%p for x in A[r][col:]]
        for i in range(r+1,n):
            factor=A[i][col]
            if factor:
                A[i][col:]=[(x-factor*y)%p for x,y in zip(A[i][col:],A[r][col:])]
        r+=1
    return r

def opposite_color_matching(character):
    ones=[i for i,a in enumerate(character) if a==1]
    twos=[i for i,a in enumerate(character) if a==2]
    assert len(ones)==len(twos)
    return tuple(zip(ones,twos))

def main():
    for n in (2,3,4,5):
        labels=list(product(range(3),repeat=n))
        G=[[intersection_kernel(tuple((x-y)%3 for x,y in zip(a,b)))
            for b in labels] for a in labels]
        rank=rank_mod_p(G)
        assert rank==1+2**n,(n,rank)
        for frequency in labels:
            if all(k==0 for k in frequency):
                expected=3**(n-1)
            elif all(k!=0 for k in frequency):
                expected=(-1)**(n+1)*3**(n-1)
            else:
                expected=0
            assert fourier_eigenvalue(n,frequency)==(expected,0),(n,frequency)
        covered=set()
        for ch in product((1,2),repeat=2*n):
            if sum(k==1 for k in ch)==n:
                matching=opposite_color_matching(ch)
                assert len(matching)==n
                assert all(ch[i]!=ch[j] for i,j in matching)
                covered.add(ch)
        assert len(covered)==comb(2*n,n)
        print(f'n={n} complex_dimension={2*n-2} planes_per_matching={3**n} '
              f'one_matching_rank={rank} covered_middle_characters={len(covered)} '
              f'expected_primitive_Hodge_dim={comb(2*n,n)}')
    print('PASS: uniform Fourier spectrum and opposite-character matching')

if __name__=='__main__':
    main()
