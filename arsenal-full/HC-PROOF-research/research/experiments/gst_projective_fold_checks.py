#!/usr/bin/env python3
"""Exact supporting arithmetic, not a test of analytic torsor projectivity.
Run: python research/experiments/gst_projective_fold_checks.py
Domain: Z^2 -> Z + Z/6; every free row in [-1,1]^2, every finite
row in [0,5]^2, and every input vector in [-2,2]^2. No sampling.
"""
from itertools import product
from math import gcd
from fractions import Fraction
import json

def main():
    count=0
    def check(p):
        nonlocal count
        count+=1
        assert p, count
    dot=lambda a,b:sum(x*y for x,y in zip(a,b))
    vectors=list(product(range(-2,3),repeat=2))
    rows=[]
    for free in product(range(-1,2),repeat=2):
        relation_count=exact_count=0
        for finite in product(range(6),repeat=2):
            def order(x):
                if dot(free,x):return None
                return 6//gcd(6,dot(finite,x))
            def exact(x):return dot(free,x)==0 and dot(finite,x)%6==0
            for x in vectors:
                o=order(x)
                relation_count+=o is not None
                exact_count+=exact(x)
                check((o is not None)==(dot(free,x)==0))
                if o is not None:
                    check(exact(tuple(o*a for a in x)))
                    check(exact(tuple(6*a for a in x)))
                for k in (2,3,4):
                    check((order(tuple(k*a for a in x)) is not None)==(o is not None))
            for x in product(range(-1,2),repeat=2):
                for y in product(range(-1,2),repeat=2):
                    if order(x) is not None and order(y) is not None:
                        check(order(tuple(a+b for a,b in zip(x,y))) is not None)
        rows.append([list(free),relation_count,exact_count])
    # Saturated basis B versus exact-kernel basis K, with index six.
    B=((1,-1,0),(0,0,1));K=((1,-1,1),(0,0,6))
    coordinates=[]
    for x in product(range(-3,4),repeat=3):
        sat=x[0]+x[1]==0
        exact=sat and (x[0]+2*x[1]+x[2])%6==0
        if sat:
            a,b=x[0],x[2]
            check(tuple(a*B[0][j]+b*B[1][j] for j in range(3))==x)
            check(exact==((b-a)%6==0))
            if exact:
                c=(b-a)//6
                check(tuple(a*K[0][j]+c*K[1][j] for j in range(3))==x)
        coordinates.append([list(x),sat,exact])
    # An actual ample-fiber polarization has an isogeny, not generally identity.
    lam=((2,1),(1,2));adj=((2,-1),(-1,2))
    mat=lambda a,b:tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))
    check(mat(adj,lam)==((3,0),(0,3)))
    kernels=[]
    for modulus in range(2,13):
        kernel=[]
        for x in product(range(modulus),repeat=2):
            if all(dot(row,x)%modulus==0 for row in lam):
                check(all(3*a%modulus==0 for a in x));kernel.append(list(x))
        kernels.append([modulus,len(kernel)])
    # Exact source coefficient in the explicit finite-cover pushforward.
    degrees=[]
    for r in range(5):
        for n in range(1,7):
            d=n**(2*r)
            coefficient=Fraction(1,d)
            check(coefficient*d==1)
            degrees.append([r,n,d])
    result={'all_passed':True,'assertions':count,'relation_rows':rows,
      'basis_index':6,'lattice_vector_counts':[len(coordinates),sum(x[1] for x in coordinates),sum(x[2] for x in coordinates)],
      'isogeny_kernel_counts':kernels,'cover_degrees':degrees,
      'bounds':{'torsor_group':'Z + Z/6','free_rows':'all 9 rows in [-1,1]^2',
      'finite_rows':'all 36 rows in [0,5]^2','vectors':'all 25 vectors in [-2,2]^2',
      'saturation_multipliers':[2,3,4],'lattice_vectors':'all 343 vectors in [-3,3]^3',
      'isogeny_moduli':'2..12','cover_order':'N=1..6,r=0..4'},
      'scope':'Finite exact group/lattice and normalization support; no analytic geometry, Lean compilation, or universal Chow-source certificate'}
    print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
