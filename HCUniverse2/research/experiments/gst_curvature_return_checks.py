#!/usr/bin/env python3
"""Exact diagnostic fixtures, not an algebraic-existence test.
Run: python research/experiments/gst_curvature_return_checks.py
All rational arithmetic uses Fraction; no random inputs or external packages.
"""
from fractions import Fraction as Q
import json

def matrix(a): return [[Q(x) for x in row] for row in a]
def product(a,b):
    assert len(a[0])==len(b)
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))),Q(0))
             for j in range(len(b[0]))] for i in range(len(a))]
def scale(c,a): return [[c*x for x in row] for row in a]
def sub(a,b): return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def identity(n): return matrix([[int(i==j) for j in range(n)] for i in range(n)])
def zero(a):return all(x==0 for row in a for x in row)
def rank(a):
    a=[row[:] for row in a];r=0
    for j in range(len(a[0])):
        p=next((i for i in range(r,len(a)) if a[i][j]),None)
        if p is None: continue
        a[r],a[p]=a[p],a[r];v=a[r][j];a[r]=[x/v for x in a[r]]
        for i in range(len(a)):
            if i!=r:
                v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[r])]
        r+=1
        if r==len(a):break
    return r
def in_range(a,b):return rank([row+[v] for row,v in zip(a,b)])==rank(a)
def encoded(a):return [[str(x) for x in row] for row in a]

def main():
    checks=[]
    def check(name,condition):
        checks.append(name)
        assert condition,name
    pull=matrix([[1,0],[0,1],[1,1]])
    raw=matrix([[4,-2,2],[-3,3,3]])
    ret=scale(Q(1,6),raw)
    proj=product(pull,ret)
    check('raw_degree_six',product(raw,pull)==scale(6,identity(2)))
    check('normalized_retraction',product(ret,pull)==identity(2))
    check('idempotent_projector',product(proj,proj)==proj)
    check('remainder_return_zero',zero(product(ret,sub(identity(3),proj))))
    check('split_ranks',[rank(pull),rank(ret),rank(proj),rank(sub(identity(3),proj))]==[2,2,2,1])
    g=matrix([[1,0,0],[0,1,0],[0,0,1],[1,-1,1]])
    rg=matrix([[5,0,0,0],[0,5,0,0],[0,0,5,0]])
    composite=product(raw,rg)
    check('composite_degree_thirty',product(composite,product(g,pull))==scale(30,identity(2)))
    check('normalized_composition',scale(Q(1,30),composite)==product(ret,scale(Q(1,5),rg)))
    clx=matrix([[1,0],[0,0]])
    cly=matrix([[1,0,0],[0,1,0],[1,-1,0]])
    cyclepull=matrix([[1,0],[0,0],[0,1]])
    cycletr=matrix([[6,-4,0],[0,0,1]])
    check('cycle_pullback_comparison',product(cly,cyclepull)==product(pull,clx))
    check('cycle_transfer_comparison',product(clx,cycletr)==product(raw,cly))
    image_rows=[]
    for a in ((1,0),(0,1),(1,1),(0,0)):
        pa=[row[0] for row in product(pull,matrix([[a[0]],[a[1]]]))]
        left,right=in_range(cly,pa),in_range(clx,a)
        check('source_image_'+str(a),left==right)
        image_rows.append([list(a),left,right])
    # Different cycles have equal returned Betti classes, not equal Chow carriers.
    z,w=matrix([[2],[0],[0]]),matrix([[2],[0],[6]])
    rz,rw=scale(Q(1,6),product(cycletr,z)),scale(Q(1,6),product(cycletr,w))
    check('boundary_solutions_same_betti',product(clx,rz)==product(clx,rw))
    check('boundary_solutions_distinct_cycles',rz!=rw)
    # This is the exact degree-2p cohomology map in the one-generator
    # model with du=h^p: the original basis h^p becomes a boundary.
    nullpull=matrix([[0]])
    augmented=matrix([[0,1]]) # equation R*0=1 has ranks 0 versus 1.
    check('nonzero_nullifier_has_no_transfer',rank(nullpull)<rank(augmented))
    check('degree_zero_is_not_a_retraction',zero(product(nullpull,nullpull)) and rank(nullpull)==0)
    # Sharp controls for P4 minus a linear codimension-c subspace:
    # its affine-bundle projection has base P^(c-1), hence h^p survives iff p<c.
    boundary_rows=[[4,2,2,True],[4,2,3,False],[4,1,1,True],[4,1,2,False]]
    for n,p,c,killed in boundary_rows:
        restriction=matrix([[int(i==j) for j in range(n+1)] for i in range(c)])
        hp=matrix([[int(j==p)] for j in range(n+1)])
        check('boundary_threshold_'+str((n,p,c)),killed==zero(product(restriction,hp)))
    print(json.dumps({'all_passed':True,'assertions':len(checks),'checks':checks,
      'projector':encoded(proj),'composite_raw_transfer':encoded(composite),
      'cycle_image_rows':image_rows,'returned_boundary_cycles':[encoded(rz),encoded(rw)],
      'nullifier_rank_pair':[rank(nullpull),rank(augmented)],'boundary_rows':boundary_rows,
      'scope':'One exact non-diagonal split-transfer fixture, a degree-thirty composition, a deficient source-image fixture with distinct nullhomologous cycles, the nonzero-nullifier incompatibility, and four projective-space boundary controls. No universal source-existence or geometric theorem is tested.'},sort_keys=True))
if __name__=='__main__':main()
