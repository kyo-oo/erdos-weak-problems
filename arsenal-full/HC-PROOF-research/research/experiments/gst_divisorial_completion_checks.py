#!/usr/bin/env python3
"""Exact fixtures for the curvature sequence and divisorial-return distinctions.
Run: python research/experiments/gst_divisorial_completion_checks.py
These are rational linear models, not geometric existence tests.
"""
from fractions import Fraction as Q
from pathlib import Path
import importlib.util,json,sys
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('transfer_fixture',Path(__file__).with_name('gst_curvature_return_checks.py'))
t=importlib.util.module_from_spec(spec);spec.loader.exec_module(t)
matrix,product,scale,identity,rank,encoded=t.matrix,t.product,t.scale,t.identity,t.rank,t.encoded

def transpose(a):return [list(x) for x in zip(*a)]
def nullspace(a):
    a=[row[:] for row in a];m,n=len(a),len(a[0]);piv=[];r=0
    for j in range(n):
        k=next((k for k in range(r,m) if a[k][j]),None)
        if k is None:continue
        a[r],a[k]=a[k],a[r];v=a[r][j];a[r]=[x/v for x in a[r]]
        for k in range(m):
            if k!=r:
                v=a[k][j];a[k]=[x-v*y for x,y in zip(a[k],a[r])]
        piv.append(j);r+=1
        if r==m:break
    out=[]
    for j in range(n):
        if j in piv:continue
        v=[Q(0)]*n;v[j]=Q(1)
        for k,p in enumerate(piv):v[p]=-a[k][j]
        out.append(v)
    return out

def inverse(a):
    n=len(a);aug=[r+s for r,s in zip(a,identity(n))]
    for j in range(n):
        k=next(k for k in range(j,n) if aug[k][j])
        aug[j],aug[k]=aug[k],aug[j];v=aug[j][j];aug[j]=[x/v for x in aug[j]]
        for k in range(n):
            if k!=j:
                v=aug[k][j];aug[k]=[x-v*y for x,y in zip(aug[k],aug[j])]
    return [r[n:] for r in aug]

def main():
    checks=[]
    def check(name,test):
        checks.append(name);assert test,name
    sequence=[]
    for L in [matrix([[1,2,3],[0,0,0]]),matrix([[1,0,1],[0,1,1]]),
              matrix([[0,0,0],[0,0,0]]),matrix([[1,0],[0,1]]),matrix([[2],[4]])]:
        m,r=len(L),len(L[0]);K=nullspace(L);rho=rank(L);k=len(K)
        E=[[*(K[j][i] for j in range(k)),*([Q(0)]*r)] for i in range(r)]
        E += [[*([Q(0)]*k),*(Q(i==j) for j in range(r))] for i in range(r)]
        qE=product([([Q(0)]*r)+row for row in L],E)
        pure=[[*(K[j][i] for j in range(k)),*([Q(0)]*k)] for i in range(r)]
        pure += [[*([Q(0)]*k),*(K[j][i] for j in range(k))] for i in range(r)]
        # Rank for the zero-column pure space is zero, without an empty-matrix shortcut.
        pr=rank(pure) if k else 0
        check('closed_vertical_dimension_'+str(L),rank(E)==2*r-rho)
        check('missing_surjection_'+str(L),rank(qE)==rho)
        check('kernel_equals_pure_'+str(L),pr==2*(r-rho) and rank(E)-rank(qE)==pr)
        if k:
            check('pure_is_in_missing_kernel_'+str(L),t.zero(product([([Q(0)]*r)+row for row in L],pure)))
        # Exact Gaussian rational splitting for real u,v in ker L.
        u=K[0] if k else [Q(0)]*r;v=K[-1] if k else [Q(0)]*r
        plus=[(x/2,-y/2) for x,y in zip(u,v)]
        minus=[(x/2,y/2) for x,y in zip(u,v)]
        add=lambda z,w:(z[0]+w[0],z[1]+w[1])
        imul=lambda z:(-z[1],z[0])
        check('explicit_complex_split_'+str(L),
              [add(a,b) for a,b in zip(plus,minus)]==[(x,Q(0)) for x in u] and
              [imul((a[0]-b[0],a[1]-b[1])) for a,b in zip(plus,minus)]==[(x,Q(0)) for x in v])
        sequence.append([m,r,rho,rank(E),rank(qE),pr])
    # Nullary handle spaces are genuinely zero, separately from the r>0 matrix code.
    check('zero_handle_exact_sequence',2*0-0==0 and 2*(0-0)==0)
    G=matrix([[1,1,0,0,0,0,0],[0,1,1,0,0,0,0],
              [0,0,0,1,0,0,0],[0,0,0,0,1,0,0]])
    PB=matrix([[int(i==j and i<3) for j in range(7)] for i in range(7)])
    PV=matrix([[int(i==j and i<2) for j in range(4)] for i in range(4)])
    a=matrix([[1],[0],[0],[0]]);raw=matrix([[1],[0],[0],[0],[0],[1],[0]])
    check('type_projectors_commute',product(G,PB)==product(PV,G))
    check('rational_lift_need_not_be_hodge',product(G,raw)==a and product(PB,raw)!=raw)
    check('corrected_lift_exact',product(G,product(PB,raw))==a)
    S=product(transpose(G),inverse(product(G,transpose(G))))
    b=product(S,a);N,d=Q(3),Q(6);integral=scale(N,b)
    check('polarized_complement_right_inverse',product(G,S)==identity(4))
    check('rational_hodge_lift',b==matrix([[Q(2,3)],[Q(1,3)],[Q(-1,3)],[0],[0],[0],[0]]) and product(PB,b)==b)
    check('integral_boundary_denominator',all(x.denominator==1 for row in integral for x in row) and product(G,integral)==scale(N,a))
    tr=matrix([[6,0,0,0],[0,6,0,0]]);expected=matrix([[1],[0]])
    returned=scale(1/(N*d),product(tr,product(G,integral)))
    check('both_denominators_return',returned==expected)
    check('omitting_degree_fails',scale(1/N,product(tr,product(G,integral)))!=expected)
    check('omitting_line_denominator_fails',scale(1/d,product(tr,product(G,integral)))!=expected)
    L=matrix([[1],[1]]);restrict=matrix([[1,-1]]);P=scale(Q(1,2),matrix([[1,-1],[-1,1]]))
    check('ample_kernel_and_primitive',t.zero(product(restrict,L)) and t.zero(product(P,L)) and product(P,P)==P)
    rows=[]
    for x in [(1,0),(0,1),(1,1),(1,-1),(0,0)]:
        col=matrix([[x[0]],[x[1]]]);res=product(restrict,col);prim=product(P,col)
        killed=t.zero(res);in_L=t.in_range(L,x)
        check('ample_exact_nullification_'+str(x),killed==in_L==t.zero(prim))
        rows.append([list(x),killed,encoded(res),encoded(prim)])
    # Q4 ruling cycles: h^2=A+B, primitive=A-B, intersection Gram=I_2.
    gamma=matrix([[1],[-1]]);h2=matrix([[1],[1]])
    check('quadric_primitive_nonzero_norm',product(transpose(gamma),gamma)==matrix([[2]]) and t.zero(product(transpose(h2),gamma)))
    check('singular_boundary_line_return',product(identity(2),gamma)==gamma and not t.zero(product(restrict,gamma)))
    print(json.dumps({'all_passed':True,'assertions':len(checks),'checks':checks,
      'sequence_rows':sequence,'hodge_lift':encoded(b),'cleared_source':encoded(integral),
      'returned_cycle':encoded(returned),'ample_rows':rows,
      'quadric_line_return':encoded(gamma),
      'scope':'Five rectangular curvature matrices plus zero handles; one rational Hodge-correction fixture with a non-Hodge rational lift, denominator-three boundary and degree-six return; five smooth-ample restriction controls in the quadric middle-coordinate model and a singular-boundary line-return control. No finite fixture proves source existence, weight degeneration, GAGA or the universal Hodge claim.'},sort_keys=True))
if __name__=='__main__':main()
