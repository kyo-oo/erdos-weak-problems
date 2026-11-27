#!/usr/bin/env python3
"""Exact finite support for nonlinear marked-base folds. No Lean or network.

The arbitrary-X classification and derived-fiber argument are hand proofs.
All fixture rings, signs, basis states and coefficient ranges are explicit.
"""
import sys
sys.dont_write_bytecode=True
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import json
import gst_minimal_curvature_checks as old
from gst_base_coupled_higher_fold_checks import basis,dense_rref,sparse_rank

N=0
def check(p,why=None):
    global N
    N+=1
    if not p:raise AssertionError((N,why))
def states(dims,r):return [(a,m) for a in basis(dims) for m in range(1<<(2*r))]
def apply(poly,fn):return old.linear_apply(poly,fn)
def add(a,b,s=1):return old.plus(a,b,s)
def prod(dims,a,b):return old.exterior_mul(dims,a,b)
def unit(dims):return {((0,)*len(dims),0):Q(1)}
def gen(dims,i):return {((0,)*len(dims),1<<i):Q(1)}
def as_base(a):return {(m,0):Q(c) for m,c in a.items() if c}
def scale(p,k):return old.clean({s:k*c for s,c in p.items()})

def differential(dims,images,state):
    a,m=state;word=[i for i in range(len(images)) if m>>i&1];out={}
    for pos,i in enumerate(word):
        part={(a,0):Q((-1)**pos)}
        for j in word[:pos]:part=prod(dims,part,gen(dims,j))
        part=prod(dims,part,images[i])
        for j in word[pos+1:]:part=prod(dims,part,gen(dims,j))
        out=add(out,part)
    return out

def substitute(dims,images,state):
    a,m=state;out={(a,0):Q(1)}
    for i in range(len(images)):
        if m>>i&1:out=prod(dims,out,images[i])
    return out

def ideal_columns(dims,cs):
    return [as_base(old.mul(dims,{b:1},a)) for a in cs for b in basis(dims)]

def kernel_row(dims,ps,cs,dfn=None):
    ss=states(dims,len(cs));bb=[(a,0) for a in basis(dims)]
    dfn=dfn or (lambda s:old.boundary(dims,cs,s))
    cols=[dfn(s) for s in ss];basecols=[{s:1} for s in bb]
    rd=sparse_rank(cols);intersection=rd+len(bb)-sparse_rank(cols+basecols)
    ideals=ideal_columns(dims,cs);ri=sparse_rank(ideals)
    check(intersection==ri,('intersection dimension',dims,ps,cs))
    for col in ideals:check(sparse_rank(cols+[col])==rd,('ideal is boundary',col))
    # Independent dense row elimination of the full image/base sum.
    rows=[[c.get(s,0) for c in cols+basecols] for s in ss]
    check(rd+len(bb)-len(dense_rref(rows,len(cols)+len(basecols))[1])==ri)
    profile=[]
    for q in range(sum(dims)+1):
        degreecols=[{s:c for s,c in col.items() if sum(s[0])==q} for col in ideals]
        profile.append(sparse_rank(degreecols))
    return {'base':list(dims),'weights':ps,'kernel_dimension':ri,'kernel_by_weight':profile}

def nonlinear_rows():
    dims=(1,1);ps=[1,1,2];cs=[{(1,0):1},{},{(1,1):1}]
    ss=states(dims,3);g=[gen(dims,i) for i in range(6)]
    yu=prod(dims,as_base({(0,1):1}),g[0]);uvz=prod(dims,prod(dims,g[0],g[1]),g[2])
    xvz=prod(dims,prod(dims,as_base(cs[0]),g[1]),g[2]);rows=[]
    for lam in [-2,-1,0,1,2]:
        forward=g.copy();forward[4]=add(add(g[4],yu,-1),uvz,lam)
        inverse=g.copy();inverse[4]=add(add(g[4],yu),uvz,-lam)
        F=lambda s:substitute(dims,forward,s);G=lambda s:substitute(dims,inverse,s)
        D=lambda s:old.boundary(dims,cs,s)
        diff=[as_base(cs[0]),{},{},{},scale(xvz,lam),{}]
        E=lambda s:differential(dims,diff,s)
        for s in ss:
            check(apply(F(s),G)=={s:1},('inverse GF',lam,s))
            check(apply(G(s),F)=={s:1},('inverse FG',lam,s))
            check(all(old.degree(ps,t)==old.degree(ps,s) for t in F(s)),('absolute degree',lam,s))
            check(apply(F(s),D)==apply(E(s),F),('nonlinear chain equation',lam,s))
            check(not apply(E(s),E),('nonlinear differential square',lam,s))
        W=g[4];closed=add(W,uvz,-lam)
        check(apply(W,E)==scale(xvz,lam))
        check(not apply(closed,E))
        check(bool(apply(W,E))==(lam!=0))
        row=kernel_row(dims,ps,cs,E);row.update(parameter=lam,states=len(ss),W_closed=(lam==0));rows.append(row)
    return rows

def nullspace(columns,bb):
    rr,piv=dense_rref([[c.get(a,0) for c in columns] for a in bb],len(columns))
    ans=[]
    for j in range(len(columns)):
        if j in piv:continue
        v=[Q(0)]*len(columns);v[j]=1
        for row,p in enumerate(piv):v[p]=-rr[row][j]
        ans.append(old.clean(dict(zip(bb,v))))
    return ans

def one_ring_row(dims,p,a):
    bb=basis(dims);ss=states(dims,1);ideal=[old.mul(dims,{b:1},a) for b in bb]
    ann=nullspace(ideal,bb);qreps=[];span=ideal.copy();rk=sparse_rank(span)
    for b in bb:
        v={b:Q(1)};n=sparse_rank(span+[v])
        if n>rk:qreps.append(v);span.append(v);rk=n
    # Independent cycle representatives, in exterior sectors 1,u,v,uv.
    reps=[]
    for mask,coeffs in [(0,qreps),(1,ann),(2,qreps),(3,ann)]:
        reps.extend({(b,mask):c for b,c in v.items()} for v in coeffs)
    D=lambda s:old.boundary(dims,[a],s)
    boundaries=[D(s) for s in ss];rd=sparse_rank(boundaries)
    for r in reps:check(not apply(r,D),('ring representative closed',dims,a,r))
    check(sparse_rank(boundaries+reps)==rd+len(reps))
    check(len(reps)==len(ss)-2*rd,('complete cohomology basis',dims,a))
    # Independent ring rule: multiply coefficient polynomials, square-zero u,v,
    # and move v past u with a minus sign. Compare every product modulo boundaries.
    for r,t in product(reps,repeat=2):
        expected={}
        for (b,m),c in r.items():
            for (e,n),f in t.items():
                if m&n:continue
                sign=-1 if (m&2 and n&1) else 1
                cf=old.mul(dims,{b:c},{e:f})
                expected=add(expected,{(z,m|n):sign*v for z,v in cf.items()})
        actual=prod(dims,r,t)
        check(actual==expected,('cohomology multiplication sign',dims,a,r,t))
        check(sparse_rank(boundaries+reps+[actual])==rd+len(reps))
    return {'base':list(dims),'p':p,'quotient_dimension':len(qreps),
      'annihilator_dimension':len(ann),'cohomology_dimension':len(reps),'products':len(reps)**2}

def massey_row():
    dims=(1,1);a={(1,1):1};D=lambda s:old.boundary(dims,[a],s)
    x=as_base({(1,0):1});y=as_base({(0,1):1});u=gen(dims,0);v=gen(dims,1)
    m=scale(prod(dims,u,y),-1);ind=[prod(dims,x,v),prod(dims,y,v)]
    check(prod(dims,x,y)==apply(u,D));check(not prod(dims,y,y))
    check(not apply(m,D));check(bool(m))
    ss=states(dims,1);bounds=[D(s) for s in ss if old.degree([2],s)==4]
    rk=sparse_rank(bounds+ind)
    check(sparse_rank(bounds+ind+[m])==rk+1,('nonzero Massey coset',m,ind))
    deg3=[s for s in ss if old.degree([2],s)==3]
    check(deg3==[((0,0),1),((0,0),2)])
    check(sparse_rank([D(s) for s in deg3])==1)
    return {'representative':'-y*u','degree':5,'indeterminacy':['x*v','y*v'],
      'indeterminacy_dimension':rk,'rank_with_representative':rk+1,'contains_zero':False}

def run():
    fixtures=[((0,),[],[]),((1,),[1],[{}]),((3,),[1],[{(1,):1}]),
      ((1,1),[1],[{(1,0):1}]),((1,1),[1],[{(0,1):1}]),
      ((1,1),[1],[{(1,0):1,(0,1):1}]),((1,1),[2],[{(1,1):1}]),
      ((1,1),[1,1],[{(1,0):1},{(0,1):1}]),
      ((1,1),[1,2],[{(1,0):1},{(1,1):1}])]
    kernels=[kernel_row(*args) for args in fixtures]
    nonlinear=nonlinear_rows()
    rings=[one_ring_row(*args) for args in [((0,),1,{}),((1,),1,{}),
      ((3,),1,{(1,):1}),((1,1),1,{(1,0):1,(0,1):1}),((1,1),2,{(1,1):1})]]
    massey=massey_row()
    # Same absolute spectrum, different marked original-base kernels.
    sx=old.spectrum((1,1),[1],[{(1,0):1}]);sy=old.spectrum((1,1),[1],[{(0,1):1}])
    check(sx==sy)
    ix=ideal_columns((1,1),[{(1,0):1}]);iy=ideal_columns((1,1),[{(0,1):1}])
    check(sparse_rank(ix+iy)>sparse_rank(ix)==sparse_rank(iy))
    return {'all_passed':True,'assertions':N,'kernel_rows':kernels,'nonlinear_rows':nonlinear,
       'one_handle_rings':rings,'massey':massey,'unmarked_equal_spectrum':sx,
       'bounds':{'kernel':'Nine explicit pure presentations, plus all five nonlinear parameters',
          'nonlinear':'All 256 basis states for each lambda in -2,-1,0,1,2; six odd handles, base P1xP1',
          'rings':'All products of every cohomology basis in five declared one-handle fixtures',
          'secondary':'Complete degree-five Massey coset and degree-three indeterminacy for curvature xy on P1xP1'},
       'scope':'Finite exact evidence; no Lean execution, arbitrary-X proof by sampling, or universal Chow construction'}

if __name__=='__main__':print(json.dumps(run(),separators=(',',':')))
