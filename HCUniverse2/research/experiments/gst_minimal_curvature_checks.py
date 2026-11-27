#!/usr/bin/env python3
"""Exact diagnostics for the finite mixed-degree curvature normal form.
Run: python research/experiments/gst_minimal_curvature_checks.py
Finite truncated polynomial fixtures; no Lean, network, or floating arithmetic.
The universal theorem and actual-space comparison are hand arguments.
"""
import sys
sys.dont_write_bytecode=True
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import json
from gst_base_coupled_higher_fold_checks import basis,times_monomial,sparse_rank,dense_rref

COUNT=0
def check(p,context=None):
    global COUNT
    COUNT+=1
    if not p:raise AssertionError((COUNT,context))
def clean(x):return {k:Q(v) for k,v in x.items() if v}
def plus(a,b,scale=1):
    c=defaultdict(Q,a)
    for k,v in b.items():c[k]+=scale*v
    return clean(c)
def mul(dims,a,b):
    out=defaultdict(Q)
    for x,c in a.items():
        for y,e in b.items():
            z=times_monomial(dims,x,y)
            if z is not None:out[z]+=c*e
    return clean(out)
def rank(cols):return sparse_rank(cols)
def span_solution(cols,target,bb):
    # Independently solved augmented row system; free parameters set to zero.
    rows=[[c.get(x,0) for c in cols]+[target.get(x,0)] for x in bb]
    rr,pivots=dense_rref(rows,len(cols)+1)
    if len(cols) in pivots:return None
    ans=[Q(0)]*len(cols)
    for row,p in enumerate(pivots):ans[p]=rr[row][-1]
    return ans

def ideal_quotient_profile(dims,ps,cs):
    # Whole ideal and m*I, computed directly, not from greedy generators.
    bb=basis(dims);ideal=[];positive=[]
    for c in cs:
        for a in bb:
            v=mul(dims,{a:1},c);ideal.append(v)
            if sum(a):positive.append(v)
    prof={}
    for q in range(1,sum(dims)+1):
        at=lambda col:{a:v for a,v in col.items() if sum(a)==q}
        n=rank([at(c) for c in ideal])-rank([at(c) for c in positive])
        if n:prof[q]=n
    return prof,rank(ideal)

def reduce_curvatures(dims,ps,cs):
    bb=basis(dims);retained=[];relations={}
    for j in sorted(range(len(cs)),key=lambda i:(ps[i],i)):
        candidates=[];labels=[]
        for i in retained:
            for a in bb:
                if sum(a)==ps[j]-ps[i]:
                    candidates.append(mul(dims,{a:1},cs[i]));labels.append((i,a))
        sol=span_solution(candidates,cs[j],bb)
        if sol is None:retained.append(j)
        else:
            rel={i:{} for i in retained}
            for value,(i,a) in zip(sol,labels):
                if value:rel[i][a]=value
            relations[j]={i:v for i,v in rel.items() if v}
            reconstructed={}
            for i,a in relations[j].items():reconstructed=plus(reconstructed,mul(dims,a,cs[i]))
            check(reconstructed==clean(cs[j]),('relation',dims,ps,cs,j))
    profile={q:sum(ps[i]==q for i in retained) for q in sorted(set(ps[i] for i in retained))}
    expected,ideal_dim=ideal_quotient_profile(dims,ps,cs)
    check(profile==expected,('indecomposable profile',dims,ps,cs,profile,expected))
    # Compare sparse column span with augmented dense solver on all decisions.
    for j,rel in relations.items():
        cols=[mul(dims,{a:1},cs[i]) for i in retained for a in bb if sum(a)==ps[j]-ps[i]]
        check(rank(cols+[cs[j]])==rank(cols))
    return retained,relations,profile,ideal_dim

def exterior_mul(dims,left,right):
    out=defaultdict(Q)
    for (a,m),c in left.items():
        for (b,n),e in right.items():
            if m&n:continue
            z=times_monomial(dims,a,b)
            if z is None:continue
            inversions=sum((n&((1<<i)-1)).bit_count() for i in range(m.bit_length()) if m>>i&1)
            out[(z,m|n)]+=(-1)**inversions*c*e
    return clean(out)

def boundary(dims,cs,state):
    a,m=state;out=defaultdict(Q)
    for i,c in enumerate(cs):
        bit=2*i
        if not m>>bit&1:continue
        sign=(-1)**((m&((1<<bit)-1)).bit_count())
        for b,v in c.items():
            z=times_monomial(dims,a,b)
            if z is not None:out[(z,m^(1<<bit))]+=sign*v
    return clean(out)

def word_boundary(dims,cs,state):
    # Separate ordered-word implementation, including absolute degree checks.
    a,mask=state;letters=[i for i in range(2*len(cs)) if mask>>i&1];out={}
    for place,letter in enumerate(letters):
        if letter%2:continue
        rest=letters[:place]+letters[place+1:];m=sum(1<<x for x in rest)
        for b,v in cs[letter//2].items():
            z=tuple(x+y for x,y in zip(a,b))
            if all(x<=cap for x,cap in zip(z,dims)):
                out=plus(out,{(z,m):(-1)**place*v})
    return out

def linear_apply(poly,fn):
    result={}
    for state,c in poly.items():result=plus(result,fn(state),c)
    return result

def change_basis(dims,r,relations,state,sign=-1):
    exp,mask=state;out={(exp,0):Q(1)};zero=(0,)*len(dims)
    for bit in range(2*r):
        if not mask>>bit&1:continue
        image={(zero,1<<bit):Q(1)}
        for i,a in relations.get(bit//2,{}).items():
            for mon,c in a.items():image=plus(image,{(mon,1<<(2*i+bit%2)):sign*c})
        out=exterior_mul(dims,out,image)
    return out

def degree(ps,state):
    exp,mask=state
    return 2*sum(exp)+sum((2*ps[i//2]-1) for i in range(2*len(ps)) if mask>>i&1)

def spectrum(dims,ps,cs):
    top=2*sum(dims)+2*sum(2*p-1 for p in ps)
    groups=[[] for _ in range(top+1)]
    for a in basis(dims):
        for mask in range(1<<(2*len(ps))):groups[degree(ps,(a,mask))].append((a,mask))
    ranks=[]
    for k,states in enumerate(groups):
        target={x:i for i,x in enumerate(groups[k+1] if k<top else [])};cols=[]
        for state in states:
            col=boundary(dims,cs,state)
            check(col==word_boundary(dims,cs,state),('word boundary',dims,ps,state))
            check(all(degree(ps,t)==k+1 for t in col),('degree',k,state))
            check(not linear_apply(col,lambda s:boundary(dims,cs,s)),('d^2',state))
            cols.append({target[t]:c for t,c in col.items()})
        sr=rank(cols)
        rows=[[c.get(i,0) for c in cols] for i in range(len(target))]
        check(sr==len(dense_rref(rows,len(cols))[1]),('independent rank',k))
        ranks.append(sr)
    betti=[len(states)-ranks[k]-(ranks[k-1] if k else 0) for k,states in enumerate(groups)]
    check(all(x>=0 for x in betti))
    check(betti==betti[::-1],('duality',dims,ps,cs))
    return betti

def convolve(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out

def full_audit(dims,ps,cs):
    retained,relations,mu,ideal_dim=reduce_curvatures(dims,ps,cs)
    reduced=[c if i in retained else {} for i,c in enumerate(cs)]
    states=[(a,m) for a in basis(dims) for m in range(1<<(2*len(cs)))]
    old=lambda s:boundary(dims,cs,s);new=lambda s:boundary(dims,reduced,s)
    forward=lambda s:change_basis(dims,len(cs),relations,s)
    inverse=lambda s:change_basis(dims,len(cs),relations,s,1)
    for state in states:
        image=forward(state)
        check(all(degree(ps,t)==degree(ps,state) for t in image),('map degree',state))
        check(linear_apply(image,old)==linear_apply(new(state),forward),('chain map',state))
        check(linear_apply(image,inverse)=={state:1},('left inverse',state))
        check(linear_apply(inverse(state),forward)=={state:1},('right inverse',state))
    orig=spectrum(dims,ps,cs);small=spectrum(dims,[ps[i] for i in retained],[cs[i] for i in retained])
    factored=small
    for j in relations:
        d=2*ps[j]-1;factor=[0]*(2*d+1);factor[0]=1;factor[d]=2;factor[2*d]=1
        factored=convolve(factored,factor)
    check(orig==factored,('full cohomology factor',dims,ps,cs,mu))
    return {'base':list(dims),'weights':ps,'mu':mu,'ideal_dimension':ideal_dim,
        'active_indices':retained,'flat_indices':sorted(relations),'states':len(states),'betti':orig}

def run():
    rows=[]
    fixtures=[((0,),[],[]),((1,),[1],[{}]),
      ((3,),[1,2,3],[{(1,):1},{(2,):1},{(3,):1}]),
      ((1,1),[1,1,2],[{(1,0):1},{(0,1):1},{(1,1):1}]),
      ((1,1),[1,1,1],[{(1,0):1,(0,1):1},{(1,0):1},{(0,1):1}]),
      ((2,1),[1,2,2],[{(1,0):1},{(2,0):1},{(1,1):1}]),
      ((2,),[1,2,2],[{(1,):1},{(2,):1},{}]),
      ((1,1),[2,2],[{(1,1):1},{(1,1):-2}])]
    for args in fixtures:rows.append(full_audit(*args))
    degree_one=[clean({(1,0):a,(0,1):b}) for a,b in product([-1,0,1],repeat=2)]
    histogram={};cases=0
    for cs in product(degree_one,repeat=3):
        _,_,mu,_=reduce_curvatures((1,1),[1,1,1],cs)
        k=sum(mu.values());histogram[k]=histogram.get(k,0)+1;cases+=1
    for a,b in product(degree_one,repeat=2):
        for z in [-1,0,1]:
            _,_,mu,_=reduce_curvatures((1,1),[1,1,2],[a,b,clean({(1,1):z})]);cases+=1
    # All bounded positive-degree b and all bounded elements x, not only Hodge-homogeneous x.
    nil_cases=0;zero={(0,0):Q(1)};mon=basis((1,1))
    for coeff in product([-1,0,1],repeat=3):
        b=clean(dict(zip([(0,1),(1,0),(1,1)],coeff)))
        check(not mul((1,1),mul((1,1),b,b),b),('nilpotence',b))
        for xc in product([-1,0,1],repeat=4):
            x=clean(dict(zip(mon,xc)));difference=plus(x,mul((1,1),b,x),-1)
            check((not difference)==(not x),('nilpotent fixed point',b,x));nil_cases+=1
    # Hostile controls: ideal dimension is not mu, and closed is not a free basis row.
    check(rows[2]['ideal_dimension']==3 and rows[2]['mu']=={1:1})
    dims=(1,1);cs=[{(1,0):1},{(0,1):1}]
    syzygy={((0,1),1):1,((1,0),4):-1}
    check(not linear_apply(syzygy,lambda s:boundary(dims,cs,s)))
    check(all(sum(a)>0 for a,_ in syzygy))
    check(ideal_quotient_profile(dims,[1,1],cs)[0]=={1:2})
    # Non-unit coefficients obstruct an invertible row: reduction modulo m is zero.
    check([a.get((0,0),0) for a in [{(0,1):1},{(1,0):-1}]]==[0,0])
    return {'all_passed':True,'assertion_count':COUNT,'full_normal_form_rows':rows,
      'normal_form_cases':cases,'same_degree_mu_histogram':histogram,
      'nilpotent_fixed_point_cases':nil_cases,'hostile_controls_passed':True,
      'bounds':{'normal_forms':'All 729 triples of degree-one curvatures and all 243 lists of weights (1,1,2), coefficients -1,0,1 on P1xP1',
        'chain_maps':'All basis states of eight explicit fixtures; both inverse orders and full absolute degrees',
        'nilpotent_guard':'27 positive-degree coefficients b and all 81 elements x in the cube -1,0,1 of Q[x,y]/(x^2,y^2)',
        'cohomology':'All degrees and two exact rank algorithms on all eight full fixtures'},
      'non_claims':['No Lean compilation','Finite polynomial fixtures do not prove arbitrary-X geometry',
        'No universal Chow constructor','No historical novelty or external-engine claim']}

if __name__=='__main__':print(json.dumps(run(),separators=(',',':')))
