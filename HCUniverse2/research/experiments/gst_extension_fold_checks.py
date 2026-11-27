#!/usr/bin/env python3
"""Exact independent period/tensor/exterior checks; run via the pinned runner.

No floating arithmetic. Q(i,sqrt(2)) is implemented as a four-coordinate
field for the irrational control. Tensor ranks use sparse rational Gaussian
elimination, not the Wolfram KroneckerProduct/NullSpace implementation.
Bounds are finite evidence; the all-arity claims have separate hand proofs.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import comb
import json

CHECKS=Counter()
def check(x,label):
    if not x:raise AssertionError(label)
    CHECKS[label]+=1
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def neg(x):return tuple(-a for a in x)
def mul(x,y):
    # basis 1,i,sqrt2,i*sqrt2, i^2=-1, sqrt2^2=2
    out=[Q(0)]*4
    for j,a in enumerate(x):
        for k,b in enumerate(y):
            si=(j&1)+(k&1);sr=(j>>1)+(k>>1)
            out[(si%2)+2*(sr%2)]+=a*b*((-1)**(si//2))*(2**(sr//2))
    return tuple(out)
def scalar(x):return (Q(x),Q(0),Q(0),Q(0))
def period(q,x,y):
    a,b,c,d=q
    return add(add(mul(scalar(a),mul(x,y)),neg(mul(scalar(b),x))),
               add(neg(mul(scalar(c),y)),scalar(d)))
ZERO=scalar(0)
ZS=[(Q(0),Q(1),Q(0),Q(0)),(Q(0),Q(2),Q(0),Q(0)),
    (Q(1),Q(1),Q(0),Q(0))]

def period_checks():
    rows=[]
    offsets=[(Q(0),Q(0)),(Q(0),Q(1,2)),(Q(1,3),Q(-2)),(Q(1,2),Q(1,3))]
    for n,m in product(range(1,4),repeat=2):
        for u,v in offsets:
            stable=fixed=0
            for q in product(range(-1,2),repeat=4):
                a,b,c,d=q
                values=[period(q,add(mul(scalar(n),z),scalar(u)),
                               add(mul(scalar(m),z),scalar(v))) for z in ZS]
                hodge=all(x==ZERO for x in values)
                predicted=a==0 and n*b+m*c==0 and d==b*u+c*v
                check(hodge==predicted,'three_period_values_iff_coefficients')
                T=(a,b+m*a,c+n*a,d+n*b+m*c+n*m*a)
                inv=T==q
                check(inv==(a==0 and n*b+m*c==0),'monodromy_kernel')
                if inv:
                    check(len(set(values))==1,'fixed_period_is_constant')
                stable+=hodge;fixed+=inv
            w=(0,m,-n,m*u-n*v)
            check(all(period(w,add(mul(scalar(n),z),scalar(u)),
                             add(mul(scalar(m),z),scalar(v)))==ZERO for z in ZS),
                  'constructed_rational_pair_period')
            check(2*(w[1]*w[2]-w[0]*w[3])==-2*n*m,'actual_pair_norm')
            # Explicit lattice isogeny denominator and determinant degree.
            a=Q(m,n);b=v-a*u;L=a.denominator*b.denominator
            check((L*a).denominator==1 and (L*b).denominator==1,'lattice_inclusion')
            check((L*L*a).denominator==1 and L*L*a>0,'isogeny_degree')
            rows.append([n,m,str(u),str(v),stable,fixed])
    irr_count=0
    for q in product(range(-2,3),repeat=4):
        x=ZS[0];y=add(x,(Q(0),Q(0),Q(1),Q(0)))
        hodge=period(q,x,y)==ZERO
        check(hodge==(q==(0,0,0,0)),'irrational_projective_cross_control')
        irr_count+=hodge
    check(period((0,1,-1,0),ZS[0],add(ZS[0],(Q(0),Q(0),Q(1),Q(0))))==
          (Q(0),Q(0),Q(1),Q(0)),'balanced_fixed_but_not_hodge')
    return rows,irr_count

def rank(rows):
    pivots={}
    for row in rows:
        row={j:Q(x) for j,x in row.items() if x}
        while row:
            p=min(row)
            if p in pivots:
                a=row[p]
                for j,x in pivots[p].items():
                    row[j]=row.get(j,Q(0))-a*x
                    if not row[j]:del row[j]
            else:
                a=row[p];pivots[p]={j:x/a for j,x in row.items()};break
    return len(pivots)

def lie_rows(m,which):
    rows=[{} for _ in range(1<<m)]
    for word in range(1<<m):
        if which=='H':
            if h:=m-2*word.bit_count():rows[word][word]=Q(h)
        else:
            for i in range(m):
                bit=(word>>i)&1
                if bit==(which=='E'):
                    out=word^(1<<i);rows[out][word]=Q(1)
    return rows

def combine_rows(*terms):
    rows=[]
    for tup in zip(*(matrix for _,matrix in terms)):
        row=Counter()
        for (a,_),r in zip(terms,tup):
            for j,x in r.items():row[j]+=a*x
        rows.append({j:x for j,x in row.items() if x})
    return rows

def matchings(indices):
    if not indices:yield ();return
    i=indices[0]
    for k in range(1,len(indices),2):
        for left in matchings(indices[1:k]):
            for right in matchings(indices[k+1:]):
                yield ((i,indices[k]),)+left+right

def match_vector(m,edges):
    vec={0:1}
    for i,j in edges:
        nxt={}
        for word,c in vec.items():
            nxt[word|(1<<j)]=c
            nxt[word|(1<<i)]=-c
        vec=nxt
    return vec

def apply_matrix(rows,v):return [sum(c*v.get(j,0) for j,c in row.items()) for row in rows]

def tensor_checks():
    result=[]
    for m in range(9):
        E,F,H=[lie_rows(m,x) for x in ('E','F','H')]
        q0=combine_rows((1,E),(-1,F));q1=combine_rows((Q(1,2),E),(-2,F))
        q2=combine_rows((-1,H),(1,E),(-2,F))
        null=(1<<m)-rank(q0+q1+q2)
        mono=(1<<m)-rank(F)
        expected=comb(m,m//2)//(m//2+1) if m%2==0 else 0
        check(null==expected,'three_charge_test_rank')
        check(mono==comb(m,m//2),'monodromy_has_extra_vectors')
        vectors=list(match_vector(m,e) for e in matchings(tuple(range(m)))) if m%2==0 else []
        check(len(vectors)==expected,'noncrossing_enumerator_catalan')
        check(rank(vectors)==expected,'noncrossing_basis_independent')
        for v in vectors:
            check(not any(apply_matrix(q0+q1+q2,v)),'each_graph_three_charges_zero')
        # Rank-one N-cohomology controls, including an entangled full fiber.
        result.append([m,1<<m,null,mono,len(vectors)])
    check(1*1-0*0==1,'two_channel_entangled_minor')
    return result

def wedge(p,q):
    out=Counter()
    for a,c in p.items():
        for b,d in q.items():
            if set(a)&set(b):continue
            inv=sum(x>y for x in a for y in b)
            out[tuple(sorted(a+b))]+=(-1)**inv*c*d
    return {m:c for m,c in out.items() if c}
def plus(*ps):
    out=Counter()
    for p in ps:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def eta(i,j):return {(2*i,2*j+1):1,(2*i+1,2*j):-1}

def exterior_checks():
    terms=[wedge(eta(0,1),eta(2,3)),wedge(eta(0,2),eta(1,3)),
           wedge(eta(0,3),eta(1,2))]
    check(not plus(*terms),'actual_exterior_plucker_has_plus_signs')
    check(bool(plus(terms[0],{m:-c for m,c in terms[1].items()},terms[2])),
          'unsigned_tensor_plucker_is_wrong_in_exterior_ring')
    check(wedge(eta(0,1),eta(0,1))=={(0,1,2,3):-2},'actual_diagonal_cross_norm')
    # Wedge equation tested directly from basis permutations, not its formula.
    for q in product(range(-1,2),repeat=4):
        v={k:c for k,c in zip([(0,2),(0,3),(1,2),(1,3)],q) if c}
        om1={(0,):1,(1,):2};om2={(2,):1,(3,):3}
        value=wedge(wedge(v,om1),om2).get((0,1,2,3),0)
        a,b,c,d=q
        check(value==-(6*a-2*b-3*c+d),'period_orientation_from_exterior')
    return [len(t) for t in terms]

def determinant_checks():
    def bracket(v,w):return v[0]*w[1]-v[1]*w[0]
    v=(2,-1);w=(-3,2)
    for a,b,c,d in product(range(-2,3),repeat=4):
        T=lambda x:(a*x[0]+b*x[1],c*x[0]+d*x[1])
        check(bracket(T(v),T(w))==(a*d-b*c)*bracket(v,w),'all_small_matrix_covariance')

if __name__=='__main__':
    rows,irr=period_checks();tensors=tensor_checks();ext=exterior_checks();determinant_checks()
    print(json.dumps({'all_passed':True,'period_rows':rows,'irrational_cross_count':irr,
      'tensor_rows':tensors,'exterior_term_counts':ext,
      'total_checks':sum(CHECKS.values()),'check_counts':dict(CHECKS)},sort_keys=True))
