#!/usr/bin/env python3
"""Exact base-coupled/higher fold audit; no Lean or network use.

Run: python research/experiments/gst_base_coupled_higher_fold_checks.py
Bases are products of declared projective spaces, with their full rational
cohomology rings. These fixtures audit the uniform hand formulas, not replace
their arbitrary-X proofs. Two independently written boundary representations
and elimination algorithms are compared on every fixture.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from math import gcd
import json

CHECKS=0
def check(value,context=None):
    global CHECKS
    CHECKS+=1
    if not value:raise AssertionError((CHECKS,context))

def sparse_rank(columns):
    pivots={}
    for column in columns:
        v={i:Q(a) for i,a in column.items() if a}
        while v:
            i=min(v)
            if i not in pivots:
                a=v[i];pivots[i]={j:b/a for j,b in v.items()};break
            a=v[i]
            for j,b in pivots[i].items():
                v[j]=v.get(j,Q(0))-a*b
                if not v[j]:del v[j]
    return len(pivots)

def dense_rref(rows,ncols):
    # Row operations rather than the independent sparse column algorithm.
    a=[[Q(x) for x in row] for row in rows];pivots=[];r=0
    for c in range(ncols):
        pivot=next((i for i in range(r,len(a)) if a[i][c]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        q=a[r][c];a[r]=[x/q for x in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][c]:
                q=a[i][c];a[i]=[x-q*y for x,y in zip(a[i],a[r])]
        pivots.append(c);r+=1
    return a,pivots

def basis(dims):return list(product(*(range(n+1) for n in dims)))
def times_monomial(dims,a,b):
    c=tuple(x+y for x,y in zip(a,b))
    return c if all(x<=n for x,n in zip(c,dims)) else None

def boundary(state,dims,curvatures):
    exp,mask=state;out=defaultdict(int)
    for a,curvature in enumerate(curvatures):
        u=2*a
        if not (mask>>u)&1:continue
        sign=(-1)**((mask&((1<<u)-1)).bit_count())
        for mon,c in curvature.items():
            target=times_monomial(dims,exp,mon)
            if target is not None:out[(target,mask^(1<<u))]+=sign*c
    return {i:c for i,c in out.items() if c}

def independent_boundary(state,dims,curvatures):
    exp,mask=state;word=[i for i in range(2*len(curvatures)) if mask&(1<<i)]
    out=defaultdict(int)
    for position,letter in enumerate(word):
        if letter%2:continue
        rest=word[:position]+word[position+1:]
        target_mask=sum(2**i for i in rest)
        for mon,c in curvatures[letter//2].items():
            target=tuple(exp[j]+mon[j] for j in range(len(dims)))
            if any(target[j]>dims[j] for j in range(len(dims))):continue
            out[(target,target_mask)]+=(-1)**position*c
    return {i:c for i,c in out.items() if c}

def spectrum(dims,p,curvatures):
    r=len(curvatures);d=2*p-1;top=2*sum(dims)+2*r*d
    groups=[[] for _ in range(top+1)]
    for exp in basis(dims):
        for mask in range(1<<(2*r)):
            groups[2*sum(exp)+d*mask.bit_count()].append((exp,mask))
    ranks=[]
    for k,states in enumerate(groups):
        columns=[];target=groups[k+1] if k<top else []
        target_index={s:i for i,s in enumerate(target)}
        for s in states:
            col=boundary(s,dims,curvatures)
            check(col==independent_boundary(s,dims,curvatures),('boundary',dims,p,s))
            squared=defaultdict(int)
            for t,c in col.items():
                check(t in target_index,('absolute degree',k,t))
                for tt,cc in boundary(t,dims,curvatures).items():squared[tt]+=c*cc
            check(not any(squared.values()),('square',s))
            columns.append({target_index[t]:c for t,c in col.items()})
        rank=sparse_rank(columns)
        rows=[[col.get(i,0) for col in columns] for i in range(len(target))]
        independent_rank=len(dense_rref(rows,len(columns))[1])
        check(rank==independent_rank,('rank',dims,p,k))
        ranks.append(rank)
    betti=[len(g)-ranks[k]-(ranks[k-1] if k else 0) for k,g in enumerate(groups)]
    check(betti==betti[::-1],('duality',dims,p))
    check(sum((-1)**k*b for k,b in enumerate(betti))==0 if r else True)
    monomials=[a for a in basis(dims) if sum(a)==p]
    rho=sparse_rank([{i:c.get(a,0) for i,a in enumerate(monomials)} for c in curvatures])
    base_d=sum(2*sum(a)==d for a in basis(dims))
    check(betti[d]==base_d+2*r-rho)
    check((betti[d]-base_d)-2*(r-rho)==rho)
    return {'dims':list(dims),'p':p,'classes':[
        [[list(a),v] for a,v in sorted(c.items())] for c in curvatures],
        'betti':betti,'boundary_ranks':ranks,'curvature_rank':rho,
        'max_retained_handles':r-rho}

def one_handle_formula(dims,p,curvature):
    d=2*p-1;bb=basis(dims);n=2*sum(dims);b={k:sum(2*sum(a)==k for a in bb) for k in range(n+1)}
    ranks={}
    for j in range(n+1):
        cols=[]
        for a in bb:
            if 2*sum(a)!=j:continue
            col=defaultdict(int)
            for mon,c in curvature.items():
                t=times_monomial(dims,a,mon)
                if t is not None:col[t]+=c
            cols.append(col)
        ranks[j]=sparse_rank(cols)
    result=[b.get(k,0)+2*b.get(k-d,0)+b.get(k-2*d,0)
       -ranks.get(k-2*p,0)-ranks.get(k-d,0)-ranks.get(k-d-2*p,0)-ranks.get(k-2*d,0)
       for k in range(n+2*d+1)]
    return result,[ranks[j] for j in range(n+1)]

def relation_audit():
    histogram=[0,0,0]
    for entries in product([-1,0,1],repeat=6):
        C=[list(entries[:3]),list(entries[3:])]
        rr,pivots=dense_rref(C,3);rho=len(pivots);histogram[rho]+=1
        free=[i for i in range(3) if i not in pivots];relations=[]
        for j in free:
            v=[Q(0)]*3;v[j]=1
            for row,col in enumerate(pivots):v[col]=-rr[row][j]
            relations.append(v)
        check(len(relations)==3-rho)
        for coeff in product([-1,0,1],repeat=len(relations)):
            row=[sum(a*v[j] for a,v in zip(coeff,relations)) for j in range(3)]
            check(all(sum(x*y for x,y in zip(c,row))==0 for c in C))
            # Free entries recover the unique factorization coefficients.
            check([row[j] for j in free]==list(coeff))
        for row in product([-1,0,1],repeat=3):
            if any(sum(x*y for x,y in zip(c,row)) for c in C):continue
            check(list(row)==[sum(row[j]*v[k] for j,v in zip(free,relations)) for k in range(3)])
    # Integral hostile case: clearing a rational nullspace basis separately
    # yields an index-two lattice and a disconnected torus kernel.
    C=[2,3,5];naive=[[-3,2,0],[-5,0,2]];primitive=[[-3,2,0],[-1,-1,1]]
    def minor_gcd(rows):
        minors=[rows[0][i]*rows[1][j]-rows[0][j]*rows[1][i] for i,j in [(0,1),(0,2),(1,2)]]
        out=0
        for x in minors:out=gcd(out,x)
        return abs(out)
    check(minor_gcd(naive)==2)
    check(minor_gcd(primitive)==1)
    check(all(sum(a*b for a,b in zip(C,row))==0 for row in primitive))
    check(sum(a*b for a,b in zip(C,[-1,1,0]))==1)
    for x in product(range(-3,4),repeat=3):
        if sum(a*b for a,b in zip(C,x)):continue
        # x=a*(-3,2,0)+b*(-1,-1,1); b=x2, a=(x1+x2)/2.
        check((x[1]+x[2])%2==0)
        a=(x[1]+x[2])//2;b=x[2]
        check(list(x)==[a*u+b*v for u,v in zip(*primitive)])
    return {'all_2_by_3_matrices':729,'rank_histogram':histogram,
            'integral_control':{'chern_row':C,'naive_minor_gcd':2,'saturated_minor_gcd':1,
                                'saturated_rows':primitive}}

def mixed_shear_audit(dims,pi,pj,c,t):
    """Check the full graded chain isomorphism, not just its spectrum."""
    e=defaultdict(int)
    for a,x in c.items():
        for b,y in t.items():
            mon=times_monomial(dims,a,b)
            if mon is not None:e[mon]+=x*y
    old=[c,dict(e)];new=[c,{}];weights=[2*pi-1]*2+[2*pj-1]*2
    top=2*sum(dims)+sum(weights);groups=[[] for _ in range(top+1)]
    for exp in basis(dims):
        for mask in range(16):
            groups[2*sum(exp)+sum(w for i,w in enumerate(weights) if mask>>i&1)].append((exp,mask))
    zero=(0,)*len(dims)
    def shear(state):
        exp,mask=state;poly={(exp,0):1}
        for letter in range(4):
            if not mask>>letter&1:continue
            choices=[(zero,letter,1)]
            if letter>=2:choices.extend((a,letter-2,-b) for a,b in t.items())
            out=defaultdict(int)
            for (a,m),x in poly.items():
                for b,j,y in choices:
                    if m>>j&1:continue
                    mon=times_monomial(dims,a,b)
                    if mon is None:continue
                    sign=(-1)**sum(bool(m>>i&1) for i in range(j+1,4))
                    out[(mon,m|(1<<j))]+=sign*x*y
            poly={a:b for a,b in out.items() if b}
        return poly
    def apply(poly,operation):
        out=defaultdict(int)
        for s,a in poly.items():
            for tt,b in operation(s).items():out[tt]+=a*b
        return {s:a for s,a in out.items() if a}
    def cohom(curvatures):
        ranks=[]
        for k,states in enumerate(groups):
            target={s:i for i,s in enumerate(groups[k+1])} if k<top else {}
            cols=[]
            for s in states:
                col=boundary(s,dims,curvatures)
                check(col==independent_boundary(s,dims,curvatures))
                check(not apply(col,lambda x:boundary(x,dims,curvatures)))
                check(all(tt in target for tt in col),('mixed absolute degree',s))
                cols.append({target[tt]:a for tt,a in col.items()})
            rank=sparse_rank(cols)
            dense=[[col.get(i,0) for col in cols] for i in range(len(target))]
            check(rank==len(dense_rref(dense,len(cols))[1]))
            ranks.append(rank)
        return [len(g)-ranks[k]-(ranks[k-1] if k else 0) for k,g in enumerate(groups)]
    for k,states in enumerate(groups):
        for s in states:
            image=shear(s)
            check(all(tt in groups[k] for tt in image),('shear degree',s))
            check(apply(image,lambda x:boundary(x,dims,old))==
                  apply(boundary(s,dims,new),shear),('graded chain map',dims,pi,pj,s))
    a,b=cohom(old),cohom(new)
    check(a==b)
    check(a==a[::-1])
    return {'dims':list(dims),'codimensions':[pi,pj],
            'coefficient':[[list(a),b] for a,b in t.items()],
            'betti':a,'chain_isomorphism_all_basis_states':True}

def noncommutative_packet_audit():
    Z=(0,0,0,0);I=(1,0,0,1);N=(0,1,0,0);T=(0,0,1,0);D=(1,0,0,-1)
    matrices=[Z,I,N,T,D]
    add=lambda a,b:tuple(x+y for x,y in zip(a,b))
    neg=lambda a:tuple(-x for x in a)
    sub=lambda a,b:add(a,neg(b))
    def mul(a,b):return (a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],
                         a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])
    def boundary(c,e,x):return (add(mul(c,x[1]),mul(e,x[2])),
                                neg(mul(e,x[3])),mul(c,x[3]),Z)
    def shear(t,x):return (x[0],sub(x[1],mul(t,x[2])),x[2],x[3])
    packets=[(N,T,D,I),(T,I,N,D),(I,N,T,Z),(Z,Z,I,I)]
    for c in matrices:
        for a,b in product([-1,0,1],repeat=2):
            t=add(tuple(a*x for x in I),tuple(b*x for x in c))
            check(mul(c,t)==mul(t,c))
            for x in packets:
                check(boundary(c,t,boundary(c,t,x))==(Z,Z,Z,Z))
                check(shear(neg(t),shear(t,x))==x)
                for e in matrices:
                    check(boundary(c,e,shear(t,x))==shear(t,boundary(c,sub(e,mul(t,c)),x)))
    hostile=(Z,Z,Z,I)
    check(boundary(N,T,boundary(N,T,hostile))!=(Z,Z,Z,Z))
    check(boundary(N,Z,shear(T,(Z,Z,I,Z)))!=shear(T,boundary(N,neg(mul(T,N)),(Z,Z,I,Z))))
    return {'coefficient_ring':'2x2 integer matrices','curvatures':5,
            'commuting_shear_pairs':45,'packets':4,'noncommuting_hostile_controls':2}

def run():
    rows=[];rank_tables=[];base_list=[(1,),(2,),(3,),(1,1),(2,1),(2,2),(1,1,1)]
    for dims in base_list:
        for p in range(1,min(sum(dims),3)+1):
            mons=[a for a in basis(dims) if sum(a)==p]
            classes=[{}, {mons[0]:1}]
            if len(mons)>1:classes += [{mons[-1]:1},{mons[0]:1,mons[-1]:1}]
            for c in classes:
                row=spectrum(dims,p,[c]);predicted,ranks=one_handle_formula(dims,p,c)
                check(row['betti']==predicted,('formula',dims,p,c))
                rows.append(row);rank_tables.append(ranks)
            c={mons[0]:1};twice={mons[0]:2}
            dep=spectrum(dims,p,[c,twice]);flat=spectrum(dims,p,[c,{}])
            check(dep['betti']==flat['betti'],('shear',dims,p))
            rows.extend([dep,flat])
            if len(mons)>1:rows.append(spectrum(dims,p,[c,{mons[-1]:1}]))
    # Empty curvature list and point base are actual unit controls.
    rows.append(spectrum((1,),1,[]))
    rows.append(spectrum((0,),1,[{}]))
    coupled=[row for row in rows if row['dims']==[2,1] and row['p']==1 and len(row['classes'])==1]
    check(coupled[1]['betti']!=coupled[2]['betti'])
    surface=next(row for row in rows if row['dims']==[1,1] and row['p']==1 and row['classes']==[[[[0,1],1]]])
    check(surface['betti']==[1,1,1,2,1,1,1])
    relations=relation_audit();mixed=[]
    for dims in [(3,),(2,1),(2,2),(1,1,1)]:
        for pi,pj in [(1,2),(1,3),(2,3)]:
            candidates=[(a,b) for a in basis(dims) for b in basis(dims)
                if sum(a)==pi and sum(b)==pj-pi and times_monomial(dims,a,b) is not None]
            if candidates:
                a,b=candidates[0]
                mixed.append(mixed_shear_audit(dims,pi,pj,{a:1},{b:1}))
    packets=noncommutative_packet_audit()
    return {'all_passed':True,'assertion_count':CHECKS,'spectral_rows':rows,
            'one_handle_cup_rank_tables':rank_tables,'relations':relations,'mixed_cup_shears':mixed,
            'noncommutative_packets':packets,
            'bounds':{'bases':[list(x) for x in base_list],
                      'higher_degree':'p=1..min(dim X,3); all cochain degrees retained',
                      'curvatures':'zero, first/last monomial, their sum, paired dependence and independence',
                      'quotients':'all 729 2x3 matrices in {-1,0,1}; coefficient and row cube {-1,0,1}',
                      'integral_control':'C=(2,3,5), every integral relation in [-3,3]^3',
                      'mixed_shears':'4 declared bases, codimensions (1,2),(1,3),(2,3); full basis chain identity'},
            'interpretation':'Exact fixture support for the hand general theorems; not a Lean build or worldwide novelty check'}

if __name__=='__main__':print(json.dumps(run(),separators=(',',':')))
