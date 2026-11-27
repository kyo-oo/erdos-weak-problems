#!/usr/bin/env python3
"""Exact independent checks; no Lean compilation or universal-HC certificate.
Run: python research/experiments/gst_spatial_fold_checks.py
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import json
import re
import subprocess
import sys
import tomllib

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from openai_gst_upgrade_checks import strip_lean

checks = Counter()
def check(h, name):
    if not h: raise AssertionError(name)
    checks[name] += 1

def eye(n): return [[F(i == j) for j in range(n)] for i in range(n)]
def add(a,b): return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def neg(a): return [[-x for x in r] for r in a]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]
def tr(a): return [list(r) for r in zip(*a)]
def determinant(a):
    a=[list(map(F,r)) for r in a]; ans=F(1)
    for j in range(len(a)):
        k=next((k for k in range(j,len(a)) if a[k][j]),None)
        if k is None:return F(0)
        if k!=j:a[j],a[k]=a[k],a[j];ans=-ans
        p=a[j][j];ans*=p
        for i in range(j+1,len(a)):
            c=a[i][j]/p
            a[i]=[x-c*y for x,y in zip(a[i],a[j])]
    return ans

def wedge(a,b):
    out=Counter()
    for I,x in a.items():
        for J,y in b.items():
            if set(I)&set(J):continue
            sign=(-1)**sum(i>j for i in I for j in J)
            out[tuple(sorted(I+J))]+=sign*x*y
    return {k:v for k,v in out.items() if v}
def padd(*polys):
    out=Counter()
    for p in polys:
        for k,v in p.items():out[k]+=v
    return {k:v for k,v in out.items() if v}
def pscale(c,a):return {k:c*v for k,v in a.items() if c*v}
def line(j):return {(j,):F(1)}
def sparse_basis(vectors):
    pivots={}
    for v in vectors:
        v={k:F(x) for k,x in v.items() if x}
        while v:
            k=min(v)
            if k not in pivots:
                z=v[k];pivots[k]={j:x/z for j,x in v.items()};break
            c=v[k];v=padd(v,pscale(-c,pivots[k]))
    return list(pivots.values())
def charge(I):
    out={}
    for k,j in enumerate(I):
        # J^* dx=-dy; J^* dy=dx. This is a derivation, not wedge^degree(J).
        replacement=j+1 if j%2==0 else j-1
        p={():F(1)}
        for t,l in enumerate(I):
            p=wedge(p,line(replacement if t==k else l))
        out=padd(out,pscale(-1 if j%2==0 else 1,p))
    return out

def divisors(s):
    D=[wedge(line(2*j),line(2*j+1)) for j in range(s)]
    ans=list(D)
    for j,k in combinations(range(s),2):
        A=wedge(padd(line(2*j),pscale(-1,line(2*k))),
                padd(line(2*j+1),pscale(-1,line(2*k+1))))
        B=wedge(padd(line(2*j),line(2*k+1)),
                padd(line(2*j+1),pscale(-1,line(2*k))))
        ans += [padd(A,pscale(-1,D[j]),pscale(-1,D[k])),
                padd(B,pscale(-1,D[j]),pscale(-1,D[k]))]
    return ans

def exterior_checks():
    rows=[]
    for s in range(5):
        ds=divisors(s);check(len(ds)==s*s,'divisor_population')
        basis=[{():F(1)}]
        for p in range(s+2):
            if p:
                basis=sparse_basis(wedge(a,b) for a in basis for b in ds)
            ambient=list(combinations(range(2*s),2*p))
            rankD=len(sparse_basis(charge(I) for I in ambient))
            expected=comb(s,p)**2 if p<=s else 0
            check(len(ambient)-rankD==expected,'actual_zero_charge_dimension')
            check(len(basis)==expected,'actual_divisor_product_span')
            for v in basis:
                image=padd(*(pscale(c,charge(I)) for I,c in v.items()))
                check(not image,'every_generated_basis_vector_hodge')
            rows.append([s,p,len(ambient),rankD,len(basis)])
    return rows

def rotation_checks():
    rows=[]
    for s in range(1,6):
        n=2*s;J=[[F(0) for _ in range(n)] for _ in range(n)]
        for j in range(s):J[2*j][2*j+1]=-1;J[2*j+1][2*j]=1
        for variant in range(3):
            U=eye(n);Ui=eye(n)
            for k in range(variant+1):
                a=k%n;b=(k+1)%n;c=k+1
                S=eye(n);Si=eye(n);S[a][b]=c;Si[a][b]=-c
                U=mul(S,U);Ui=mul(Ui,Si)
            K=mul(mul(U,J),Ui);G=add(eye(n),mul(tr(K),K));E=mul(tr(K),G)
            check(mul(U,Ui)==eye(n),'unimodular_conjugation')
            check(mul(K,K)==neg(eye(n)),'rotation_square')
            check(tr(E)==neg(E),'polarization_alternating')
            check(mul(mul(tr(K),E),K)==E,'polarization_invariant')
            check(mul(E,K)==G,'polarization_sign')
            minors=[determinant([row[:k] for row in G[:k]]) for k in range(1,n+1)]
            check(all(x>0 for x in minors),'sylvester_exact_positivity')
            check(abs(determinant(sub(K,eye(n))))==2**s,'door_determinant')
            rows.append([s,variant,int(determinant(G)),[int(x) for x in minors]])
    for x,y in product(range(-4,5),repeat=2):
        door=lambda u,v:(-v-u,u-v)
        check(door(y-x,-x-y)==(2*x,2*y),'integral_doubled_witness')
        u,v=F(y-x,2),F(-x-y,2)
        check(door(u,v)==(x,y),'rational_inverse')
        found=any(door(a,b)==(x,y) for a,b in product(range(-8,9),repeat=2))
        check(found==((x+y)%2==0),'integral_door_exhaustive_search')
    return rows

def causal_checks():
    rows=[]
    for n in range(1,5):
        z=[[F(0) for _ in range(n)] for _ in range(n)]
        matrix=lambda t:[[F(((i+2)*(j+1)+t*(i-j+1))%7-3) for j in range(n)] for i in range(n)]
        for length in range(7):
            Js=[matrix(10+j) for j in range(length+1)]
            Ts=[matrix(1+j) for j in range(length)]
            P=eye(n)
            for T in Ts:P=mul(T,P)
            lhs=sub(mul(Js[-1],P),mul(P,Js[0]));rhs=z
            for j,T in enumerate(Ts):
                before=eye(n);after=eye(n)
                for U in Ts[:j]:before=mul(U,before)
                for U in Ts[j+1:]:after=mul(U,after)
                edge=sub(mul(Js[j+1],T),mul(T,Js[j]))
                rhs=add(rhs,mul(mul(after,edge),before))
            check(lhs==rhs,'heterogeneous_causal_telescoping')
            rows.append([n,length,int(sum(x*x for r in lhs for x in r))])
    J=[[F(0),F(-1)],[F(1),F(0)]];T=[[F(1),F(0)],[F(0),F(-1)]]
    check(sub(mul(J,T),mul(T,J))!=[[0,0],[0,0]],'unsafe_edge_control')
    check(mul(T,T)==eye(2),'cancellation_not_edge_safety')
    return rows

def variable_checks():
    rows=[]
    for f,df in product([F(1,2),F(1),F(2),F(3)],[F(-2),F(0),F(1),F(5)]):
        J=[[F(0),-1,0,0],[1,0,0,0],[0,0,0,-1/f],[0,0,f,0]]
        dJ=[[F(0) for _ in range(4)] for _ in range(4)]
        dJ[2][3]=df/f**2;dJ[3][2]=df
        apply=lambda M,v:[sum(a*b for a,b in zip(r,v)) for r in M]
        unit=lambda j:[F(i==j) for i in range(4)]
        bracket=lambda a,da,b,db:[x-y for x,y in zip(apply(db,a),apply(da,b))]
        N=[]
        for i,j in product(range(4),repeat=2):
            X,Y=unit(i),unit(j);JX,JY=apply(J,X),apply(J,Y)
            dJX=[[dJ[r][i] if c==0 else F(0) for c in range(4)] for r in range(4)]
            dJY=[[dJ[r][j] if c==0 else F(0) for c in range(4)] for r in range(4)]
            zero=[[F(0)]*4 for _ in range(4)]
            a=bracket(JX,dJX,JY,dJY)
            b=apply(J,bracket(JX,dJX,Y,zero));c=apply(J,bracket(X,zero,JY,dJY))
            N.append([a[k]-b[k]-c[k] for k in range(4)])
        check(mul(J,J)==neg(eye(4)),'variable_square')
        check(N[2]==[0,0,df/f,0],'independent_vector_field_brackets')
        check(any(any(v) for v in N)==(df!=0),'variable_integrability_discriminator')
        for v in product(range(-1,2),repeat=4):
            Jv=apply(J,v);energy=v[0]*Jv[1]-v[1]*Jv[0]+v[2]*Jv[3]-v[3]*Jv[2]
            check(energy==v[0]**2+v[1]**2+f*v[2]**2+v[3]**2/f,'positive_energy_formula')
            check((energy>0)==any(v),'strict_positive_energy')
        rows.append([str(f),str(df),str(N[2][2])])
    return rows

def source_checks():
    names=['GSTFoldRotation','GSTFoldPolarization','GSTCausalFoldDefect',
           'GSTVariableFoldIntegrability','GSTGraphV2GeneralSpaceRealization','GSTSpatialFoldResearch',
           'GSTLawStackRound51']
    for name in names:
        code=strip_lean((ROOT/(name+'.lean')).read_text())
        check(not re.search(r'\b(sorry|admit|axiom|unsafe)\b',code),'changed_lean_escape_scan')
    config=tomllib.loads((ROOT/'lakefile.toml').read_text())
    target=next(t for t in config['lean_lib'] if t['name']=='GSTSpatialFoldUpgrade')
    check(set(target['roots'])==set(names),'module_registry')
    # Whole-source byte inventory is not semantic proof review.
    files=subprocess.check_output(['git','ls-tree','-r','--name-only',
        '05a27588a17d3f611d2219b5e0b496272a28816a'],cwd=ROOT).decode().splitlines()
    graph={};anomalies=[]
    for path in ROOT.rglob('*.lean'):
        if any(part in {'.git','.lake','node_modules'} for part in path.relative_to(ROOT).parts):continue
        relative=path.relative_to(ROOT).as_posix()
        try:code=strip_lean(path.read_text())
        except AssertionError:
            check(path.name in ['ComparatorSmokeChallenge.lean','ComparatorSmokeSolution.lean',
                               'GSTLawStackRound40.lean'],
                  'known_preexisting_lexical_anomaly')
            baseline=subprocess.check_output(['git','show',
                '05a27588a17d3f611d2219b5e0b496272a28816a:'+relative],cwd=ROOT)
            check(baseline==path.read_bytes(),'lexical_anomaly_unchanged_from_upstream')
            anomalies.append(path.name);continue
        graph[relative[:-5].replace('/','.')]=re.findall(r'^import\s+(\S+)',code,re.M)
    seen=set();active=set()
    def visit(node):
        if node in seen:return
        check(node not in active,'local_import_acyclic')
        active.add(node)
        for dep in graph[node]:
            if dep in graph:visit(dep)
        active.remove(node);seen.add(node)
    for node in graph:visit(node)
    return {'tracked_lean':sum(p.endswith('.lean') for p in files),
            'tracked_tex':sum(p.endswith('.tex') for p in files),
            'inventory_revision':'05a27588a17d3f611d2219b5e0b496272a28816a',
            'current_parsed_import_nodes':len(graph),'unchanged_lexical_anomalies':sorted(anomalies),
            'scope':'Counts and lexical checks only; no full proof review or Lean compilation.'}

if __name__=='__main__':
    result={'rotation_rows':rotation_checks(),'exterior_rows':exterior_checks(),
            'causal_rows':causal_checks(),'variable_rows':variable_checks(),
            'source_inventory':source_checks()}
    result.update(all_passed=True,checks=dict(checks),total_checks=sum(checks.values()))
    print(json.dumps(result,sort_keys=True,separators=(',',':')))
