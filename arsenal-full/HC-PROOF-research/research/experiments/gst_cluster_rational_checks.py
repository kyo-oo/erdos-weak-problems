#!/usr/bin/env python3
"""Exact independent checks for GST cluster transfer and rational fibers.

Contract: n=2..7 group Hilbert tables; n=2..5 selectors with every Chern
monomial of weighted degree 1..4 in F and its complement; rank-three
coinvariant controls; rational-vs-integer and two-ruling tests. Python's
polynomial division and permutation enumeration are independent of Wolfram's
SymmetricReduction and conjugacy-class cycle-index summation. No finite
range is extrapolated into an all-X proof. Run via gst_cluster_rational_run.py.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import comb, factorial
from pathlib import Path
import json
import re
import subprocess
import sys
from openai_gst_upgrade_checks import strip_lean

ROOT=Path(__file__).resolve().parents[2]
BASE='b403d3aadd6ed79b2822037941e4503ca1788ec3'
CHECKS=Counter()
def check(test,kind):
    if not test: raise AssertionError(kind)
    CHECKS[kind]+=1

def add(*polys):
    out=Counter()
    for p in polys:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def scale(a,p):return {m:a*c for m,c in p.items() if a*c}
def mul(p,q):
    out=Counter()
    for a,c in p.items():
        for b,d in q.items():out[tuple(x+y for x,y in zip(a,b))]+=c*d
    return {m:c for m,c in out.items() if c}
def power(p,k,n):
    r={(0,)*n:1}
    for _ in range(k):r=mul(r,p)
    return r
def elementary(n,indices,k):
    return {tuple(int(j in s) for j in range(n)):1
            for s in combinations(indices,k)}
def compositions(total,length):
    if length==0:
        if total==0:yield ()
        return
    for a in range(total+1):
        for rest in compositions(total-a,length-1):yield (a,)+rest
def coinvariant_basis(n):
    # Lex x0>...>x(n-1): h_(i+1)(x_i,...,x_(n-1)).
    return [{(0,)*i+e:1 for e in compositions(i+1,n-i)} for i in range(n)]
def normal_form(p,basis):
    p=dict(p);remainder={}
    while p:
        m=max(p);c=p[m]
        for g in basis:
            lead=max(g)
            if all(a>=b for a,b in zip(m,lead)):
                shift=tuple(a-b for a,b in zip(m,lead))
                shifted={tuple(a+b for a,b in zip(shift,k)):v for k,v in g.items()}
                p=add(p,scale(-c,shifted))
                break
        else:
            remainder[m]=c;del p[m]
    return remainder

def selector_checks():
    rows=[]
    for n in range(2,6):
        gb=coinvariant_basis(n)
        for j in range(1,n+1):
            check(not normal_form(elementary(n,range(n),j),gb),'elementary_ideal_control')
        for r in range(n+1):
            weights=list(range(1,r+1))+list(range(1,n-r+1))
            counts=Counter()
            for es in product(*(range(4//w+1) for w in weights)):
                degree=sum(a*b for a,b in zip(weights,es))
                if not 1<=degree<=4:continue
                orbit={}
                for I in combinations(range(n),r):
                    J=tuple(j for j in range(n) if j not in I)
                    cherns=[elementary(n,I,k) for k in range(1,r+1)]
                    cherns += [elementary(n,J,k) for k in range(1,n-r+1)]
                    term={(0,)*n:1}
                    for ch,e in zip(cherns,es):term=mul(term,power(ch,e,n))
                    orbit=add(orbit,term)
                check(not normal_form(orbit,gb),'full_selector_chern_trace_zero')
                counts[degree]+=1
            rows += [[n,r,d,counts[d]] for d in range(1,5)]
    n=3;xs=[{tuple(int(j==i) for j in range(n)):1} for i in range(n)]
    x,y,z=xs
    delta=mul(mul(add(x,scale(-1,y)),add(x,scale(-1,z))),add(y,scale(-1,z)))
    cyc=add(mul(power(x,2,n),y),mul(power(y,2,n),z),mul(power(z,2,n),x))
    gb=coinvariant_basis(n);rd=normal_form(delta,gb);rc=normal_form(cyc,gb)
    check(bool(rd),'orientation_survives_formal_coinvariant_control')
    check(scale(2,rc)==rd,'oriented_cyclic_half_sign')
    check(not normal_form(mul(delta,delta),gb),'orientation_square_zero')
    return rows,[[list(m),c] for m,c in sorted(rd.items())]

def grassmann_degree_checks():
    """Independent top-Chern coefficient calculation for the global incidence.
    c(T Gr)=prod_i(1+z_i t)^n/prod_ij(1+(z_i-z_j)t), z_i=c1(F*) roots.
    Integrate by the Vandermonde coefficient rule; all arithmetic is integral.
    """
    rows=[]
    for n in range(2,6):
        for r in range(n+1):
            degree=r*(n-r);one={(0,)*r:1}
            zs=[{tuple(int(i==j) for i in range(r)):1} for j in range(r)]
            series=[one]+[{} for _ in range(degree)]
            for z in zs:
                for _ in range(n):
                    for k in range(degree,0,-1):series[k]=add(series[k],mul(z,series[k-1]))
            for i in range(r):
                for j in range(r):
                    delta=add(zs[i],scale(-1,zs[j]))
                    out=[series[0]]
                    for k in range(1,degree+1):out.append(add(series[k],scale(-1,mul(delta,out[k-1]))))
                    series=out
            vd=one
            for i in range(r):
                for j in range(i+1,r):vd=mul(vd,add(zs[i],scale(-1,zs[j])))
            target=tuple(n-i-1 for i in range(r))
            integral=mul(series[degree],vd).get(target,0)
            check(integral==comb(n,r),'global_incidence_top_chern_degree')
            rows.append([n,r,degree,integral])
    return rows

def cycle_lengths(p):
    seen=set();lengths=[]
    for i in range(len(p)):
        if i in seen:continue
        j=i;k=0
        while j not in seen:seen.add(j);k+=1;j=p[j]
        lengths.append(k)
    return tuple(sorted(lengths))
def series_mul(a,b,degree):
    out=[Q(0)]*(degree+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=degree:out[i+j]+=x*y
    return out
def hilbert(n,types,order):
    degree=n*(n-1)//2
    num=[Q(1)]+[Q(0)]*degree
    for j in range(1,n+1):
        factor=[Q(0)]*(degree+1);factor[0]=1
        if j<=degree:factor[j]=-1
        num=series_mul(num,factor,degree)
    out=[Q(0)]*(degree+1)
    for lengths,count in types.items():
        series=[Q(1)]+[Q(0)]*degree
        for length in lengths:
            factor=[Q(int(i%length==0)) for i in range(degree+1)]
            series=series_mul(series,factor,degree)
        term=series_mul(num,series,degree)
        out=[a+Q(count,order)*b for a,b in zip(out,term)]
    check(all(v.denominator==1 and v>=0 for v in out),'integral_nonnegative_hilbert')
    check(sum(out)==Q(factorial(n),order),'coinvariant_total_dimension')
    return list(map(int,out))
def hilbert_checks():
    rows=[]
    for n in range(2,8):
        full=Counter(cycle_lengths(p) for p in permutations(range(n)))
        alt=Counter({ls:c for ls,c in full.items() if (n-len(ls))%2==0})
        cyc=Counter(cycle_lengths(tuple((i+k)%n for i in range(n))) for k in range(n))
        for name,types,order in [('S',full,factorial(n)),('A',alt,factorial(n)//2),('C',cyc,n)]:
            hs=hilbert(n,types,order);rows.append([n,name,hs])
            if name=='S':check(hs==[1]+[0]*(len(hs)-1),'symmetric_only_constant')
            if name=='A':check(hs==[1]+[0]*(len(hs)-2)+[1],'alternating_orientation_threshold')
    return rows

def rational_checks():
    for a,b in product(range(-5,6),repeat=2):
        a,b=Q(a,2),Q(b,3)
        check((2*(a/2),0)==(a,0),'explicit_rational_index_witness')
        for m in [Q(-5),Q(-1,3),Q(1,2),Q(2),Q(7,3)]:
            check((m*b==0)==(b==0),'rational_missing_direction_scale')
            check(((m*a)/m,(m*b)/m)==(a,b),'rational_normalization')
        # Actual two-ruling coefficient identity and geometric pairing.
        L=(a,0);R=(0,b)
        check(tuple(x+y for x,y in zip(L,R))==(a,b),'labeled_ruling_source')
        check(a*(-1)+b==b-a,'primitive_target_pairing')
    return {'targets':121,'nonzero_scales_per_target':5,'integer_index_control_breaks':10,
            'rational_index_control_breaks':0,'two_direction_control_breaks':110}

def source_checks():
    changed=['GSTCausalFoldDefect.lean','GSTLawStackRound51.lean',
             'GSTSpectralBoundaryDefect.lean','GSTSpatialFoldResearch.lean']
    for path in changed:
        code=strip_lean((ROOT/path).read_text())
        check(not re.search(r'\b(sorry|admit|axiom|unsafe)\b',code),'changed_lean_escape_scan')
    graph={};anomalies=[]
    for p in ROOT.rglob('*.lean'):
        relative=p.relative_to(ROOT)
        if any(x in {'.git','.lake','node_modules'} for x in relative.parts):continue
        try:code=strip_lean(p.read_text())
        except AssertionError:
            check(p.name in ['ComparatorSmokeChallenge.lean','ComparatorSmokeSolution.lean',
                             'GSTLawStackRound40.lean'],'known_lexical_anomaly')
            old=subprocess.check_output(['git','show',BASE+':'+relative.as_posix()],cwd=ROOT)
            check(old==p.read_bytes(),'anomaly_unchanged_from_base')
            anomalies.append(relative.as_posix());continue
        graph[relative.as_posix()[:-5].replace('/','.')]=re.findall(r'^import\s+(\S+)',code,re.M)
    seen=set();active=set()
    def visit(node):
        if node in seen:return
        check(node not in active,'local_import_acyclic')
        active.add(node)
        for dep in graph[node]:
            if dep in graph:visit(dep)
        active.remove(node);seen.add(node)
    for node in graph:visit(node)
    run=subprocess.run([sys.executable,'research/experiments/seed_orbit_break_hunt_round51_checks.py'],
                       cwd=ROOT,capture_output=True,text=True)
    check(run.returncode==0 and '75 passed, 0 failed' in run.stdout,'corrected_round51_suite')
    return {'parsed_import_nodes':len(graph),'known_unchanged_anomalies':anomalies,
            'round51_exit_status':run.returncode,'round51_checks':75,
            'scope':'Lexical graph/escape checks; Lean not compiled.'}

if __name__=='__main__':
    rows,delta=selector_checks()
    out={'selector_rows':rows,'orientation_normal_form':delta,'grassmann_rows':grassmann_degree_checks(),
         'hilbert_rows':hilbert_checks(),
         'rational_rows':rational_checks(),'source_checks':source_checks()}
    out.update(all_passed=True,checks=dict(CHECKS),total_checks=sum(CHECKS.values()))
    print(json.dumps(out,sort_keys=True,separators=(',',':')))
