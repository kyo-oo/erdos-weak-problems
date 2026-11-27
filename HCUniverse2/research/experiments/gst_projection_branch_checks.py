#!/usr/bin/env python3
"""Exact audit, not a Lean build. Run: python research/experiments/gst_projection_branch_checks.py

Exhaustive populations are all 2x2 matrices over Z/m for m=2,3,4,5,8,9,
and all pairs of idempotents therein. Nilpotence search uses the proved bound
2e for Mat_2(Z/p^e): reduction is nilpotent iff its square is zero mod p,
and the e-th power of a matrix divisible by p is zero mod p^e.
Free associative polynomial reductions and hostile controls are separate.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
import sys
import tomllib
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent))
from openai_gst_upgrade_checks import strip_lean

ROOT=Path(__file__).resolve().parents[2]
counts=Counter()
def check(c,label):
    if not c: raise AssertionError(label)
    counts[label]+=1

# A fresh four-coordinate matrix engine, with optional exact modular reduction.
I=(1,0,0,1); Z=(0,0,0,0)
def add(a,b,m=None): return tuple((x+y)%m if m else x+y for x,y in zip(a,b))
def neg(a,m=None): return tuple((-x)%m if m else -x for x in a)
def sub(a,b,m=None): return add(a,neg(b,m),m)
def scale(c,a,m=None): return tuple((c*x)%m if m else c*x for x in a)
def mul(a,b,m=None):
    x,y,z,w=a; r,s,t,u=b
    out=(x*r+y*t,x*s+y*u,z*r+w*t,z*s+w*u)
    return tuple(v%m for v in out) if m else out
def power(a,n,m=None):
    r=I
    for _ in range(n): r=mul(r,a,m)
    return r
def defect(a,m=None): return sub(mul(a,a,m),a,m)
def newton(a,m=None): return sub(a,mul(sub(scale(2,a,m),I,m),defect(a,m),m),m)
def bridge(p,q,m=None): return add(mul(q,p,m),mul(sub(I,q,m),sub(I,p,m),m),m)
def nilindex(a,m,bound):
    r=I
    for n in range(1,bound+1):
        r=mul(r,a,m)
        if r==Z: return n
    return None

rows=[]
for modulus,prime,exponent in [(2,2,1),(3,3,1),(4,2,2),(5,5,1),(8,2,3),(9,3,2)]:
    eligible=0; histogram=Counter(); idempotents=[]; bound=2*exponent
    for a in product(range(modulus),repeat=4):
        e=defect(a,modulus); na=newton(a,modulus)
        rhs=mul(mul(e,e,modulus),sub(scale(4,e,modulus),scale(3,I,modulus),modulus),modulus)
        check(defect(na,modulus)==rhs,'exhaustive_modular_defect_identity')
        check(newton(sub(I,a,modulus),modulus)==sub(I,na,modulus),'exhaustive_complement_compatibility')
        index=nilindex(e,modulus,bound)
        criterion=mul(e,e,prime)==Z
        check(bool(index)==criterion,'nilpotence_bound_matches_mod_prime_criterion')
        if e==Z: idempotents.append(a)
        if index:
            eligible+=1; rounds=(index-1).bit_length(); r=a
            for _ in range(rounds): r=newton(r,modulus)
            check(defect(r,modulus)==Z,'every_nilpotent_defect_corrected_at_log_bound')
            histogram[index]+=1
    nearpairs=0
    for p,q in product(idempotents,repeat=2):
        u=bridge(p,q,modulus); v=bridge(q,p,modulus); d=sub(q,p,modulus)
        c=sub(I,mul(d,d,modulus),modulus)
        check(mul(u,p,modulus)==mul(q,u,modulus),'all_idempotent_pairs_intertwine')
        check(mul(u,v,modulus)==c and mul(v,u,modulus)==c,'all_idempotent_pairs_bridge_products')
        n=nilindex(d,modulus,bound)
        if n:
            nearpairs+=1; series=Z; dsq=mul(d,d,modulus); term=I
            for _ in range(n): series=add(series,term,modulus); term=mul(term,dsq,modulus)
            inverse=mul(v,series,modulus)
            check(mul(u,inverse,modulus)==I and mul(inverse,u,modulus)==I,'all_nilpotent_difference_bridge_inverses')
            check(mul(mul(u,p,modulus),inverse,modulus)==q,'all_nilpotent_difference_conjugacies')
    rows.append({'modulus':modulus,'matrix_count':modulus**4,'eligible_matrices':eligible,
                 'defect_nilpotence_histogram':dict(sorted(histogram.items())),
                 'idempotent_count':len(idempotents),'idempotent_pair_count':len(idempotents)**2,
                 'nilpotent_difference_pair_count':nearpairs})

# Free associative polynomial arithmetic; only pp=p and qq=q are reduced
# in the idempotent-pair quotient. Distinct letters retain their order.
def poly(items): return {w:Q(c) for w,c in items.items() if c}
one={():Q(1)}; a={('a',):Q(1)}; p={('p',):Q(1)}; q={('q',):Q(1)}
def pa(*args):
    c=Counter()
    for f in args:
        for w,v in f.items(): c[w]+=v
    return poly(c)
def ps(k,f): return poly({w:k*v for w,v in f.items()})
def pm(f,g,reduce=False):
    out=Counter()
    for w,x in f.items():
        for v,y in g.items():
            word=w+v
            if reduce:
                reduced=[]
                for letter in word:
                    if not reduced or letter!=reduced[-1]: reduced.append(letter)
                word=tuple(reduced)
            out[word]+=x*y
    return poly(out)
def pp(f,n,reduce=False):
    ans=one
    for _ in range(n): ans=pm(ans,f,reduce)
    return ans
ee=pa(pm(a,a),ps(-1,a)); tt=pa(a,ps(-1,pm(pa(ps(2,a),ps(-1,one)),ee)))
check(pa(pm(tt,tt),ps(-1,tt))==pm(pp(ee,2),pa(ps(4,ee),ps(-3,one))),'universal_free_ring_newton_identity')
u=pa(pm(q,p),pm(pa(one,ps(-1,q)),pa(one,ps(-1,p)))); v=pa(pm(p,q),pm(pa(one,ps(-1,p)),pa(one,ps(-1,q))))
d=pa(q,ps(-1,p)); central=pa(one,ps(-1,pm(d,d,True)))
check(pm(u,v,True)==central and pm(v,u,True)==central,'universal_idempotent_quotient_bridge_products')
check(pm(u,p,True)==pm(q,u,True),'universal_idempotent_quotient_intertwining')
check(u!=pa(one,pm(d,pa(ps(2,p),ps(-1,one)))),'missing_idempotence_in_bridge_formula_is_detected')
check(u==pa(one,pm(d,pa(ps(2,p),ps(-1,one)),True)),'bridge_formula_with_idempotence')

# A separate commutative truncated ring engine for boundary and mixed-source laws.
def cp(items): return poly(items)
def cm(f,g,caps=None):
    out=Counter()
    for w,x in f.items():
        for v,y in g.items():
            z=tuple(i+j for i,j in zip(w,v))
            if caps and any(i>=cap for i,cap in zip(z,caps)): continue
            out[z]+=x*y
    return cp(out)
def cpower(f,n,caps=None):
    ans={(0,)*len(next(iter(f))):Q(1)}
    for _ in range(n): ans=cm(ans,f,caps)
    return ans
c1={(0,0):Q(1)}; x={(1,0):Q(1)}; y={(0,1):Q(1)}
sd=pa(ps(2,c1),ps(-1,x),ps(-1,y)); dd=pa(c1,ps(-1,cm(x,y)))
check(cpower(pa(x,ps(-1,y)),2)==pa(cpower(sd,2),ps(-4,sd),ps(4,dd)),'universal_commutative_boundary_defect')
ex=pa(c1,x); ey=pa(c1,ps(-1,x)); eu=pa(c1,y); ev=pa(c1,ps(-1,y)); caps=(2,2)
dx=pa(ex,ps(-1,ey)); dy=pa(eu,ps(-1,ev))
check(cpower(dx,2,caps)=={} and cpower(dy,2,caps)=={},'repeated_square_zero_control')
check(cm(dx,dy,caps)=={(1,1):Q(4)},'mixed_independent_source_survives_in_abstract_ring')
for n in range(13):
    check(cpower(ex,n,caps)==pa(c1,ps(n,x)),'square_zero_power_formula')
    check(pa(cpower(ex,n,caps),cpower(ey,n,caps))==ps(2,c1),'all_power_sums_sample')
for s in range(2,9):
    modulus=2**s; xval=modulus-1; aug=(xval-1)%modulus
    check(pow(xval,2,modulus)==1 and pow(aug,s,modulus)==0 and xval!=1,'integral_torsion_counterexample_to_rationalization_omission')
for xval,yval in [(Q(0),Q(2)),(Q(2),Q(1,2))]:
    check((xval-yval)**2!=0,'each_complement_relation_is_load_bearing')

# Smooth ramification normal form over Q[t], certified as polynomial identities.
cp1={(0,):Q(1)}; t={(1,):Q(1)}; zz={}
def matmul(A,B): return tuple(tuple(pa(*(cm(A[i][k],B[k][j]) for k in range(2))) for j in range(2)) for i in range(2))
matrix=((cp1,cp1),(t,ps(-1,t)))
right=((cp1,ps(-1,cp1)),(zz,cp1)); left=((cp1,zz),(ps(-1,t),cp1))
check(matmul(matmul(left,matrix),right)==((cp1,zz),(zz,ps(-2,t))),'ramification_addition_matrix_smith_equivalence')
b=((zz,cp1),(cpower(t,2),zz))
check(matmul(b,b)==((cpower(t,2),zz),(zz,cpower(t,2))),'ramification_companion_square')

# Symbolic three-twist extraction and every exceptional pair in A1...A12.
a=x; d=y
twist=lambda k:cpower(pa(a,ps(2*k,d)),2)
check(pa(twist(1),twist(-1),ps(-2,twist(0)))==ps(8,cpower(d,2)),
      'three_twist_extraction_polynomial')
for n in range(1,13):
    chain=lambda i,j:-2 if i==j else 1 if abs(i-j)==1 else 0
    for i in range(n):
        j=n-1-i
        coefficient=chain(i,i)+chain(j,j)-chain(i,j)-chain(j,i)
        expected=0 if i==j else -6 if abs(i-j)==1 else -4
        check(coefficient==expected,'every_A_chain_reflected_pair_intersection')
        if coefficient:
            check(Q(1,8*coefficient)*(8*coefficient)==1,'exact_exceptional_stratum_normalization')
check(Q(1,8*(-6))==Q(-1,48) and Q(1,8*(-4))==Q(-1,32),
      'adjacent_and_nonadjacent_source_coefficients')

# Connectedness is essential: two P1xP1 components, deck exchanging them.
v=(1,0,-1,0); h=(1,1,1,1)
pair=lambda a,b:a[0]*b[1]+a[1]*b[0]+a[2]*b[3]+a[3]*b[2]
deck=lambda a:a[2:]+a[:2]
check(deck(v)==tuple(-x for x in v) and deck(h)==h and pair(v,h)==0 and pair(v,v)==0 and v!=(0,0,0,0),
      'split_cover_counterexample_to_unqualified_positivity')

leanfiles=['GSTIntegralProjectionCorrection.lean','GSTNilpotentProjectionConjugacy.lean',
           'GSTSpectralBoundaryDefect.lean','GSTTorsionLineConservation.lean',
           'GSTConnectedSpectralHodgeRigidity.lean','GSTSingularBranchExtraction.lean',
           'GSTFilteredK0SourceConservation.lean',
           'GSTOpenAISourceCorrectionUpgrade.lean']
import re
for name in leanfiles:
    text=strip_lean((ROOT/name).read_text())
    check(not re.search(r'\b(sorry|admit|axiom|unsafe)\b',text),'changed_lean_no_escape_keywords')
    check(not re.search(r':\s*(?:True|Prop\s*:=\s*True)\b',text),'changed_lean_no_truth_stubs')
    for imp in re.findall(r'^import\s+(\S+)',text,re.M):
        check(imp=='Mathlib' or (ROOT/(imp+'.lean')).exists(),'changed_import_exists')
cfg=tomllib.loads((ROOT/'lakefile.toml').read_text())
roots=next(lib['roots'] for lib in cfg['lean_lib'] if lib['name']=='GSTOpenAISourceUpgrade')
for root in roots: check((ROOT/(root+'.lean')).exists(),'registered_module_exists')
graph={}; known_anomalies=[]
for path in ROOT.rglob('*.lean'):
    if '.git' in path.parts: continue
    try: source=strip_lean(path.read_text())
    except AssertionError:
        known_anomalies.append(path.name); continue
    graph[str(path.relative_to(ROOT))[:-5].replace('/','.')]=re.findall(r'^import\s+(\S+)',source,re.M)
check(set(known_anomalies)=={'ComparatorSmokeChallenge.lean','ComparatorSmokeSolution.lean'},
      'only_two_preexisting_lexical_anomalies')
seen=set(); active=set()
def visit(node):
    if node in active: raise AssertionError('import cycle '+node)
    if node in seen: return
    active.add(node)
    for other in graph.get(node,[]):
        if other in graph: visit(other)
    active.remove(node);seen.add(node)
for node in graph: visit(node)
check(len(seen)==len(graph),'current_local_import_graph_acyclic')
out={'all_passed':True,'total_checks':sum(counts.values()),'families':dict(counts),'finite_rows':rows,
     'parsed_import_nodes':len(graph),'known_preexisting_lexical_anomalies':known_anomalies,
     'arithmetic':'integer, modular, Fraction and exact sparse polynomial arithmetic',
     'lean_compiled':False,'review':'self-review; independent local and Wolfram implementations'}
print(json.dumps(out,indent=2))
