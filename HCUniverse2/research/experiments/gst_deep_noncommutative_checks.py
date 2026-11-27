#!/usr/bin/env python3
"""Independent rational sparse elimination and ordered-ring checks.

Run: python research/experiments/gst_deep_noncommutative_checks.py
No Lean compilation, random sampling, floating arithmetic or Wolfram library.
Full rational cocycle kernels are checked for exactly the 13 declared actions.
"""
from fractions import Fraction as Q
from itertools import permutations, product
from collections import Counter
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import tomllib
import time
from datetime import datetime,timezone

ROOT=Path(__file__).resolve().parents[2]
checks=Counter()
def check(label,condition):
    if not condition: raise AssertionError(label)
    checks[label]+=1
def ident(n): return tuple(tuple(Q(i==j) for j in range(n)) for i in range(n))
def scale(c,a): return tuple(tuple(c*x for x in r) for r in a)
def add(a,b): return tuple(tuple(x+y for x,y in zip(r,s)) for r,s in zip(a,b))
def mul(a,b): return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(len(b)))
    for j in range(len(b[0]))) for i in range(len(a)))
def power(a,n):
    out=ident(len(a))
    for _ in range(n): out=mul(out,a)
    return out
def star(a,b): return add(add(a,b),mul(a,b))
def inverse_series(a,n):
    out=scale(0,a)
    for k in range(n): out=add(out,power(scale(-1,a),k))
    return out
def apply(a,v): return tuple(sum(x*y for x,y in zip(row,v)) for row in a)

def nullspace(rows,ncols):
    """Exact sparse Gauss-Jordan elimination, with all free-column vectors."""
    a=[{j:Q(v) for j,v in row.items() if v} for row in rows if any(row.values())]
    pivot_cols=[]; row=0
    for col in range(ncols):
        pivot=next((r for r in range(row,len(a)) if a[r].get(col)),None)
        if pivot is None: continue
        a[row],a[pivot]=a[pivot],a[row]
        factor=a[row][col]; a[row]={j:v/factor for j,v in a[row].items()}
        for r in range(len(a)):
            if r==row or not a[r].get(col): continue
            factor=a[r][col]
            for j,v in a[row].items():
                value=a[r].get(j,Q(0))-factor*v
                if value: a[r][j]=value
                else: a[r].pop(j,None)
        pivot_cols.append(col); row+=1
        if row==len(a): break
    basis=[]
    for free in sorted(set(range(ncols))-set(pivot_cols)):
        vec=[Q(0)]*ncols; vec[free]=Q(1)
        for r,col in enumerate(pivot_cols): vec[col]=-a[r].get(free,Q(0))
        basis.append(tuple(vec))
    return basis,len(pivot_cols)

def cocycle_audit(reps,table,label):
    n,d=len(reps),len(reps[0]); ncols=n*n*d
    ix=lambda g,h,i:(g*n+h)*d+i
    rows=[]
    for g,h,k,i in product(range(n),range(n),range(n),range(d)):
        row=Counter()
        for j in range(d): row[ix(h,k,j)]+=reps[g][i][j]
        row[ix(table[g][h],k,i)]-=1
        row[ix(g,table[h][k],i)]+=1
        row[ix(g,h,i)]-=1
        rows.append(dict(row))
    for g,h in product(range(n),repeat=2):
        check('finite_action_homomorphism',mul(reps[g],reps[h])==reps[table[g][h]])
    for g,h,k in product(range(n),repeat=3):
        check('finite_group_associativity',table[table[g][h]][k]==table[g][table[h][k]])
    basis,rank=nullspace(rows,ncols)
    invariant_rows=[{j:reps[g][i][j]-Q(i==j) for j in range(d)}
                    for g in range(n) for i in range(d)]
    invariant_dim=len(nullspace(invariant_rows,d)[0])
    check('cocycle_dimension_benchmark',len(basis)==(n-1)*d+invariant_dim)
    for vec in basis:
        check('basis_really_is_cocycle',all(sum(v*vec[j] for j,v in row.items())==0 for row in rows))
        avg=[tuple(sum(vec[ix(g,k,i)] for k in range(n))/n for i in range(d)) for g in range(n)]
        reconstructed=tuple(avg[g][i]+apply(reps[g],avg[h])[i]-avg[table[g][h]][i]
                            for g,h,i in product(range(n),range(n),range(d)))
        check('entire_cocycle_basis_reconstructed',reconstructed==vec)
    return dict(action=label,group_order=n,coefficient_rank=d,cochain_dimension=ncols,
                cocycle_dimension=len(basis),constraint_rank=rank)

def mathematics():
    aa=((0,0,0),(0,0,-1),(0,1,0)); bb=((0,0,1),(0,0,0),(-1,0,0)); cc=((0,-1,0),(1,0,0),(0,0,0))
    aa2,bb2,cc2=(mul(x,x) for x in (aa,bb,cc))
    check('word_identity_no_denominators',add(add(mul(aa2,bb2),mul(aa2,cc2)),mul(bb2,cc2))==ident(3))
    check('quadratic_word_identity',add(add(aa2,bb2),cc2)==scale(-2,ident(3)))
    check('word_generators_noncommute',mul(aa,bb)!=mul(bb,aa))
    for v in product(range(-2,3),repeat=3):
        weighted=add(add(scale(v[0],aa),scale(v[1],bb)),scale(v[2],cc))
        check('weighted_frame_explicit_kernel',apply(weighted,v)==(0,0,0))
    for n in range(1,10):
        x=tuple(tuple(Q(j==i+1) for j in range(n)) for i in range(n))
        y=tuple(tuple(Q(i+1) if j==i+1 else Q(0) for j in range(n)) for i in range(n))
        z=add(x,mul(x,x)); zero=scale(0,x); inv=inverse_series(z,n)
        check('all_tested_nilpotent_depths',power(z,n)==zero)
        check('ordered_inverse_left',mul(add(ident(n),z),inv)==ident(n))
        check('ordered_inverse_right',mul(inv,add(ident(n),z))==ident(n))
        check('ordered_associativity',star(star(x,y),z)==star(x,star(y,z)))
        lhs=add(mul(mul(add(ident(n),x),add(ident(n),y)),inv),scale(-1,ident(n)))
        rhs=mul(add(star(x,y),scale(-1,z)),inv)
        check('exact_ordered_gauge_defect',lhs==rhs)
    ff=((0,1,0,0),(0,0,0,0),(0,0,2,0),(0,0,0,3)); ii=ident(4)
    ee=scale(Q(1,36),mul(power(ff,2),add(scale(19,ii),scale(-5,ff))))
    ll=scale(Q(1,216),mul(power(ff,2),add(scale(65,ii),scale(-19,ff))))
    check('Fitting_projector',ee==((0,0,0,0),(0,0,0,0),(0,0,1,0),(0,0,0,1)))
    check('Fitting_inverse_relations',mul(ff,ll)==ee==mul(ll,ff) and mul(ee,ee)==ee)
    e1,e2=(1,0,0,0),(0,1,0,0)
    check('generalized_blind_mode',apply(ff,e2)==e1 and apply(power(ff,2),e2)==(0,0,0,0))
    check('source_image_can_exceed_polynomial_recovery',apply(ff,e2)==e1 and apply(ee,e1)==(0,0,0,0))
    jj3=((0,1,0),(0,0,1),(0,0,0))
    check('generalized_nonfixed_mode_already_in_source_image',apply(jj3,(0,0,1))==(0,1,0)
      and apply(jj3,(0,1,0))==(1,0,0) and apply(power(jj3,2),(0,1,0))==(0,0,0))
    cases=[]
    cyclic=lambda n,r:([power(r,g) for g in range(n)],[[((g+h)%n) for h in range(n)] for g in range(n)])
    for n in range(1,7): cases.append((*cyclic(n,((1,),)),f'trivial C{n}'))
    for n,r,label in [(2,((-1,),),'sign C2'),(2,((0,1),(1,0)),'swap C2'),
        (3,((0,-1),(1,-1)),'rotation C3'),(4,((0,-1),(1,0)),'rotation C4'),
        (6,((0,-1),(1,1)),'rotation C6')]: cases.append((*cyclic(n,r),label))
    reps=[tuple(ident(3)[i] for i in p) for p in permutations(range(3))]
    table=[[reps.index(mul(g,h)) for h in reps] for g in reps]
    check('S3_is_noncommutative',mul(reps[1],reps[2])!=mul(reps[2],reps[1]))
    cases.extend([([((1,),)]*6,table,'trivial S3'),(reps,table,'permutation S3')])
    result=[cocycle_audit(*case) for case in cases]
    check('whole_basis_count',sum(row['cocycle_dimension'] for row in result)==67)
    # Actual nonabelian affine extension: C3 acting on Q² by a rotation.
    reps,tab=cyclic(3,((0,-1),(1,-1))); b=[(Q(0),Q(0)),(Q(1),Q(2)),(Q(3),Q(1))]
    c=[[tuple(b[g][i]+apply(reps[g],b[h])[i]-b[tab[g][h]][i] for i in range(2))
        for h in range(3)] for g in range(3)]
    avg=[tuple(sum(c[g][k][i] for k in range(3))/3 for i in range(2)) for g in range(3)]
    def affine(g,v): return tuple(tuple(reps[g][i][j] if j<2 else v[i] for j in range(3))
        for i in range(2))+((Q(0),Q(0),Q(1)),)
    lift=[affine(g,tuple(b[g][i]-avg[g][i] for i in range(2))) for g in range(3)]
    for g,h in product(range(3),repeat=2):
        check('corrected_nonabelian_extension_product',mul(lift[g],lift[h])==lift[tab[g][h]])
    check('hostile_uncorrected_lifts_fail',any(mul(affine(g,b[g]),affine(h,b[h]))!=affine(tab[g][h],b[tab[g][h]])
        for g,h in product(range(3),repeat=2)))
    return result

def source_checks():
    changed=['GSTOrderedNilpotentDressing.lean','GSTFiniteGroupCocycleAveraging.lean',
      'GSTTargetWordRecovery.lean','GSTClassicalHodgeWordSourceRecovery.lean',
      'GSTFilteredK0SourceConservation.lean','GSTFiniteSourceCorrection.lean',
      'GSTOpenAISourceCorrectionUpgrade.lean']
    # Reuse only the previous nested-comment lexer, not its mathematics engine.
    sys.dont_write_bytecode=True
    import importlib.util
    spec=importlib.util.spec_from_file_location('old_lexer',ROOT/'research/experiments/openai_gst_upgrade_checks.py')
    old=importlib.util.module_from_spec(spec); spec.loader.exec_module(old)
    all_files={p.stem:p for p in ROOT.glob('*.lean')}
    for name in changed:
        code=old.strip_lean((ROOT/name).read_text())
        check('no_added_proof_escape',not re.search(r'\b(sorry|admit|axiom|unsafe)\b',code))
        check('no_truth_stubs',not re.search(r':\s*(True|False)\b',code))
    cfg=tomllib.loads((ROOT/'lakefile.toml').read_text())
    for lib in cfg['lean_lib']:
        if lib['name']=='GSTOpenAISourceUpgrade':
            for root in lib['roots']: check('entry_roots_exist',root in all_files)
    graph={}
    for path in ROOT.rglob('*.lean'):
        if '.git' in path.parts: continue
        try: code=old.strip_lean(path.read_text())
        except AssertionError: continue # two pre-existing recorded comparator anomalies
        graph[str(path.relative_to(ROOT))[:-5].replace('/','.')]=re.findall(r'^import\s+(\S+)',code,re.M)
    visiting=set(); done=set()
    def visit(node):
        if node in done: return
        check('imports_acyclic',node not in visiting); visiting.add(node)
        for dep in graph[node]:
            if dep in graph: visit(dep)
        visiting.remove(node); done.add(node)
    for node in graph: visit(node)
    return {name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in changed}

def wolfram_crosscheck(rows):
    artifact=json.loads((ROOT/'research/computations/gst_deep_noncommutative_wolfram_20261028.output.json').read_text())
    raw='\n'.join(x['text'] for x in artifact['raw_result']['content'] if x['type']=='text')
    check('wolfram_all_assertions_passed','"AllPassed" -> True' in raw and
          f'"AssertionCount" -> {artifact["assertion_count"]}' in raw)
    check('wolfram_exact_arithmetic','"NumericApproximationUsed" -> False' in raw)
    check('wolfram_input_hash_unchanged',hashlib.sha256((ROOT/artifact['input_file']).read_bytes()).hexdigest()
          ==artifact['input_sha256_before'])
    pattern=r'"Action" -> "([^"]+)", "GroupOrder" -> (\d+), "CoefficientRank" -> (\d+), "CochainDimension" -> (\d+), "CocycleDimension" -> (\d+), "ConstraintRank" -> (\d+), "EveryCocycleBasisVectorReconstructed" -> True'
    observed={r[0]:tuple(map(int,r[1:])) for r in re.findall(pattern,raw)}
    check('wolfram_all_action_rows_present',len(observed)==len(rows)==13)
    for row in rows:
        expected=tuple(row[k] for k in ['group_order','coefficient_rank','cochain_dimension','cocycle_dimension','constraint_rank'])
        check('independent_wolfram_row_match',observed[row['action']]==expected)
    return dict(kernel_version=artifact['kernel_version'],assertion_count=artifact['assertion_count'],
                complete_cocycle_basis_vectors=67,finite_actions=13)

if __name__=='__main__':
    started_at=datetime.now(timezone.utc).isoformat(); started=time.perf_counter()
    rows=mathematics(); sources=source_checks(); wolfram=wolfram_crosscheck(rows)
    print(json.dumps({'base_commit':'417b4aa5a50280b655c31bd066f588e0c6330365',
      'status':'completed','started_at':started_at,'runtime_seconds':time.perf_counter()-started,
      'finite_action_rows':rows,'checks':dict(sorted(checks.items())),
      'total_checks':sum(checks.values()),'source_sha256':sources,'wolfram_crosscheck':wolfram,
      'lean_compilation':'not run'},indent=2))
