#!/usr/bin/env python3
"""Reproduce exact local assertions and compare pinned actual Wolfram output.
Run: python research/experiments/gst_extension_fold_run.py
"""
from datetime import datetime,timezone
from pathlib import Path
import hashlib
import json
import platform
import re
import subprocess
import sys
import time
import tomllib
from openai_gst_upgrade_checks import strip_lean

ROOT=Path(__file__).resolve().parents[2]
BASE='6191cdc6bb5a3f94d422da4a39ccaa7f6e2008d7'
SCRIPT='research/experiments/gst_extension_fold_checks.py'
WL='research/experiments/gst_extension_fold_wolfram_20261103.wl'
REMOTE='research/computations/gst_extension_fold_wolfram_20261103.output.json'
OUTPUT='research/computations/gst_extension_fold_20261103.independent.output.json'
MANIFEST='research/computations/gst_extension_fold_20261103.manifest.json'
TEX='research/derivations/GST_extension_sensitive_causal_folds_2026_11_03.tex'
LEAN=['GSTFoldPeriodDescent.lean','GSTCausalPairingGraphs.lean',
      'GSTSpatialFoldResearch.lean','waves/GSTNCohomologyV3.lean']
INPUTS=[SCRIPT,str(Path(__file__).relative_to(ROOT)),WL,REMOTE,TEX,*LEAN,
        'lakefile.toml','research/experiments/openai_gst_upgrade_checks.py']
digest=lambda p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest()

def structural():
    files={str(p.relative_to(ROOT)):p for p in ROOT.rglob('*.lean') if '.git' not in p.parts}
    graph={};anomalies=[]
    for name,p in sorted(files.items()):
        try:code=strip_lean(p.read_text())
        except AssertionError:
            old=subprocess.check_output(['git','show',BASE+':'+name],cwd=ROOT)
            if old!=p.read_bytes():raise RuntimeError('changed malformed Lean comment: '+name)
            anomalies.append(name);continue
        graph[name[:-5].replace('/','.')]=re.findall(r'^import\s+(\S+)',code,re.M)
    active=set();done=set()
    def visit(n):
        if n in done:return
        if n in active:raise RuntimeError('local import cycle '+n)
        active.add(n)
        for d in graph[n]:
            if d in graph:visit(d)
        active.remove(n);done.add(n)
    for n in graph:visit(n)
    for name in LEAN:
        code=strip_lean((ROOT/name).read_text())
        if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',code):
            raise RuntimeError('proof escape '+name)
        if re.search(r':\s*(True|False)\b',code):raise RuntimeError('truth stub '+name)
    cfg=tomllib.loads((ROOT/'lakefile.toml').read_text())
    roots=next(x['roots'] for x in cfg['lean_lib'] if x['name']=='GSTSpatialFoldUpgrade')
    for mod in ['GSTFoldPeriodDescent','GSTCausalPairingGraphs']:
        if mod not in roots:raise RuntimeError('missing root '+mod)
    environments=[]
    for kind,name in re.findall(r'\\(begin|end)\{([^}]+)\}',(ROOT/TEX).read_text()):
        if kind=='begin':environments.append(name)
        elif not environments or environments.pop()!=name:raise RuntimeError('LaTeX nesting')
    if environments:raise RuntimeError('LaTeX unclosed')
    subprocess.run(['git','diff','--check'],cwd=ROOT,check=True,stdout=subprocess.PIPE)
    texfiles=sorted(p for p in ROOT.rglob('*.tex') if '.git' not in p.parts)
    inventory=hashlib.sha256()
    for p in sorted([*files.values(),*texfiles]):
        inventory.update(str(p.relative_to(ROOT)).encode()+b'\0'+hashlib.sha256(p.read_bytes()).digest())
    return {'lean_files':len(files),'latex_files':len(texfiles),'parsed_import_nodes':len(graph),
      'preexisting_unchanged_lexical_anomalies':anomalies,
      'lean_latex_inventory_sha256':inventory.hexdigest(),
      'inventory_scope':'all source bytes enumerated/hashed and Lean imports parsed; targeted semantic review only, not every proof reviewed'}

if __name__=='__main__':
    before={p:digest(p) for p in INPUTS}
    started=datetime.now(timezone.utc).isoformat();t=time.perf_counter()
    argv=[sys.executable,SCRIPT]
    run=subprocess.run(argv,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if run.returncode:
        sys.stderr.buffer.write(run.stderr);raise SystemExit(run.returncode)
    result=json.loads(run.stdout)
    remote=json.loads((ROOT/REMOTE).read_text())
    rawtext='\n'.join(x['text'] for x in remote['raw_result']['content'] if x['type']=='text')
    raw=json.loads(json.loads(rawtext.split('Out[1]=',1)[1].strip()))
    if raw!=remote['parsed_result']:raise RuntimeError('raw/parsed mismatch')
    if remote['input_sha256_before']!=before[WL]:raise RuntimeError('stale Wolfram source')
    if raw['all_passed'] is not True or result['all_passed'] is not True:raise RuntimeError('suite failed')
    for key in ['period_rows','tensor_rows','irrational_cross_count','exterior_term_counts']:
        if raw[key]!=result[key]:raise RuntimeError('independent disagreement: '+key)
    result['all_remote_tables_match']=True;result['source_integrity']=structural()
    (ROOT/OUTPUT).write_text(json.dumps(result,indent=2)+'\n')
    after={p:digest(p) for p in INPUTS}
    if before!=after:raise RuntimeError('inputs changed')
    elapsed=time.perf_counter()-t
    evidence={
      'schema_version':2,'claim_id':'GST-EXTENSION-SENSITIVE-CAUSAL-FOLDS-20261103',
      'repository':{'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
        'dirty':bool(subprocess.check_output(['git','status','--porcelain'],cwd=ROOT))},
      'command':argv,
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
        {'name':'Wolfram Language remote kernel','version':raw['kernel_version']}],
        'hardware':platform.machine()+'; remote hardware not exposed'},
      'mathematics':{
        'assertion_tested':'Finite exact period/monodromy coefficient equivalence, irrational-shift rational cross-Hodge control, three-charge tensor kernels and noncrossing graph ranks, explicit isogeny lattice denominators, exterior Koszul sign and pair-norm checks.',
        'coefficient_domain':'Q, Z, Q(i,sqrt(2)), exact integer exterior and tensor coordinates',
        'conventions':'a_i b_i has integral one; factor-ordered exterior orientation. Bracket amplitudes are commutative tensor polynomials and actual divisor products retain Koszul signs. Tensor test operators are sums of single-factor Lie operators, not tensor powers.',
        'inputs':INPUTS,
        'bounds':{'periods':'n,m=1..3, four declared rational offset pairs, all A,B,C,D=-1..1, evaluated at z=i,2i,1+i',
          'irrational_control':'all 625 A,B,C,D=-2..2 at (tau1,tau2)=(i,i+sqrt2)',
          'tensor_arities':'all m=0..8 including odd arities and vacuum; every recursively enumerated noncrossing matching',
          'matrix_covariance':'all 625 2x2 integer matrices with entries -2..2 on fixed vectors (2,-1),(-3,2)',
          'exterior_period_orientation':'all 81 coefficient quadruples -1..1 at formal rational period values 2,3; sign controls are exterior algebra assertions'},
        'non_claims':['No Lean compilation or kernel axiom audit','No universal original-X source construction',
          'No finite table replaces an all-arity proof','No global novelty claim',
          'All-source byte/lexical inventory is not semantic review of every proof',
          'A rational class that loses Hodge type is not an HC counterexample']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':elapsed,'exit_status':run.returncode,'status':'completed',
        'resource_limits':{'memory_bytes':None,'cpu_seconds':None,'max_cores':None,'max_threads':None}},
      'outputs':[{'path':OUTPUT,'sha256':digest(OUTPUT),'kind':'result'}],
      'checks':['All remote tables reparsed from raw output and matched to independent Python',
        'Sparse rational elimination versus KroneckerProduct and NullSpace',
        'Independent field arithmetic versus Wolfram RootReduce',
        'Actual exterior orientation checked rather than assumed from commutative bracket formulas',
        'Changed Lean escape scan; full parsed local import acyclicity; LaTeX environment balance; whitespace'],
      'result':'implementation and finite assertion verified in the stated ranges',
      'residual_risks':['Lean remains uncompiled at owner request','Hand geometry and invariant-theory transfer are self-reviewed',
        'No scheme or analytic-family Lean instance claimed','Remote process exit status not exposed'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[OUTPUT],
      'remote_evaluation':{'input_sha256_before':before[WL],'kernel_process_exit_status':None,
        'kernel_runtime_seconds':raw['runtime_seconds'],'assertion_count':raw['assertion_count']}}
    (ROOT/MANIFEST).write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':run.returncode,
      'python_checks':result['total_checks'],'wolfram_assertions':raw['assertion_count'],
      'all_tables_match':True,'source_integrity':result['source_integrity'],'manifest':MANIFEST}))
