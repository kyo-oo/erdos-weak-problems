#!/usr/bin/env python3
"""Provenance and static audit for base-coupled/higher GST folds.

Command: python research/experiments/gst_base_coupled_higher_fold_run.py
Does not install/run Lean, invoke CI, or access the network.
"""
from datetime import datetime,timezone
from hashlib import sha256
from pathlib import Path
import importlib.util
import json,platform,re,subprocess,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
BASE='b2de3bdecf4467211702f5d5118577a014170333'
LEAN=['GSTCausalFoldDefect.lean','GSTGradedWorldAlgebra.lean',
      'GSTSpatialFoldResearch.lean','waves/GSTNCohomologyV3.lean']
CHECK='research/experiments/gst_base_coupled_higher_fold_checks.py'
TEX='research/derivations/GST_base_coupled_and_higher_transgression_folds_2026_11_03.tex'
LEXER='research/experiments/openai_gst_upgrade_checks.py'
OUT='research/computations/gst_base_coupled_higher_fold_20261103.output.json'
MANIFEST='research/computations/gst_base_coupled_higher_fold_20261103.manifest.json'
INPUTS=[CHECK,TEX,LEXER,str(Path(__file__).resolve().relative_to(ROOT))]+LEAN
def digest(p):return sha256((ROOT/p).read_bytes()).hexdigest()
def main():
    started=datetime.now(timezone.utc).isoformat();clock=time.perf_counter()
    before={p:digest(p) for p in INPUTS}
    cp=subprocess.run([sys.executable,CHECK],cwd=ROOT,capture_output=True,text=True,timeout=30)
    if cp.returncode:raise RuntimeError(cp.stderr or cp.stdout)
    checked=json.loads(cp.stdout);assert checked['all_passed']
    spec=importlib.util.spec_from_file_location('gst_coupled_lexer',ROOT/LEXER)
    lexer=importlib.util.module_from_spec(spec);spec.loader.exec_module(lexer)
    graph={};anomalies=[];new_theorems={}
    for p in sorted(ROOT.rglob('*.lean')):
        if '.git' in p.parts:continue
        name=str(p.relative_to(ROOT))
        try:code=lexer.strip_lean(p.read_text())
        except AssertionError as e:
            assert name not in LEAN
            assert subprocess.check_output(['git','show',BASE+':'+name],cwd=ROOT)==p.read_bytes()
            anomalies.append({'path':name,'error':str(e),'base_unchanged':True});continue
        graph[name[:-5].replace('/','.')]=re.findall(r'^import\s+(\S+)',code,re.M)
        if name in LEAN:
            assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',code)
            old=lexer.strip_lean(subprocess.check_output(['git','show',BASE+':'+name],cwd=ROOT,text=True))
            names=lambda s:set(re.findall(r'\btheorem\s+([A-Za-z0-9_.]+)',s))
            new_theorems[name]=sorted(names(code)-names(old))
    visiting=set();visited=set()
    def visit(n):
        if n in visited:return
        assert n not in visiting,('import cycle',n)
        visiting.add(n)
        for dep in graph.get(n,[]):
            if dep in graph:visit(dep)
        visiting.remove(n);visited.add(n)
    for n in graph:visit(n)
    stack=[]
    for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',(ROOT/TEX).read_text()):
        if op=='begin':stack.append(name)
        else:assert stack and stack.pop()==name
    assert not stack
    static={'parsed_import_nodes':len(graph),'import_acyclic':True,
            'new_theorems':new_theorems,'theorem_count':sum(map(len,new_theorems.values())),
            'unchanged_lexical_anomalies':anomalies,'tex_environments_balanced':True,
            'scope':'Lexical/import checks, not a Lean build or whole-repository proof audit'}
    result={'status':'completed','exact_checks':checked,'static':static}
    (ROOT/OUT).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    after={p:digest(p) for p in INPUTS};assert before==after
    manifest={'schema_version':2,'claim_id':'GST-BASE-COUPLED-HIGHER-TRANSGRESSION-20261103',
      'repository':{'commit':BASE,'dirty':True},'command':[sys.executable,CHECK],
      'environment':{'software':[{'name':'Python','version':platform.python_version()}],
                     'hardware':platform.machine()},
      'mathematics':{'assertion_tested':'Two complete boundary constructions and exact elimination algorithms; full one-handle cup-rank formula; mixed-degree cup-coefficient chain isomorphisms; restoring relation factorization; primitive versus nonprimitive integral kernels; noncommutative packet identities with hostile controls.',
          'coefficient_domain':'Z, Q; actual and model Hodge filtrations separately derived by hand',
          'conventions':'Base cohomology of declared products of projective spaces. Odd generators u_i,v_i have degree 2p_i-1, du_i=alpha_i, dv_i=0; all exterior signs and absolute degrees retained.',
          'inputs':INPUTS,'bounds':checked['bounds'],
          'non_claims':['Finite fixtures do not establish the arbitrary-X theorem',
                        'No Lean compilation or CI dispatch',
                        'Higher rational spaces are not asserted compact complex varieties',
                        'No universal Chow-source construction or historical-priority claim']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':time.perf_counter()-clock,'exit_status':cp.returncode,
             'status':'completed','resource_limits':{'memory_bytes':None,'cpu_seconds':None,
              'max_cores':None,'max_threads':None}},
      'outputs':[{'path':OUT,'sha256':digest(OUT),'kind':'result'}],
      'checks':['Bit-mask versus signed-word exterior boundary on every fixture',
                'Sparse column elimination versus dense rational row reduction',
                'Full spectra versus independent cup kernel/cokernel formula',
                'Every mixed-degree basis vector tested against the chain substitution',
                'All small quotient matrices and exact integer-lattice hostile control',
                'Changed Lean proof-escape scan, acyclic import graph, LaTeX environment balance'],
      'result':'implementation and finite assertion verified in the stated range',
      'residual_risks':['Geometric/topological proof is author self-review',
                        'Lean drafts remain uncompiled',
                        'No independent external engine or global literature comparison in this run'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[OUT]}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':cp.returncode,
       'exact_checks':checked['assertion_count'],'full_spectra':len(checked['spectral_rows']),
       'mixed_degree_shears':len(checked['mixed_cup_shears']),
       'theorem_drafts':static['theorem_count'],'parsed_import_nodes':len(graph)}))
if __name__=='__main__':main()
