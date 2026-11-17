#!/usr/bin/env python3
"""Provenance and static audit for minimal-curvature GST folds.

Command: python research/experiments/gst_minimal_curvature_run.py
Does not install/run Lean, invoke CI, or access the network.
"""
from datetime import datetime,timezone
from hashlib import sha256
from pathlib import Path
import importlib.util
import json,platform,re,subprocess,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
BASE='fde04bf40c9482f6818521a04df3700b2edb4210'
LEAN=['GSTGradedWorldAlgebra.lean','GSTSpatialFoldResearch.lean']
CHECK='research/experiments/gst_minimal_curvature_checks.py'
TEX='research/derivations/GST_minimal_curvature_fold_normal_form_2026_11_03.tex'
LEXER='research/experiments/openai_gst_upgrade_checks.py'
OUT='research/computations/gst_minimal_curvature_20261103.output.json'
MANIFEST='research/computations/gst_minimal_curvature_20261103.manifest.json'
WL='research/experiments/gst_minimal_curvature_wolfram_20261103.wl'
REMOTE='research/computations/gst_minimal_curvature_wolfram_20261103.output.json'
DEPENDENCY='research/experiments/gst_base_coupled_higher_fold_checks.py'
INPUTS=[CHECK,TEX,LEXER,WL,REMOTE,DEPENDENCY,str(Path(__file__).resolve().relative_to(ROOT))]+LEAN
def digest(p):return sha256((ROOT/p).read_bytes()).hexdigest()
def main():
    started=datetime.now(timezone.utc).isoformat();clock=time.perf_counter()
    before={p:digest(p) for p in INPUTS}
    cp=subprocess.run([sys.executable,CHECK],cwd=ROOT,capture_output=True,text=True,timeout=30)
    if cp.returncode:raise RuntimeError(cp.stderr or cp.stdout)
    checked=json.loads(cp.stdout);assert checked['all_passed']
    remote=json.loads((ROOT/REMOTE).read_text())
    raw='\n'.join(b['text'] for b in remote['raw_response']['content'] if b['type']=='text')
    result=json.loads(json.loads(re.sub(r'^Out\[\d+\]=\s*','',raw)))
    assert result==remote['result'] and result['all_passed'] and not result['failures']
    assert remote['input_sha256']==digest(WL)
    assert result['assertions']==972+1+27+2187+1+2+2
    assert result['normal_form_cases']==checked['normal_form_cases']==972
    assert result['nilpotent_fixed_point_cases']==checked['nilpotent_fixed_point_cases']==2187
    assert result['histogram']==[checked['same_degree_mu_histogram'].get(str(i),0) for i in range(3)]
    assert result['P3_spectrum']==checked['full_normal_form_rows'][2]['betti']
    assert result['P1P1_spectrum']==checked['full_normal_form_rows'][3]['betti']
    remote_verified={'all_shared_tables_match':True,'assertions':result['assertions'],
       'kernel_version':result['kernel_version'],'raw_roundtrip_verified':True}
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
    result={'status':'completed','exact_checks':checked,'static':static,'wolfram_comparison':remote_verified}
    (ROOT/OUT).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    after={p:digest(p) for p in INPUTS};assert before==after
    manifest={'schema_version':2,'claim_id':'GST-MINIMAL-CURVATURE-NORMAL-FORM-20261103',
      'repository':{'commit':BASE,'dirty':True},'command':[sys.executable,CHECK],
      'environment':{'software':[{'name':'Python','version':platform.python_version()},{'name':'Wolfram Language','version':remote_verified['kernel_version']}],
                     'hardware':platform.machine()},
      'mathematics':{'assertion_tested':'Full finite simultaneous clearing, independent I/mI dimensions, both inverse chain maps, absolute degree, whole cohomology factor, nilpotent fixed points and nonunit syzygy controls; Wolfram checks the declared shared cases and spectra.',
          'coefficient_domain':'Z, Q; actual and model Hodge filtrations separately derived by hand',
          'conventions':'Base cohomology of declared products of projective spaces. Odd generators u_i,v_i have degree 2p_i-1, du_i=alpha_i, dv_i=0; homogeneous even coefficients, all exterior signs and absolute degrees retained.',
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
      'checks':['Bit-mask versus signed-word boundary and two exact rank algorithms',
                'Greedy minimal generators versus full ideal quotient dimensions',
                'Every mixed-degree basis state checked under both inverse chain substitutions',
                'Full cohomology factor and nonunit syzygy hostile controls',
                'Wolfram raw parse roundtrip, all shared populations and both full spectra match',
                'Changed Lean proof-escape scan, acyclic import graph, LaTeX environment balance'],
      'result':'implementation and finite assertion verified in the stated range',
      'residual_risks':['Geometric/topological proof is author self-review',
                        'Lean drafts remain uncompiled',
                        'Wolfram is an independent exact implementation, not independent proof review; no global literature comparison in this run'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[OUT]}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':cp.returncode,
       'exact_checks':checked['assertion_count'],'full_spectra':len(checked['full_normal_form_rows']),
       'wolfram_assertions':remote_verified['assertions'],
       'all_shared_tables_match':True,
       'theorem_drafts':static['theorem_count'],'parsed_import_nodes':len(graph)}))
if __name__=='__main__':main()
