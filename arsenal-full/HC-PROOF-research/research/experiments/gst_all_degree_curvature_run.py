#!/usr/bin/env python3
"""Run exact audits and compare the complete retained Wolfram tables.
Run: python research/experiments/gst_all_degree_curvature_run.py
No Lean compilation, CI dispatch or network access.
"""
from datetime import datetime,timezone
from hashlib import sha256
from pathlib import Path
import importlib.util,json,platform,re,subprocess,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
BASE='f96a12fe6c4617555a1495bd14c6ef2b06851c93'
LEAN=['GSTGradedWorldAlgebra.lean','GSTSpatialFoldResearch.lean']
CHECK='research/experiments/gst_all_degree_curvature_checks.py'
TEX='research/derivations/GST_all_degree_curvature_duality_specialization_2026_11_03.tex'
LEXER='research/experiments/openai_gst_upgrade_checks.py'
WL='research/experiments/gst_all_degree_curvature_wolfram_20261103.wl'
RAW='research/computations/gst_all_degree_curvature_wolfram_20261103.output.json'
OUT='research/computations/gst_all_degree_curvature_20261103.output.json'
MANIFEST='research/computations/gst_all_degree_curvature_20261103.manifest.json'
RUNNER=str(Path(__file__).resolve().relative_to(ROOT))
INPUTS=[CHECK,TEX,LEXER,WL,RAW,RUNNER]+LEAN+[
 'research/derivations/GST_nonlinear_relative_fold_classification_2026_11_03.tex']
def digest(p):return sha256((ROOT/p).read_bytes()).hexdigest()
def main():
    started=datetime.now(timezone.utc).isoformat();clock=time.perf_counter()
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    dirty=bool(subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True))
    before={p:digest(p) for p in INPUTS}
    cp=subprocess.run([sys.executable,CHECK],cwd=ROOT,capture_output=True,text=True,timeout=30)
    if cp.returncode:raise RuntimeError(cp.stderr or cp.stdout)
    exact=json.loads(cp.stdout);assert exact['all_passed']
    evidence=json.loads((ROOT/RAW).read_text())
    raw='\n'.join(c['text'] for c in evidence['raw_response']['content'] if c['type']=='text')
    match=re.search(r'Out\[\d+\]=\s*("(?:[^"\\]|\\.)*")',raw,re.S)
    assert match,'No complete evaluator JSON string'
    observed=json.loads(json.loads(match[1]))
    assert observed==evidence['result'] and observed['all_passed'] and observed['failures']==[]
    assert evidence['input_sha256']==digest(WL)
    assert exact['tables']==observed['tables'] and len(exact['tables'])==13
    spec=importlib.util.spec_from_file_location('gst_all_degree_lexer',ROOT/LEXER)
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
    static={'parsed_import_nodes':len(graph),'import_acyclic':True,'new_theorems':new_theorems,
      'theorem_count':sum(map(len,new_theorems.values())),
      'unchanged_lexical_anomalies':anomalies,'tex_environments_balanced':True,
      'scope':'Lexical/import checks, not Lean compilation or repository-wide semantic proof review'}
    assert static['theorem_count']==19
    result={'status':'completed','arithmetic':exact,'static':static,
      'wolfram_comparison':{'assertions':observed['assertions'],'all_13_tables_match':True,
       'raw_roundtrip_verified':True,'kernel_version':observed['kernel_version']}}
    (ROOT/OUT).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    after={p:digest(p) for p in INPUTS};assert before==after
    manifest={'schema_version':2,'claim_id':'GST-ALL-DEGREE-CURVATURE-20261103',
      'repository':{'commit':head,'dirty':dirty},'command':[sys.executable,RUNNER],
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
       {'name':'Wolfram Language','version':observed['kernel_version']}],'hardware':platform.machine()},
      'mathematics':{'assertion_tested':exact['scope'],
       'coefficient_domain':'Q; Python Fraction elimination versus actual Wolfram MatrixRank and NullSpace',
       'conventions':'Even polynomial powers, then ordered odd base generators, then u then v. All degrees absolute; |u|=|v|=2p-1. Trace is the top original-base uv coefficient.',
       'inputs':INPUTS,'bounds':{'fixtures':13,'max_base_dimension':16,'max_cochain_dimension':64,
        'p_values':[1,2],'controls':'zero curvature, nonzero curvature, rational coefficients, odd base, equal handle rank but distinct all-degree profiles',
        'first_jet_dimension_max':128},
       'non_claims':['Finite fixtures do not prove the general Poincare double or geometric cochain comparison',
        'The parameter family is a DGA family, not an asserted projective family',
        'No Lean compilation, CI dispatch, Chow source or universal Hodge proof',
        'No historical novelty or independent referee claim']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':time.perf_counter()-clock,
       'exit_status':cp.returncode,'status':'completed','resource_limits':{
        'memory_bytes':None,'cpu_seconds':None,'max_cores':None,'max_threads':None}},
      'outputs':[{'path':OUT,'sha256':digest(OUT),'kind':'result'}],
      'checks':['Independent full differential matrices, cohomology representatives and Poincare trace ranks in Python and Wolfram',
       'Every basis multiplication Leibniz check in Python, including odd base and uv signs',
       'All 13 shared tables agree with complete reparsed remote raw output',
       'Actual first-jet matrices and first-order prescribed-target readout',
       'Changed Lean proof-escape scan, acyclic parsed import graph and balanced LaTeX environments'],
      'result':'implementation and finite assertion verified in the stated range',
      'residual_risks':['General mathematics has author self-review, not independent review',
       'Lean drafts uncompiled','Remote runtime and process exit status not exposed',
       'Rational model cochains are distinct from algebraic Chow cycles'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[OUT]}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','python_assertions':exact['assertions'],
     'wolfram_assertions':observed['assertions'],'all_13_tables_match':True,
     'theorem_drafts':static['theorem_count'],'parsed_import_nodes':len(graph)}))
if __name__=='__main__':main()
