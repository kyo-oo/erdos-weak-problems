#!/usr/bin/env python3
"""Reproduce exact nonlinear fold evidence and pin current execution inputs.
Command: python research/experiments/gst_nonlinear_relative_run.py
No Lean installation/execution, CI dispatch, or network access.
"""
from datetime import datetime,timezone
from hashlib import sha256
from pathlib import Path
import importlib.util,json,platform,re,subprocess,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
BASE='2e0324f1328409d68c25d85897435187d0a380b0'
LEAN=['GSTGradedWorldAlgebra.lean','GSTSpatialFoldResearch.lean']
CHECK='research/experiments/gst_nonlinear_relative_checks.py'
TEX='research/derivations/GST_nonlinear_relative_fold_classification_2026_11_03.tex'
LEXER='research/experiments/openai_gst_upgrade_checks.py'
WL='research/experiments/gst_nonlinear_relative_wolfram_20261103.wl'
REMOTE='research/computations/gst_nonlinear_relative_wolfram_20261103.output.json'
OUT='research/computations/gst_nonlinear_relative_20261103.output.json'
MANIFEST='research/computations/gst_nonlinear_relative_20261103.manifest.json'
DEPENDENCIES=['research/experiments/gst_minimal_curvature_checks.py',
 'research/experiments/gst_base_coupled_higher_fold_checks.py',
 'research/derivations/GST_minimal_curvature_fold_normal_form_2026_11_03.tex']
INPUTS=[CHECK,TEX,LEXER,WL,REMOTE,str(Path(__file__).resolve().relative_to(ROOT))]+DEPENDENCIES+LEAN
def digest(p):return sha256((ROOT/p).read_bytes()).hexdigest()
def main():
    started=datetime.now(timezone.utc).isoformat();clock=time.perf_counter()
    before={p:digest(p) for p in INPUTS}
    cp=subprocess.run([sys.executable,CHECK],cwd=ROOT,capture_output=True,text=True,timeout=60)
    if cp.returncode:raise RuntimeError(cp.stderr or cp.stdout)
    checked=json.loads(cp.stdout);assert checked['all_passed']
    remote=json.loads((ROOT/REMOTE).read_text())
    raw='\n'.join(b['text'] for b in remote['raw_response']['content'] if b['type']=='text')
    assert raw.startswith('Out['),'final raw response must not contain warning preamble'
    observed=json.loads(json.loads(re.sub(r'^Out\[\d+\]=\s*','',raw)))
    assert observed==remote['result'] and observed['all_passed'] and not observed['failures']
    assert remote['input_sha256']==digest(WL)
    assert observed['assertions']==5*(4+256+3)+3==1318
    assert observed['nonlinear_rows']==[[r['parameter'],r['states'],r['kernel_dimension'],r['W_closed']] for r in checked['nonlinear_rows']]
    assert observed['massey_ranks']==[checked['massey']['indeterminacy_dimension'],checked['massey']['rank_with_representative']]
    spec=importlib.util.spec_from_file_location('gst_lexer',ROOT/LEXER)
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
      'scope':'Lexical/import checks, not Lean compilation or a whole-repository semantic proof audit'}
    assert static['theorem_count']==13
    result={'status':'completed','exact_checks':checked,'static':static,
      'wolfram_comparison':{'all_shared_tables_match':True,'raw_roundtrip_verified':True,
        'assertions':observed['assertions'],'kernel_version':observed['kernel_version']}}
    (ROOT/OUT).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    after={p:digest(p) for p in INPUTS};assert before==after
    manifest={'schema_version':2,'claim_id':'GST-NONLINEAR-RELATIVE-FOLD-CLASSIFICATION-20261103',
      'repository':{'commit':BASE,'dirty':True},'command':[sys.executable,CHECK],
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
          {'name':'Wolfram Language','version':observed['kernel_version']}],'hardware':platform.machine()},
      'mathematics':{'assertion_tested':'Exact base-boundary intersections, nonlinear full chain maps and both inverses, all absolute degrees, one-handle cohomology-ring products and a complete Massey coset in the declared finite fixtures.',
        'coefficient_domain':'Q, exact arithmetic',
        'conventions':'Finite truncated polynomial base; paired odd handles have degrees 2p-1. The nonlinear differential is transported on the whole exterior algebra, including all Leibniz signs. Base marking is fixed.',
        'inputs':INPUTS,'bounds':checked['bounds'],
        'non_claims':['No Lean compilation or CI dispatch','Finite fixtures do not prove the arbitrary-X classification',
          'No universal original-X Chow constructor','No global novelty search or historical-priority claim']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':time.perf_counter()-clock,'exit_status':cp.returncode,
        'status':'completed','resource_limits':{'memory_bytes':None,'cpu_seconds':None,'max_cores':None,'max_threads':None}},
      'outputs':[{'path':OUT,'sha256':digest(OUT),'kind':'result'}],
      'checks':['Sparse image intersections versus independent dense row ranks',
        'All nonlinear basis states, inverse orders, chain equation, differential square and absolute degrees',
        'Complete one-handle ring bases and all products, including annihilator summands',
        'Nonzero Massey coset modulo its full indeterminacy',
        'Independent Wolfram ordered-word/dense-matrix tables match Python bit-mask/sparse tables',
        'Changed Lean proof-escape scan, acyclic import graph, LaTeX environment balance'],
      'result':'implementation and finite assertion verified in the stated range',
      'residual_risks':['Hand classification and geometric comparison have author self-review only',
        'Lean drafts are uncompiled','Wolfram implementation independence is not independent proof review',
        'The derived-fiber proof is not implemented by the finite computation'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[OUT]}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':cp.returncode,'python_assertions':checked['assertions'],
      'wolfram_assertions':observed['assertions'],'all_shared_tables_match':True,
      'theorem_drafts':static['theorem_count'],'parsed_import_nodes':len(graph)}))
if __name__=='__main__':main()
