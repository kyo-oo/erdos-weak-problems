#!/usr/bin/env python3
"""Run current-source checks and compare retained actual Wolfram evidence.
Run: python research/experiments/gst_divisorial_completion_run.py
No Lean build, CI dispatch or network access.
"""
from datetime import datetime,timezone
from hashlib import sha256
from pathlib import Path
import importlib.util,json,platform,re,subprocess,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
BASE='e40e328b80d3ede78202234054891b1e56edf0b3'
LEAN=['GSTCausalFoldDefect.lean','GSTSpatialFoldResearch.lean']
CHECK='research/experiments/gst_divisorial_completion_checks.py'
TEX='research/derivations/GST_curvature_exact_sequence_divisorial_completion_2026_11_03.tex'
LEXER='research/experiments/openai_gst_upgrade_checks.py'
WL='research/experiments/gst_divisorial_completion_wolfram_20261103.wl'
RAW='research/computations/gst_divisorial_completion_wolfram_20261103.output.json'
OUT='research/computations/gst_divisorial_completion_20261103.output.json'
MANIFEST='research/computations/gst_divisorial_completion_20261103.manifest.json'
INPUTS=[CHECK,TEX,LEXER,WL,RAW,str(Path(__file__).resolve().relative_to(ROOT))]+LEAN+[
 'research/experiments/gst_curvature_return_checks.py',
 'research/derivations/GST_whole_space_central_causal_fold_2026_11_03.tex',
 'research/derivations/GST_curvature_projective_retraction_boundary_2026_11_03.tex',
 'research/records/gst_divisorial_completion_sources_20261103.json']
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
    shared=['sequence_rows','hodge_lift','cleared_source','returned_cycle','ample_rows','quadric_line_return']
    for k in shared:assert exact[k]==observed[k],k
    assert exact['assertions']==observed['assertions']==41
    spec=importlib.util.spec_from_file_location('gst_divisorial_lexer',ROOT/LEXER)
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
    assert static['theorem_count']==10
    result={'status':'completed','arithmetic':exact,'static':static,
      'wolfram_comparison':{'assertions':observed['assertions'],'all_shared_tables_match':True,
       'shared_keys':shared,'raw_roundtrip_verified':True,'kernel_version':observed['kernel_version']}}
    (ROOT/OUT).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    after={p:digest(p) for p in INPUTS};assert before==after
    manifest={'schema_version':2,'claim_id':'GST-DIVISORIAL-COMPLETION-20261103',
      'repository':{'commit':head,'dirty':dirty},'command':[sys.executable,CHECK],
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
       {'name':'Wolfram Language','version':observed['kernel_version']}],'hardware':platform.machine()},
      'mathematics':{'assertion_tested':exact['scope'],
       'coefficient_domain':'Q and exact Gaussian rational splitting; Fraction elimination versus Wolfram exact linear algebra',
       'conventions':'Column vectors. Curvature pure space has both vertical coefficients in ker L. Boundary line denominator N and generic transfer degree d are distinct.',
       'inputs':INPUTS,'bounds':{'curvature_matrices':5,'zero_handle_control':1,
        'hodge_lift_fixture':'one 4 by 7 Gysin-coordinate map, with rational lift outside the designated type subspace',
        'line_denominator':3,'generic_degree':6,'ample_targets':5,
        'quadric_control':'two middle ruling coordinates; geometric return is a hand proof'},
       'non_claims':['No finite computation proves algebraic existence, weight degeneration or GAGA',
        'No Lean compilation or CI dispatch','No universal prescribed-alpha nullifying open',
        'No independent referee or historical novelty claim']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':time.perf_counter()-clock,
       'exit_status':cp.returncode,'status':'completed','resource_limits':{
        'memory_bytes':None,'cpu_seconds':None,'max_cores':None,'max_threads':None}},
      'outputs':[{'path':OUT,'sha256':digest(OUT),'kind':'result'}],
      'checks':['Fraction kernel/rank and rational inverse versus Wolfram NullSpace/MatrixRank/Inverse',
       'All six shared tables agree with complete reparsed remote raw output',
       'Zero/full-rank curvature, non-Hodge raw lift, each omitted-denominator failure, primitive survival controls',
       'Changed Lean proof-escape scan, import graph and LaTeX environment balance'],
      'result':'implementation and finite assertion verified in the stated range',
      'residual_risks':['Geometry remains a self-reviewed hand proof','Lean drafts uncompiled',
       'Provider global-symbol diagnostics retained; all 41 actual assertions passed',
       'Remote runtime and process exit status not exposed','Universal source construction unresolved'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[OUT]}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','python_assertions':exact['assertions'],
     'wolfram_assertions':observed['assertions'],'all_shared_tables_match':True,
     'theorem_drafts':static['theorem_count'],'parsed_import_nodes':len(graph)}))
if __name__=='__main__':main()
