#!/usr/bin/env python3
"""Reproducible whole-space finite audit; never installs or runs Lean."""
from datetime import datetime,timezone
from hashlib import sha256
from pathlib import Path
import importlib.util
import json,platform,re,subprocess,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
BASE='ef1a452d5a91e5e8c8a740fbda5761faf4cb9e0a'
LEAN=['GSTCausalFoldDefect.lean','GSTGradedWorldAlgebra.lean',
      'GSTGraphV2GeneralSpaceRealization.lean','GSTGraphV2UnboundedHigherCausality.lean',
      'GSTSpatialFoldResearch.lean','waves/GSTNCohomologyV3.lean']
CHECK='research/experiments/gst_central_fold_checks.py'
WL='research/experiments/gst_central_fold_wolfram_20261103.wl'
RAW='research/computations/gst_central_fold_wolfram_20261103.output.json'
TEX='research/derivations/GST_whole_space_central_causal_fold_2026_11_03.tex'
LEXER='research/experiments/openai_gst_upgrade_checks.py'
OUT='research/computations/gst_central_fold_20261103.independent.output.json'
MANIFEST='research/computations/gst_central_fold_20261103.manifest.json'
INPUTS=[CHECK,WL,RAW,TEX,LEXER,str(Path(__file__).resolve().relative_to(ROOT))]+LEAN
def digest(p):return sha256((ROOT/p).read_bytes()).hexdigest()
def main():
    started=datetime.now(timezone.utc).isoformat();clock=time.perf_counter()
    before={p:digest(p) for p in INPUTS}
    cp=subprocess.run([sys.executable,CHECK],cwd=ROOT,capture_output=True,text=True,timeout=30)
    if cp.returncode:raise RuntimeError(cp.stderr or cp.stdout)
    independent=json.loads(cp.stdout)
    evidence=json.loads((ROOT/RAW).read_text())
    raw='\n'.join(c['text'] for c in evidence['raw_tool_result']['content'] if c['type']=='text')
    remote=json.loads(json.loads(raw[raw.index('"'):]))
    assert remote==evidence['parsed_result']
    assert evidence['source_sha256']==digest(WL)
    assert independent['all_passed'] and remote['all_passed']
    for key in ['spectral_rows','matrix_rank_histogram_2x2']:assert independent[key]==remote[key],key
    spec=importlib.util.spec_from_file_location('gst_central_lexer',ROOT/LEXER)
    lexer=importlib.util.module_from_spec(spec);spec.loader.exec_module(lexer)
    graph={};anomalies=[];new_theorems={}
    for p in sorted(ROOT.rglob('*.lean')):
        if '.git' in p.parts:continue
        name=str(p.relative_to(ROOT))
        try:code=lexer.strip_lean(p.read_text())
        except AssertionError as e:
            assert name not in LEAN
            old=subprocess.check_output(['git','show',BASE+':'+name],cwd=ROOT)
            assert old==p.read_bytes()
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
    result={'status':'completed','independent':independent,'remote_assertions':remote['assertion_count'],
            'all_shared_tables_match':True,'static':static}
    (ROOT/OUT).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    after={p:digest(p) for p in INPUTS};assert before==after
    manifest={'schema_version':2,'claim_id':'GST-WHOLE-SPACE-CENTRAL-CAUSAL-FOLD-20261103',
      'repository':{'commit':BASE,'dirty':True},'command':[sys.executable,CHECK],
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
                   {'name':'Wolfram Language remote kernel','version':remote['kernel_version']}],
                   'hardware':platform.machine()+'; remote hardware not exposed'},
      'mathematics':{'assertion_tested':'Full exterior differential, d squared zero, exact cohomology ranks and Betti polynomials for 22 declared fixtures; all 81 small 2x2 curvature matrices and 64 declared point triples each; whole first-filtration defect and fusion cancellation.',
          'coefficient_domain':'Z, Q; complex filtration proven in the hand derivation',
          'conventions':'Generators Xj,Yj,Ua,Va in that order; dUa=-sum K_aj Xj wedge Yj. Full graded Leibniz signs retained. Opposedness defect is b1-2 dim F1.',
          'inputs':INPUTS,'bounds':independent['bounds'],
          'non_claims':['No Lean compilation','No classification of every GST realization',
                        'No unconditional Hodge-conjecture proof','No global historical novelty claim']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':time.perf_counter()-clock,'exit_status':cp.returncode,
             'status':'completed','resource_limits':{'memory_bytes':None,'cpu_seconds':None,
              'max_cores':None,'max_threads':None}},
      'outputs':[{'path':OUT,'sha256':digest(OUT),'kind':'result'}],
      'checks':['Independent bit-mask and signed-list exterior differentials',
                'Exact sparse Fraction elimination versus Wolfram MatrixRank',
                'All shared full spectra and rank histogram match reparsed remote output',
                'Changed Lean proof-escape scan and parsed import acyclicity','LaTeX environment balance'],
      'result':'implementation and finite assertion verified in the stated range',
      'residual_risks':['Geometric argument is self-reviewed','Lean drafts remain uncompiled',
                        'Remote kernel exit status and runtime not exposed',
                        'First remote evaluation returned internal error; preserved separately'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[OUT],
      'remote_evaluation':{'input_sha256_before':evidence['source_sha256'],'input_sha256_after':digest(WL),
                           'kernel_process_exit_status':None,'kernel_runtime_seconds':None,
                           'assertion_count':remote['assertion_count']}}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':cp.returncode,
       'python_checks':independent['assertion_count'],'wolfram_assertions':remote['assertion_count'],
       'full_spectra_matched':len(remote['spectral_rows']),'theorem_drafts':static['theorem_count'],
       'parsed_import_nodes':len(graph),'all_shared_tables_match':True}))
if __name__=='__main__':main()
