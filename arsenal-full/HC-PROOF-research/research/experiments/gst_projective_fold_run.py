#!/usr/bin/env python3
"""Reproduce projective-fold supporting arithmetic and pin current inputs.
Run: python research/experiments/gst_projective_fold_run.py
No Lean execution, installation, CI dispatch, or public network lookup.
"""
from datetime import datetime,timezone
from hashlib import sha256
from pathlib import Path
import importlib.util,json,platform,re,subprocess,sys,time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
BASE='e699dbec256fc23d4c5615449bf303df45d0076d'
LEAN=['GSTCausalFoldDefect.lean','GSTSpatialFoldResearch.lean']
CHECK='research/experiments/gst_projective_fold_checks.py'
TEX='research/derivations/GST_projective_fold_algebraization_2026_11_03.tex'
LEXER='research/experiments/openai_gst_upgrade_checks.py'
WL='research/experiments/gst_projective_fold_wolfram_20261103.wl'
RAW='research/computations/gst_projective_fold_wolfram_20261103.output.json'
OUT='research/computations/gst_projective_fold_20261103.output.json'
MANIFEST='research/computations/gst_projective_fold_20261103.manifest.json'
INPUTS=[CHECK,TEX,LEXER,WL,RAW,str(Path(__file__).resolve().relative_to(ROOT))]+LEAN

def digest(p):return sha256((ROOT/p).read_bytes()).hexdigest()
def main():
    started=datetime.now(timezone.utc).isoformat();clock=time.perf_counter()
    before={p:digest(p) for p in INPUTS}
    cp=subprocess.run([sys.executable,CHECK],cwd=ROOT,capture_output=True,text=True,timeout=30)
    if cp.returncode:raise RuntimeError(cp.stderr or cp.stdout)
    exact=json.loads(cp.stdout);assert exact['all_passed']
    evidence=json.loads((ROOT/RAW).read_text())
    raw='\n'.join(x['text'] for x in evidence['raw_response']['content'] if x['type']=='text')
    observed=json.loads(json.loads(re.sub(r'^Out\[\d+\]=\s*','',raw)))
    assert observed==evidence['result'] and observed['all_passed'] and observed['failures']==[]
    assert evidence['input_sha256']==digest(WL)
    for k in ['relation_rows','basis_index','lattice_vector_counts','isogeny_kernel_counts','cover_degrees']:
        assert exact[k]==observed[k],k
    assert exact['assertions']==42745 and observed['assertions']==40658
    spec=importlib.util.spec_from_file_location('gst_projective_lexer',ROOT/LEXER)
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
      'scope':'Lexical/import checks, not Lean compilation or a full-repository semantic review'}
    assert static['theorem_count']==10
    result={'status':'completed','arithmetic':exact,'static':static,
      'wolfram_comparison':{'assertions':observed['assertions'],'all_shared_tables_match':True,
      'raw_roundtrip_verified':True,'kernel_version':observed['kernel_version']}}
    (ROOT/OUT).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    after={p:digest(p) for p in INPUTS};assert before==after
    manifest={'schema_version':2,'claim_id':'GST-PROJECTIVE-FOLD-ALGEBRAIZATION-20261103',
      'repository':{'commit':BASE,'dirty':True},'command':[sys.executable,CHECK],
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
        {'name':'Wolfram Language','version':observed['kernel_version']}],'hardware':platform.machine()},
      'mathematics':{'assertion_tested':'Exact torsion-relation saturation and witnesses for 324 homomorphisms Z^2 -> Z + Z/6, an index-six lattice, non-scalar isogeny kernel orders, and finite-cover cycle normalization in the declared range.',
        'coefficient_domain':'Z, Q, Z/6 and Z/d; exact arithmetic',
        'conventions':'Torsion relations retain free and finite coordinates. Python computes finite order by gcd; Wolfram enumerates all annihilators 1..6. Curvature-zero alone is never substituted for torsion.',
        'inputs':INPUTS,'bounds':exact['bounds'],
        'non_claims':['No numerical proof of analytic projectivity or Picard representability',
          'No Lean compilation or CI dispatch','No universal original-X Chow source',
          'No historical novelty claim']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':time.perf_counter()-clock,'exit_status':cp.returncode,
        'status':'completed','resource_limits':{'memory_bytes':None,'cpu_seconds':None,'max_cores':None,'max_threads':None}},
      'outputs':[{'path':OUT,'sha256':digest(OUT),'kind':'result'}],
      'checks':['GCD order computation versus exhaustive annihilator enumeration',
        'All shared relation, lattice, isogeny and cover-degree tables match reparsed Wolfram output',
        'Explicit lattice bases and normalization','Changed Lean proof-escape scan and import acyclicity',
        'LaTeX environment balance'],
      'result':'implementation and finite assertion verified in the stated range',
      'residual_risks':['Analytic torsor geometry is a separate self-reviewed hand proof',
        'Lean drafts remain uncompiled','Remote kernel runtime and process exit status not exposed',
        'No universal source existence follows from these finite group tests'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[OUT]}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','python_assertions':exact['assertions'],
      'wolfram_assertions':observed['assertions'],'all_shared_tables_match':True,
      'theorem_drafts':static['theorem_count'],'parsed_import_nodes':len(graph)}))
if __name__=='__main__':main()
