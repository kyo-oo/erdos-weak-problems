#!/usr/bin/env python3
"""Reproduce the exact finite checks and compare to retained remote evidence."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import platform
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
CHECK = 'research/experiments/gst_selected_block_checks.py'
WL = 'research/experiments/gst_selected_block_wolfram_20261103.wl'
RAW = 'research/computations/gst_selected_block_wolfram_20261103.output.json'
TEX = 'research/derivations/GST_selected_block_excess_and_integrability_2026_11_03.tex'
OUT = 'research/computations/gst_selected_block_20261103.independent.output.json'
MANIFEST = 'research/computations/gst_selected_block_20261103.manifest.json'
INPUTS = [CHECK, WL, RAW, TEX, str(Path(__file__).resolve().relative_to(ROOT))]

def digest(path):
    return sha256((ROOT/path).read_bytes()).hexdigest()

def main():
    started = datetime.now(timezone.utc).isoformat()
    clock = time.perf_counter()
    before = {p:digest(p) for p in INPUTS}
    observed = subprocess.run([sys.executable, CHECK], cwd=ROOT,
                              capture_output=True, text=True, timeout=30)
    if observed.returncode:
        raise RuntimeError(observed.stderr or observed.stdout)
    independent = json.loads(observed.stdout)
    evidence = json.loads((ROOT/RAW).read_text())
    raw_text = '\n'.join(c['text'] for c in evidence['raw_tool_result']['content']
                         if c['type'] == 'text')
    # Parse both serialization layers, rather than trusting the saved summary.
    remote = json.loads(json.loads(raw_text[raw_text.index('"'):]))
    assert remote == evidence['parsed_result']
    assert evidence['source_sha256'] == digest(WL)
    assert independent['all_passed'] and remote['all_passed']
    matched = ['coefficient_rows','branch_rows','commutator']
    for key in matched:
        assert independent[key] == remote[key], key
    stack = []
    for kind, name in re.findall(r'\\(begin|end)\{([^}]+)\}', (ROOT/TEX).read_text()):
        if kind == 'begin':
            stack.append(name)
        else:
            assert stack and stack.pop() == name, (kind, name)
    assert not stack
    result = {'status':'completed','independent':independent,
              'matched_tables':matched,'all_tables_match':True,
              'wolfram_assertion_count':remote['assertion_count'],
              'tex_environments_balanced':True}
    (ROOT/OUT).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    after = {p:digest(p) for p in INPUTS}
    assert before == after
    manifest = {
      'schema_version':2,
      'claim_id':'GST-SELECTED-BLOCK-EXCESS-INTEGRABILITY-20261103',
      'repository':{'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                    'dirty':bool(subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True))},
      'command':[sys.executable,CHECK],
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
                      {'name':'Wolfram Language remote kernel','version':remote['kernel_version']}],
                     'hardware':platform.machine()+'; remote hardware not exposed'},
      'mathematics':{
        'assertion_tested':'Exact block coefficient/occurrence and power-sum identities, finite root-transitive package cancellation, nonzero-projector perturbation characteristic/discriminant, excluded parameter boundaries and traceless noncommuting obstruction.',
        'coefficient_domain':'Z, Q and sparse quotient Q[x,y,z,e,t]/(x^2+yz-1)',
        'conventions':'Monodromy acts on root labels, selector shells count first-block roots. Complete block packages are orbit-shell connected components. eta2 wedge eta1 = -eta1 wedge eta2.',
        'inputs':INPUTS,
        'bounds':independent['bounds'],
        'non_claims':['No universal Hodge proof','No Lean changes or compilation',
                      'Finite checks do not prove scheme-level geometric statements',
                      'No global novelty or independent mathematical reviewer']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':time.perf_counter()-clock,
             'exit_status':observed.returncode,'status':'completed',
             'resource_limits':{'memory_bytes':None,'cpu_seconds':None,
                                'max_cores':None,'max_threads':None}},
      'outputs':[{'path':OUT,'sha256':digest(OUT),'kind':'result'}],
      'checks':['Direct subset enumeration versus Wolfram binomial coefficients',
                'Sparse quotient matrix arithmetic versus PolynomialReduce',
                'All subgroups enumerated for n=1..4 (counts 1,2,6,30)',
                'Remote output reparsed and all three shared tables matched',
                'LaTeX environment balance'],
      'result':'implementation and finite assertion verified in the stated range',
      'residual_risks':['Hand geometric arguments are self-reviewed',
                        'Source constructor remains conditional on the stated selection input',
                        'Remote kernel process exit status and runtime not exposed'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,
      'declared_results':[OUT],
      'remote_evaluation':{'input_sha256_before':evidence['source_sha256'],
                           'input_sha256_after':digest(WL),
                           'started_at':evidence['started_at'],
                           'finished_at':evidence['finished_at'],
                           'kernel_process_exit_status':None,'kernel_runtime_seconds':None,
                           'assertion_count':remote['assertion_count']}}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':observed.returncode,
                      'independent_checks':independent['assertion_count'],
                      'wolfram_assertions':remote['assertion_count'],
                      'coefficient_rows_matched':len(remote['coefficient_rows']),
                      'subgroup_rows':independent['subgroup_rows'],
                      'all_tables_match':True,'tex_environments_balanced':True}))

if __name__ == '__main__':
    main()
