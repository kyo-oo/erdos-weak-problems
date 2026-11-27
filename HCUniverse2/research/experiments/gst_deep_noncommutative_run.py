#!/usr/bin/env python3
"""Reproduce independent checks and preserve a v2 mathematical audit manifest.
The Wolfram evaluation is a pinned input; its source and raw result are checked.
Run: python research/experiments/gst_deep_noncommutative_run.py
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib
import json
import platform
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[2]
RESULT='research/computations/gst_deep_noncommutative_20261028.independent.output.json'
MANIFEST='research/computations/gst_deep_noncommutative_20261028.manifest.json'
SCRIPT='research/experiments/gst_deep_noncommutative_checks.py'
INPUTS=[SCRIPT,str(Path(__file__).relative_to(ROOT)),
  'research/experiments/openai_gst_upgrade_checks.py',
  'research/experiments/gst_deep_noncommutative_wolfram_20261028.wl',
  'research/computations/gst_deep_noncommutative_wolfram_20261028.output.json',
  'GSTOrderedNilpotentDressing.lean','GSTFiniteGroupCocycleAveraging.lean',
  'GSTTargetWordRecovery.lean','GSTClassicalHodgeWordSourceRecovery.lean',
  'GSTFilteredK0SourceConservation.lean','GSTFiniteSourceCorrection.lean',
  'GSTOpenAISourceCorrectionUpgrade.lean','lakefile.toml']
digest=lambda p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
if __name__=='__main__':
    before={p:digest(p) for p in INPUTS}
    started_at=datetime.now(timezone.utc).isoformat(); start=time.perf_counter()
    command=[sys.executable,SCRIPT]
    run=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    runtime=time.perf_counter()-start
    if run.returncode:
        sys.stderr.buffer.write(run.stderr); raise SystemExit(run.returncode)
    output=json.loads(run.stdout)
    (ROOT/RESULT).write_bytes(run.stdout)
    after={p:digest(p) for p in INPUTS}
    if before!=after: raise RuntimeError('execution inputs changed')
    remote=json.loads((ROOT/INPUTS[4]).read_text())
    manifest={
      'schema_version':2,'claim_id':'GST-DEEP-NONCOMMUTATIVE-20261028',
      'repository':{'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
                    'dirty':bool(subprocess.check_output(['git','status','--porcelain'],cwd=ROOT))},
      'command':command,
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
        {'name':'Remote Wolfram Language kernel (pinned prior evaluation)','version':remote['kernel_version']}],
        'hardware':platform.machine()+'; remote kernel hardware not exposed'},
      'mathematics':{
        'assertion_tested':'Independent exact reconstruction of all 67 cocycle-basis vectors across 13 listed finite actions; rational matrix word, ordered inverse, gauge-defect and Fitting checks; raw Wolfram row/hash comparison.',
        'coefficient_domain':'Z and Q; no floating mathematical arithmetic',
        'conventions':'Left group actions; inhomogeneous cocycle c(g,h)+c(gh,k)=g.c(h,k)+c(g,hk); word products act from the rightmost letter first.',
        'inputs':INPUTS,
        'bounds':{'finite_actions':13,'complete_cocycle_basis_vectors':67,
          'cyclic_orders':[1,2,3,4,5,6],'noncommutative_group':'S3',
          'nilpotent_matrix_orders':[1,2,3,4,5,6,7,8,9],'weighted_kernel_grid':'[-2,2]^3'},
        'non_claims':['No universal Hodge source existence','No Lean elaboration or kernel audit',
          'No global novelty claim','No finite assertion is promoted to a universal geometric theorem']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started_at,'runtime_seconds':runtime,'exit_status':run.returncode,
        'status':'completed','resource_limits':{'memory_bytes':None,'cpu_seconds':None,
                                              'max_cores':None,'max_threads':None}},
      'outputs':[{'path':RESULT,'sha256':digest(RESULT),'kind':'result'}],
      'checks':['Independent sparse rational elimination','Every cocycle basis vector tested',
                'Group/action laws and dimension benchmark checked','Wolfram raw rows and source hash matched',
                'Changed Lean escape scan and import acyclicity checked'],
      'result':'implementation and finite assertion verified in the stated ranges',
      'residual_risks':['Lean source remains uncompiled','Geometric source/operator existence is not established',
        'The remote kernel process exit status is not exposed; this manifest records the actual local verifier exit status.'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[RESULT],
      'remote_evaluation':{'input_sha256_before':remote['input_sha256_before'],
        'kernel_runtime_seconds':remote['kernel_runtime_seconds'],
        'kernel_process_exit_status':remote['kernel_process_exit_status'],
        'assertion_count':remote['assertion_count']}}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':run.returncode,
      'independent_checks':output['total_checks'],'wolfram_assertions':remote['assertion_count'],
      'complete_cocycle_basis_vectors':67,'manifest':MANIFEST}))
