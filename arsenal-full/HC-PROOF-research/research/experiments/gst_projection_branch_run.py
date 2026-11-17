#!/usr/bin/env python3
"""Reproduce local exact checks, compare raw Wolfram rows, write v2 evidence.
Run: python research/experiments/gst_projection_branch_run.py
The remote evaluation is a pinned input; the plugin is not called by Python.
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

ROOT=Path(__file__).resolve().parents[2]
SCRIPT='research/experiments/gst_projection_branch_checks.py'
WL='research/experiments/gst_projection_branch_wolfram_20261028.wl'
REMOTE='research/computations/gst_projection_branch_wolfram_20261028.output.json'
RESULT='research/computations/gst_projection_branch_20261028.independent.output.json'
MANIFEST='research/computations/gst_projection_branch_20261028.manifest.json'
LEAN=['GSTIntegralProjectionCorrection.lean','GSTNilpotentProjectionConjugacy.lean',
      'GSTSpectralBoundaryDefect.lean','GSTTorsionLineConservation.lean',
      'GSTConnectedSpectralHodgeRigidity.lean','GSTSingularBranchExtraction.lean',
      'GSTFilteredK0SourceConservation.lean','GSTOpenAISourceCorrectionUpgrade.lean']
INPUTS=[SCRIPT,str(Path(__file__).relative_to(ROOT)),WL,REMOTE,
        'research/experiments/openai_gst_upgrade_checks.py',*LEAN,'lakefile.toml',
        'research/derivations/GST_integral_projection_and_singular_branch_source_2026_10_28.tex']
digest=lambda p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest()

if __name__=='__main__':
    before={p:digest(p) for p in INPUTS}
    started=datetime.now(timezone.utc).isoformat();start=time.perf_counter()
    command=[sys.executable,SCRIPT]
    run=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    runtime=time.perf_counter()-start
    if run.returncode:
        sys.stderr.buffer.write(run.stderr);raise SystemExit(run.returncode)
    out=json.loads(run.stdout)
    if out.get('all_passed') is not True:raise RuntimeError('missing local success')
    remote=json.loads((ROOT/REMOTE).read_text())
    if remote['input_sha256_before']!=before[WL]:raise RuntimeError('remote input stale')
    raw='\n'.join(block['text'] for block in remote['raw_result']['content'] if block['type']=='text')
    if '"AllPassed" -> True' not in raw:raise RuntimeError('remote run did not pass')
    if int(re.search(r'"AssertionCount" -> (\d+)',raw).group(1))!=remote['assertion_count']:
        raise RuntimeError('remote assertion-count mismatch')
    regex=(r'<\|"Modulus" -> (\d+), "MatrixCount" -> (\d+), "EligibleMatrices" -> (\d+), '
           r'"DefectNilpotenceHistogram" -> <\|([^|]+)\|>, "IdempotentCount" -> (\d+), '
           r'"IdempotentPairCount" -> (\d+), "NilpotentDifferencePairCount" -> (\d+)\|>')
    rows=[]
    for match in re.finditer(regex,raw):
        g=match.groups();hist={k:int(v) for k,v in re.findall(r'(\d+) -> (\d+)',g[3])}
        rows.append({'modulus':int(g[0]),'matrix_count':int(g[1]),'eligible_matrices':int(g[2]),
                     'defect_nilpotence_histogram':hist,'idempotent_count':int(g[4]),
                     'idempotent_pair_count':int(g[5]),'nilpotent_difference_pair_count':int(g[6])})
    if len(rows)!=6 or rows!=out['finite_rows'] or rows!=remote['finite_rows']:
        raise RuntimeError('independent finite populations disagree')
    out['wolfram_all_six_rows_match']=True
    (ROOT/RESULT).write_text(json.dumps(out,indent=2)+'\n')
    after={p:digest(p) for p in INPUTS}
    if before!=after:raise RuntimeError('input changed during run')
    manifest={
      'schema_version':2,'claim_id':'GST-PROJECTION-SINGULAR-BRANCH-20261028',
      'repository':{'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
                    'dirty':bool(subprocess.check_output(['git','status','--porcelain'],cwd=ROOT))},
      'command':command,
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
         {'name':'Remote Wolfram Language kernel (pinned evaluation)','version':remote['kernel_version']}],
         'hardware':platform.machine()+'; remote kernel hardware not exposed'},
      'mathematics':{
        'assertion_tested':'All 11635 two-by-two matrices and 23664 idempotent pairs over the six listed prime-power rings; every nilpotent-defect correction and nilpotent-difference conjugacy; exact free-ring and commutative boundary identities; ramification normal form and three-twist exceptional extraction.',
        'coefficient_domain':'Z, Z/mZ, Q and exact sparse polynomial rings; no floating mathematical arithmetic',
        'conventions':'Matrix product ordered as written; defect a^2-a; all idempotent pairs ordered; A_n self-intersection -2 and adjacent intersection +1; canonical geometric readout is not replaced by the finite rings.',
        'inputs':INPUTS,
        'bounds':{'moduli':[2,3,4,5,8,9],'matrix_size':2,'all_matrices':11635,
          'all_idempotent_pairs':23664,'nilpotent_defect_matrices':6362,
          'nilpotent_difference_pairs':10116,'A_chain_lengths':list(range(1,13)),
          'A_chain_reflected_pairs':78,'square_zero_power_indices':list(range(13)),
          'integral_hostile_two_power_exponents':list(range(2,9))},
        'non_claims':['No Lean elaboration or kernel audit','No universal original-X Chow source',
          'No assertion of global novelty','No whole-scheme geometry inferred from the finite populations',
          'No assertion that mixed independent sources vanish in every ring or on split covers']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':runtime,'exit_status':run.returncode,'status':'completed',
        'resource_limits':{'memory_bytes':None,'cpu_seconds':None,'max_cores':None,'max_threads':None}},
      'outputs':[{'path':RESULT,'sha256':digest(RESULT),'kind':'result'}],
      'checks':['Raw Wolfram rows re-parsed and all six compared to independent local rows',
        'Nilpotence search bound checked against reduction modulo the residue prime',
        'Free associative quotient preserves order and reduces only idempotence',
        'Missing-hypothesis, integral-torsion, mixed-source and split-cover hostile controls',
        'Changed Lean escape scan, module registration and local import acyclicity'],
      'result':'implementation and finite assertion verified in the stated populations',
      'residual_risks':['Lean remains uncompiled','Geometric hand proofs are self-reviewed, not kernel-verified',
        'Alpha-matched singular support is not constructed universally','Remote process exit status is not exposed'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[RESULT],
      'remote_evaluation':{'input_sha256_before':remote['input_sha256_before'],
        'input_sha256_observed_after':after[WL],'kernel_runtime_seconds':remote['kernel_runtime_seconds'],
        'kernel_process_exit_status':remote['kernel_process_exit_status'],
        'assertion_count':remote['assertion_count']}}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':run.returncode,'independent_checks':out['total_checks'],
      'wolfram_assertions':remote['assertion_count'],'finite_rows_match':True,
      'parsed_import_nodes':out['parsed_import_nodes'],'manifest':MANIFEST}))
