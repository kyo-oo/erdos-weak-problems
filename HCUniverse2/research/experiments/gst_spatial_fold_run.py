#!/usr/bin/env python3
"""Reproduce exact checks, compare all remote tables, write v2 evidence.
Run: python research/experiments/gst_spatial_fold_run.py
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[2]
SCRIPT='research/experiments/gst_spatial_fold_checks.py'
WL='research/experiments/gst_spatial_fold_wolfram_20261102.wl'
REMOTE='research/computations/gst_spatial_fold_wolfram_20261102.output.json'
RESULT='research/computations/gst_spatial_fold_20261102.independent.output.json'
MANIFEST='research/computations/gst_spatial_fold_20261102.manifest.json'
LEAN=['GSTFoldRotation.lean','GSTFoldPolarization.lean','GSTCausalFoldDefect.lean',
      'GSTVariableFoldIntegrability.lean','GSTGraphV2GeneralSpaceRealization.lean','GSTSpatialFoldResearch.lean',
      'GSTLawStackRound51.lean']
INPUTS=[SCRIPT,str(Path(__file__).relative_to(ROOT)),WL,REMOTE,*LEAN,'lakefile.toml',
        'research/experiments/openai_gst_upgrade_checks.py',
        'research/derivations/GST_fold_polarization_integrability_and_causal_defect_2026_11_02.tex']
digest=lambda p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest()

if __name__=='__main__':
    before={p:digest(p) for p in INPUTS}
    started=datetime.now(timezone.utc).isoformat();start=time.perf_counter()
    command=[sys.executable,SCRIPT]
    run=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    elapsed=time.perf_counter()-start
    if run.returncode:
        sys.stderr.buffer.write(run.stderr);raise SystemExit(run.returncode)
    out=json.loads(run.stdout)
    remote=json.loads((ROOT/REMOTE).read_text())
    if remote['input_sha256_before']!=before[WL]:raise RuntimeError('remote source stale')
    text='\n'.join(b['text'] for b in remote['raw_result']['content'] if b['type']=='text')
    raw=json.loads(json.loads(text.split('=',1)[1].strip()))
    if raw!=remote['parsed_result']:raise RuntimeError('remote raw/parsed mismatch')
    if raw['all_passed'] is not True or out['all_passed'] is not True:raise RuntimeError('failed suite')
    for key in ['rotation_rows','exterior_rows','causal_rows','variable_rows']:
        if out[key]!=raw[key]:raise RuntimeError('independent disagreement: '+key)
    out['all_remote_tables_match']=True
    (ROOT/RESULT).write_text(json.dumps(out,indent=2)+'\n')
    after={p:digest(p) for p in INPUTS}
    if before!=after:raise RuntimeError('inputs changed during run')
    manifest={
      'schema_version':2,'claim_id':'GST-SPATIAL-FOLD-POLARIZATION-20261102',
      'repository':{'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
        'dirty':bool(subprocess.check_output(['git','status','--porcelain'],cwd=ROOT))},
      'command':command,
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
        {'name':'Remote Wolfram Language kernel','version':raw['kernel_version']}],
        'hardware':platform.machine()+'; remote hardware not exposed'},
      'mathematics':{
        'assertion_tested':'Exact constant-rotation polarization and integral doors; real-basis exterior charge kernel versus actual divisor products; independently constructed complex balanced basis; heterogeneous causal telescoping; first-jet Nijenhuis brackets and positive energies.',
        'coefficient_domain':'Z, Q, Q(i), symbolic smooth functions; no floating mathematical approximations',
        'conventions':'J(x,y)=(-y,x); E=J^T(I+J^TJ), E(x,Jx)>0; Milne Riemann-form sign is opposite. Exterior order dx0,dy0,...; newest causal operator on the left. N_J=[JU,JV]-J[JU,V]-J[U,JV]-[U,V].',
        'inputs':INPUTS,
        'bounds':{'complex_rotation_ranks':[1,2,3,4,5],'conjugates_per_rank':3,
          'integral_targets_per_coordinate':[-4,4],'brute_integer_preimages_per_coordinate':[-8,8],
          'elliptic_power_dimensions':[0,1,2,3,4],'codimensions':'0 through s+1',
          'causal_matrix_sizes':[1,2,3,4],'causal_word_lengths':[0,1,2,3,4,5,6],
          'variable_f':['1/2','1','2','3'],'variable_df':['-2','0','1','5'],
          'energy_vectors':'all 81 vectors in {-1,0,1}^4 for each of 16 jets'},
        'non_claims':['No Lean elaboration or kernel audit','No universal original-X Chow constructor',
          'No global novelty claim','A pure Hodge structure is not a surjective canonical Chow map',
          'Full-source byte and lexical inventory is not semantic review of every proof']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':elapsed,'exit_status':run.returncode,'status':'completed',
        'resource_limits':{'memory_bytes':None,'cpu_seconds':None,'max_cores':None,'max_threads':None}},
      'outputs':[{'path':RESULT,'sha256':digest(RESULT),'kind':'result'}],
      'checks':['Every remote table reparsed from raw output and compared with independent Python output',
        'Exact Sylvester minors; integer brute witness search; exterior charge kernels versus complex balanced bases',
        'Nonintegrable positive square-fold and cancelling unsafe-edge controls',
        'Changed Lean escape scan, explicit root registration, all local parsed imports acyclic'],
      'result':'implementation and finite assertion verified in the stated ranges',
      'residual_risks':['Lean remains uncompiled at owner request','Geometry is hand-level and self-reviewed',
        'No original-X algebraic return from arbitrary auxiliary rotation data is constructed',
        'Remote process exit status is not exposed'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[RESULT],
      'remote_evaluation':{'input_sha256_before':before[WL],'kernel_runtime_seconds':raw['runtime_seconds'],
        'kernel_process_exit_status':None,'assertion_count':raw['assertion_count']}}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':run.returncode,
      'local_checks':out['total_checks'],'wolfram_assertions':raw['assertion_count'],
      'all_tables_match':True,'manifest':MANIFEST}))
