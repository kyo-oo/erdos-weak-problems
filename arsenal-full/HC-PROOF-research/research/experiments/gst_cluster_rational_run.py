#!/usr/bin/env python3
"""Reproduce exact checks, compare all remote tables, write v2 evidence.
Run: python research/experiments/gst_cluster_rational_run.py
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
SCRIPT='research/experiments/gst_cluster_rational_checks.py'
WL='research/experiments/gst_cluster_rational_wolfram_20261103.wl'
REMOTE='research/computations/gst_cluster_rational_wolfram_20261103.output.json'
RESULT='research/computations/gst_cluster_rational_20261103.independent.output.json'
MANIFEST='research/computations/gst_cluster_rational_20261103.manifest.json'
LEAN=['GSTCausalFoldDefect.lean','GSTLawStackRound51.lean',
      'GSTSpectralBoundaryDefect.lean','GSTSpatialFoldResearch.lean']
INPUTS=[SCRIPT,str(Path(__file__).relative_to(ROOT)),WL,REMOTE,*LEAN,
        'research/experiments/seed_orbit_break_hunt_round51_checks.py',
        'research/experiments/openai_gst_upgrade_checks.py',
        'research/derivations/GST_selected_cluster_transfer_and_rational_fiber_2026_11_03.tex',
        'research/derivations/GST_seed_orbit_break_hunt_round51_2026_11_09.tex']
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
    for key in ['selector_rows','orientation_normal_form','hilbert_rows','rational_rows','grassmann_rows']:
        if out[key]!=raw[key]:raise RuntimeError('independent disagreement: '+key)
    out['all_remote_tables_match']=True
    (ROOT/RESULT).write_text(json.dumps(out,indent=2)+'\n')
    after={p:digest(p) for p in INPUTS}
    if before!=after:raise RuntimeError('inputs changed during run')
    manifest={
      'schema_version':2,'claim_id':'GST-SELECTED-CLUSTER-RATIONAL-FIBER-20261103',
      'repository':{'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT).decode().strip(),
        'dirty':bool(subprocess.check_output(['git','status','--porcelain'],cwd=ROOT))},
      'command':command,
      'environment':{'software':[{'name':'Python','version':platform.python_version()},
        {'name':'Remote Wolfram Language kernel','version':raw['kernel_version']}],
        'hardware':platform.machine()+'; remote hardware not exposed'},
      'mathematics':{
        'assertion_tested':'Every two-block Chern monomial through weighted degree four has zero full-selector trace modulo elementary symmetric relations for n=2..5; exact Grassmann tangent top-Chern integration degrees; exact S/A/C invariant coinvariant Hilbert tables for n=2..7; rank-three oriented cubic control; rational saturation versus integral index; finite two-ruling source reconstruction; corrected Round51 rational-span controls.',
        'coefficient_domain':'Z, Q and universal sparse polynomial rings; no floating mathematical approximations',
        'conventions':'Roots x_i are c1 of spectral eigenlines, not K0 units. Delta=product_(i<j)(x_i-x_j). Lex x0>...; monic triangular coinvariant basis h_(i+1)(x_i,...,x_(n-1)). All source membership for rational HC is Q-span, not Z-lattice.',
        'inputs':INPUTS,
        'bounds':{'selector_ranks':[2,3,4,5],'cluster_sizes':'every r=0..n',
          'Chern_monomials':'every monomial of weighted degree 1..4 in Chern classes of rank r and rank n-r complementary bundles',
          'grassmann_ranks':[2,3,4,5],'grassmann_cluster_sizes':'every r=0..n',
          'group_ranks':[2,3,4,5,6,7],'groups':['S_n','A_n','cyclic n-cycle group'],
          'Hilbert_degrees':'0..n(n-1)/2',
          'rational_targets':'all a/2,b/3 with a,b=-5..5',
          'rational_scales':['-5','-1/3','1/2','2','7/3'],
          'Round51':'the unchanged declared finite bounds, with Q-span and corrected missing-direction controls'},
        'non_claims':['No Lean elaboration or kernel audit','No universal original-X Chow constructor','No claim that formal coinvariant classes have nonzero geometric pullback',
          'No global novelty claim','A pure Hodge structure is not a surjective canonical Chow map',
          'Full-source byte and lexical inventory is not semantic review of every proof']},
      'randomness':{'used':False,'generator':'none','seed':None},
      'run':{'started_at':started,'runtime_seconds':elapsed,'exit_status':run.returncode,'status':'completed',
        'resource_limits':{'memory_bytes':None,'cpu_seconds':None,'max_cores':None,'max_threads':None}},
      'outputs':[{'path':RESULT,'sha256':digest(RESULT),'kind':'result'}],
      'checks':['Every remote table reparsed from raw output and compared with independent Python output',
        'Wolfram SymmetricReduction versus independent sparse-polynomial Groebner division',
        'Conjugacy-class cycle-index sums versus independently enumerated permutations',
        'Integral-index rejection accepted over Q; actual rational missing-direction controls persist under scale',
        'Changed Lean escape scan and all parsed local imports acyclic; corrected Round51 suite exits zero'],
      'result':'implementation and finite assertion verified in the stated ranges',
      'residual_risks':['Lean remains uncompiled at owner request','Geometry is hand-level and self-reviewed',
        'Spectral-selector geometry and Chow transfer are hand proofs; actual schemes are not instantiated in Lean',
        'Remote process exit status is not exposed'],
      'input_artifacts':[{'path':p,'sha256':before[p],'sha256_after':after[p]} for p in INPUTS],
      'execution_artifacts':INPUTS,'declared_results':[RESULT],
      'remote_evaluation':{'input_sha256_before':before[WL],'kernel_runtime_seconds':raw['runtime_seconds'],
        'kernel_process_exit_status':None,'assertion_count':raw['assertion_count']}}
    (ROOT/MANIFEST).write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'status':'completed','exit_status':run.returncode,
      'local_checks':out['total_checks'],'wolfram_assertions':raw['assertion_count'],
      'all_tables_match':True,'manifest':MANIFEST}))
