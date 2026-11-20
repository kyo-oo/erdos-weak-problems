#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
engine107f5v3.py — W77-107K — THE COMPLETION WAVE — THEOREM F5: f(5) = 9.

The v3 layer on top of the banked v2 engine (engine107f5v2.py, which loads
engine107f5.py): CHUNKED + CHECKPOINTED stages.  The sandbox reaps background
processes and the W76 machine died twice mid-run — v3 runs every stage
IN-PROCESS in bounded chunks, checkpoints to disk after every chunk, and
resumes from the progress file.  Mathematics identical to v2 (S1 cells +
S2 wall sweep + S3 in-cell walk per parent); only the execution discipline
changed.  Anchors (classical counts, the completeness certificate):
n = 3..9 mirror-identified: 1, 2, 3, 16, 135, 3315, 158817.

Stages (all append receipts to receipts107f5_v2.txt):
  --stage chunkot8 --n N     process the next N unprocessed n=7 parents with
                             the FULL v2 machinery (S1+S2+S3), checkpoint
                             after every absorb batch; when all 242 done:
                             final certification vs anchor 3315 and write
                             engine107f5_cache/ot8_v2.pkl.
  --stage chunkouter --n N   the INDEPENDENT outer-insertion cross-check
                             (hull-vertex-deletion direction), chunked;
                             outer-only type set must equal the full set.
  --stage hull8               classify every n=8 type by hull size (chirotope
                             method + coordinate cross-check) -> the stage-2
                             parent strata ot8_hull.json.
  --stage status              progress dump.

All arithmetic exact (int / Fraction).  Zero floats.
"""

import sys, os, json, pickle, time, argparse, random
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
CACHE = os.path.join(HERE, "engine107f5_cache")
os.makedirs(CACHE, exist_ok=True)
RECEIPTS = os.path.join(HERE, "receipts107f5_v2.txt")

import engine107f5v2 as V2
# v2 already imported v1 and exposes: orient, sgn, is_gp, chi_of_points,
# TRIPLES, rule_for, osign, canonical_key, shear_distinct_x,
# arrangement_cell_samples, hull_monotone, two_method_agree,
# chi_hull_vertices, chi_convex5_method_a, chi_convex5_method_b,
# chi_witness_is_convex_both

OT_ANCHOR = {3: 1, 4: 2, 5: 3, 6: 16, 7: 135, 8: 3315, 9: 158817}

def R(line=""):
    print(line, flush=True)
    with open(RECEIPTS, "a") as f:
        f.write(line + "\n")

def now():
    return time.strftime("%H:%M:%S")

# ---------------------------------------------------------------------------
# STAGE 1 — chunked n=8 enumeration (v2 machinery, checkpointed)
# ---------------------------------------------------------------------------

PROG8 = os.path.join(CACHE, "ot8_v3_progress.json")
PART8 = os.path.join(CACHE, "ot8_v3_partial.pkl")

def _parents7():
    types7 = pickle.load(open(os.path.join(CACHE, "ot7_v2.pkl"), 'rb'))
    return sorted(types7.items(), key=lambda kv: kv[0])   # deterministic order

def _parent_job_v3(arg):
    """v2's _parent_job_v2 + canonicalization in-worker (parallel) +
    exact-rational child coords.  Returns (key, {ck: (chi, pts)} | None, st)."""
    key, rec, seed = arg
    opts = {'sweep': True, 'walk': True, 'walk_steps': 6}
    k, out, st = V2._parent_job_v2((key, rec, seed, opts))
    if out is None:
        return key, None, st
    rule8 = V2.rule_for(8)
    can = {}
    for chi9, coords in out.items():
        ck = V2.canonical_key(chi9, 8, rule8)
        if ck not in can:
            can[ck] = (chi9, [tuple(p) for p in coords])
    return key, can, st

def stage_chunkot8(n_chunk, wall_guard=470.0):
    t0 = time.time()
    parents = _parents7()
    done = set()
    results = {}
    stats_agg = {}
    if os.path.exists(PROG8):
        prog = json.load(open(PROG8))
        done = set(prog['done'])
        stats_agg = prog.get('stats', {})
    if os.path.exists(PART8):
        results = pickle.load(open(PART8))
    todo = [(i, k, v) for i, (k, v) in enumerate(parents) if i not in done]
    R(f"[chunkot8 {now()}] resume: {len(done)}/{len(parents)} parents done, "
      f"types so far {len(results)}, this chunk: {min(n_chunk, len(todo))}")
    if not todo:
        return _finish_ot8(results, stats_agg)
    from multiprocessing import Pool, cpu_count
    items = [(k, v, 700000 + 7 * 131 + i) for i, k, v in todo[:n_chunk]]
    absorbed = 0
    if len(items) >= 2:
        with Pool(min(2, cpu_count())) as pool:
            for key, can, st in pool.imap_unordered(_parent_job_v3, items, chunksize=1):
                if can is None:
                    R(f"[chunkot8] !! GENERIC-FAIL parent {str(key)[:40]}")
                    continue
                for ck, (chi9, coords) in can.items():
                    if ck not in results:
                        results[ck] = {'chi': chi9, 'pts': coords}
                idx = [i for i, k, v in todo if k == key][0]
                done.add(idx)
                absorbed += 1
                for kk, vv in st.items():
                    stats_agg[kk] = stats_agg.get(kk, 0) + vv
                if absorbed % 8 == 0:
                    _save8(results, done, stats_agg)
                if time.time() - t0 > wall_guard:
                    R(f"[chunkot8 {now()}] wall guard hit — checkpointing")
                    break
    else:
        for it in items:
            key, can, st = _parent_job_v3(it)
            if can is None:
                continue
            for ck, (chi9, coords) in can.items():
                if ck not in results:
                    results[ck] = {'chi': chi9, 'pts': coords}
            done.add([i for i, k, v in todo if k == key][0])
            absorbed += 1
    _save8(results, done, stats_agg)
    R(f"[chunkot8 {now()}] chunk done: +{absorbed} parents "
      f"({len(done)}/{len(parents)}), types {len(results)} "
      f"({time.time()-t0:.0f}s)")
    if len(done) >= len(parents):
        return _finish_ot8(results, stats_agg)
    return None

def _save8(results, done, stats):
    with open(PART8, 'wb') as f:
        pickle.dump(results, f, protocol=4)
    with open(PROG8, 'w') as f:
        json.dump({'done': sorted(done), 'stats': stats}, f)

def _finish_ot8(results, stats_agg):
    cert = V2.certify_level(results, 8)
    R(f"[chunkot8 {now()}] FINAL n=8: {cert['N']} reflection-distinguished, "
      f"self-mirror {cert['self_mirror']}, mirror-identified "
      f"{cert['identified']} (anchor {cert['anchor']}) "
      f"closure={cert['closure_ok']} "
      f"[{'OK — CERTIFIED' if cert['ok'] else 'MISMATCH'}]")
    if cert['ok']:
        with open(os.path.join(CACHE, "ot8_v2.pkl"), 'wb') as f:
            pickle.dump(results, f, protocol=4)
        R(f"[chunkot8 {now()}] wrote engine107f5_cache/ot8_v2.pkl "
          f"({len(results)} types with exact realizations) | totals: "
          + " ".join(f"{k}={v}" for k, v in sorted(stats_agg.items())))
        return results
    # not certified: dump orphans for the escalation lane
    rule8 = V2.rule_for(8)
    orphans = [ck for ck in results
               if V2.canonical_key(tuple(-s for s in ck), 8, rule8) not in results]
    with open(os.path.join(CACHE, "ot8_v3_orphans.pkl"), 'wb') as f:
        pickle.dump(orphans, f, protocol=4)
    R(f"[chunkot8 {now()}] !! {len(orphans)} orphans dumped "
      f"(ot8_v3_orphans.pkl) — escalation lane required")
    return None

# ---------------------------------------------------------------------------
# STAGE 1b — chunked OUTER cross-check (independent method: outer insertions)
# ---------------------------------------------------------------------------

PROGO = os.path.join(CACHE, "outer8_progress.json")
PARTO = os.path.join(CACHE, "outer8_partial.pkl")

def _outer_job_v3(arg):
    key, rec, seed = arg
    rng = random.Random(seed)
    n = len(rec['pts'])
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    posmap = {t: q for q, t in enumerate(V2.TRIPLES(n))}
    chi = rec['chi']
    pts = V2.shear_distinct_x(rec['pts'])
    pts, _ok = V2.make_arrangement_generic(pts, chi, rng)
    if pts is None:
        return key, None
    sh, cells = V2.arrangement_cell_samples(pts)
    current_svs = set()
    out = {}
    for (sx, sy) in cells:
        conf = sh + [(sx, sy)]
        if len(V2.hull_monotone(conf)) <= n:   # sample not a hull vertex
            continue
        sv = V2.sv_of_point(sh, (sx, sy), pairs)
        current_svs.add(sv)
        chi9 = V2.chi_insert(chi, n, sv, pairs, posmap)
        if chi9 not in out:
            out[chi9] = [tuple(p) for p in sh] + [(sx, sy)]
    grabs, _st = V2.sweep_parent(sh, chi, current_svs, rng)
    for chi9, coords in grabs.items():
        if len(V2.hull_monotone(coords)) <= n:
            continue
        if chi9 not in out:
            out[chi9] = coords
    wgrabs, _nw = V2.walk_parent(sh, chi, rng, steps=6, want_new_vs=current_svs)
    for chi9, coords in wgrabs.items():
        if len(V2.hull_monotone(coords)) <= n:
            continue
        if chi9 not in out:
            out[chi9] = coords
    rule8 = V2.rule_for(8)
    can = {}
    for chi9, coords in out.items():
        ck = V2.canonical_key(chi9, 8, rule8)
        if ck not in can:
            can[ck] = (chi9, coords)
    return key, can

def stage_chunkouter(n_chunk, wall_guard=470.0):
    t0 = time.time()
    parents = _parents7()
    done = set()
    results = {}
    if os.path.exists(PROGO):
        done = set(json.load(open(PROGO))['done'])
    if os.path.exists(PARTO):
        results = pickle.load(open(PARTO))
    todo = [(i, k, v) for i, (k, v) in enumerate(parents) if i not in done]
    R(f"[chunkouter {now()}] resume: {len(done)}/{len(parents)} parents, "
      f"outer types so far {len(results)}, chunk {min(n_chunk, len(todo))}")
    if not todo:
        return _finish_outer(results)
    from multiprocessing import Pool, cpu_count
    items = [(k, v, 830000 + i) for i, k, v in todo[:n_chunk]]
    absorbed = 0
    with Pool(min(2, cpu_count())) as pool:
        for key, can in pool.imap_unordered(_outer_job_v3, items, chunksize=1):
            if can is None:
                continue
            for ck, (chi9, coords) in can.items():
                if ck not in results:
                    results[ck] = {'chi': chi9, 'pts': coords}
            done.add([i for i, k, v in todo if k == key][0])
            absorbed += 1
            if absorbed % 8 == 0:
                _saveo(results, done)
            if time.time() - t0 > wall_guard:
                R(f"[chunkouter {now()}] wall guard — checkpointing")
                break
    _saveo(results, done)
    R(f"[chunkouter {now()}] chunk done: +{absorbed} ({len(done)}/{len(parents)}), "
      f"outer types {len(results)} ({time.time()-t0:.0f}s)")
    if len(done) >= len(parents):
        return _finish_outer(results)
    return None

def _saveo(results, done):
    with open(PARTO, 'wb') as f:
        pickle.dump(results, f, protocol=4)
    with open(PROGO, 'w') as f:
        json.dump({'done': sorted(done)}, f)

def _finish_outer(results):
    cert = V2.certify_level(results, 8)
    R(f"[chunkouter {now()}] FINAL outer-only n=8: {cert['N']} "
      f"reflection-distinguished, identified {cert['identified']} "
      f"(anchor {cert['anchor']}) closure={cert['closure_ok']}")
    ref = pickle.load(open(os.path.join(CACHE, "ot8_v2.pkl"), 'rb'))
    same = set(results.keys()) == set(ref.keys())
    R(f"[chunkouter {now()}] outer-only set == full set: "
      f"{'YES — CROSS-CHECK GREEN' if same else 'NO'} "
      f"(outer-missing={len(set(ref)-set(results))} "
      f"full-missing={len(set(results)-set(ref))})")
    return same and cert['ok']

# ---------------------------------------------------------------------------
# STAGE 2 prep — hull classification of the certified n=8 types
# ---------------------------------------------------------------------------

def stage_hull8():
    R(f"[hull8 {now()}] hull-size classification of the certified n=8 types")
    types = pickle.load(open(os.path.join(CACHE, "ot8_v2.pkl"), 'rb'))
    rule8 = V2.rule_for(8)
    census = {}
    recs_by_h = {}
    bad_cross = 0
    for ck, rec in types.items():
        chi = rec['chi']
        hv = V2.chi_hull_vertices(chi, 8, rule8)
        h = len(hv)
        # coordinate cross-check (independent code path)
        hv2 = set(V2.hull_monotone(rec['pts']))
        if len(hv2) != h:
            bad_cross += 1
            R(f"[hull8] !! hull disagree {str(ck)[:40]} chi={h} coord={len(hv2)}")
        census[h] = census.get(h, 0) + 1
        recs_by_h.setdefault(h, []).append(ck)
    R("[hull8] n=8 hull census (reflection-distinguished): "
      + ", ".join(f"h={h}:{c}" for h, c in sorted(census.items())))
    tot = sum(census.values())
    le4 = sum(c for h, c in census.items() if h <= 4)
    R(f"[hull8] total {tot} | hull<=4 stratum: {le4} parents for stage 2 | "
      f"cross-check {'GREEN' if bad_cross == 0 else f'RED ({bad_cross})'}")
    with open(os.path.join(CACHE, "ot8_hull.json"), 'w') as f:
        json.dump({'census': {str(h): c for h, c in census.items()},
                   'total': tot, 'le4': le4, 'bad_cross': bad_cross}, f, indent=1)
    return census

# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", required=True,
                    choices=["chunkot8", "chunkouter", "hull8", "status"])
    ap.add_argument("--n", type=int, default=40)
    args = ap.parse_args()
    if args.stage == "chunkot8":
        stage_chunkot8(args.n)
    elif args.stage == "chunkouter":
        stage_chunkouter(args.n)
    elif args.stage == "hull8":
        stage_hull8()
    elif args.stage == "status":
        for f, nm in [(PROG8, 'ot8'), (PROGO, 'outer8')]:
            if os.path.exists(f):
                d = json.load(open(f))
                print(f"{nm}: {len(d['done'])} parents done")
            else:
                print(f"{nm}: no progress file")

if __name__ == "__main__":
    main()
