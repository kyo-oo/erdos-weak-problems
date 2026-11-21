#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
engine107f5v4.py — W81-107A — THE C-PORT DRIVER — THEOREM F5: f(5) = 9.

The chunked + checkpointed driver around the C port engine107f9.c
(the faithful C port of the v2 machinery: S1 slab cells + S2 wall sweep +
S3 in-cell walk + C canonical form; exact rationals via GMP mpq).

Stages (receipts -> receipts107f9.txt):
  --stage ladder              VALIDATION LADDER: the C engine re-enumerates
                              n=4..8 from the banked parent caches; SET
                              EQUALITY vs the python bank at EVERY level
                              (the two-code law). Any mismatch -> STOP.
  --stage grind [--chunk N]   THE n=9 RUN: 6405 banked n=8 parents in
                              hull-class order (hull<=4 strata FIRST — the
                              f(5)-critical types), C engine in chunks,
                              python certification layer per chunk (chi
                              re-verified from coords + canonical_key
                              re-verified for every new type), checkpoint
                              (f9_progress.json, sharp107_progress format)
                              after every chunk.
  --stage certify             FINAL: mirror closure + anchor 158817 + hull
                              census + convex-5 two-code (chi A/B on all
                              hull<=4 types; coordinate A/B on a certified
                              sample + the banked witness).
  --stage status              progress dump.

All arithmetic exact (int / Fraction).  Zero floats.
"""

import sys, os, json, pickle, time, argparse, random, subprocess, itertools
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
CACHE = os.path.join(HERE, "engine107f5_cache")
F9DIR = os.path.join(CACHE, "f9")
os.makedirs(F9DIR, exist_ok=True)
RECEIPTS = os.path.join(HERE, "receipts107f9.txt")
ENGINE9 = os.path.join(HERE, "engine107f9")

import engine107f5v2 as V2
orient = V2.orient
sgn = V2.sgn
is_gp = V2.is_gp
chi_of_points = V2.chi_of_points
TRIPLES = V2.TRIPLES
rule_for = V2.rule_for
osign = V2.osign
canonical_key = V2.canonical_key
hull_monotone = V2.hull_monotone
chi_hull_vertices = V2.chi_hull_vertices
chi_convex5_method_a = V2.chi_convex5_method_a
chi_convex5_method_b = V2.chi_convex5_method_b
chi_witness_is_convex_both = V2.chi_witness_is_convex_both
two_method_agree = V2.two_method_agree

OT_ANCHOR = {3: 1, 4: 2, 5: 3, 6: 16, 7: 135, 8: 3315, 9: 158817}

def R(line=""):
    print(line, flush=True)
    with open(RECEIPTS, "a") as f:
        f.write(line + "\n")

def now():
    return time.strftime("%H:%M:%S")

# ---------------------------------------------------------------------------
# shared packing (the C engine's convention: bit i = (sign_i > 0), hex,
# little-endian nibbles, zero-padded)
# ---------------------------------------------------------------------------

def pack_signs(t):
    bits = 0
    for i, s in enumerate(t):
        if s > 0:
            bits |= 1 << i
    return format(bits, "0{}x".format((len(t) + 3) // 4))

def unpack_signs(h, L):
    bits = int(h, 16)
    return tuple(1 if (bits >> i) & 1 else -1 for i in range(L))

def frac_str(f):
    f = Fraction(f)
    return f"{f.numerator}/{f.denominator}"

def parse_frac(s):
    if "/" in s:
        a, b = s.split("/")
        return Fraction(int(a), int(b))
    return Fraction(int(s))

def ntrip(n):
    return len(TRIPLES(n))

# ---------------------------------------------------------------------------
# C engine invocation
# ---------------------------------------------------------------------------

def write_batch(path, parents):
    """parents: list of (key, n, chi tuple, pts list)."""
    with open(path, "w") as f:
        for key, n, chi, pts in parents:
            f.write(f"P {key} {n} {pack_signs(chi)}\n")
            for (x, y) in pts:
                f.write(f"{frac_str(x)} {frac_str(y)}\n")

def run_engine(batch_path, out_path, walk_steps=6, seed=1070707, timeout=100000):
    t0 = time.time()
    with open(out_path, "w") as fo:
        proc = subprocess.run([ENGINE9, "--walk-steps", str(walk_steps),
                               "--seed", str(seed)],
                              stdin=open(batch_path), stdout=fo,
                              stderr=subprocess.PIPE, timeout=timeout)
    if proc.returncode != 0:
        raise RuntimeError(f"engine107f9 failed rc={proc.returncode}: "
                           f"{proc.stderr.decode()[:2000]}")
    return time.time() - t0

def read_engine_output(path, nchild):
    """Returns (children, stats, errors): children = list of
    (ckhex, chihex, [coord strings]) — coords parsed lazily by caller."""
    children = []
    stats = {}
    errors = []
    L = ntrip(nchild)
    with open(path) as f:
        for line in f:
            if line.startswith("T "):
                parts = line.split()
                children.append((parts[1], parts[2], parts[3:]))
            elif line.startswith("#P "):
                parts = line.split()
                idx = int(parts[1])
                st = {}
                for kv in parts[3:]:
                    k, v = kv.split("=", 1)
                    st[k] = v
                stats[idx] = st
            elif line.startswith("#E "):
                errors.append(line.split()[1])
    return children, stats, errors

# ---------------------------------------------------------------------------
# VALIDATION LADDER
# ---------------------------------------------------------------------------

def _load_bank(n):
    return pickle.load(open(os.path.join(CACHE, f"ot{n}_v2.pkl"), "rb"))

def stage_ladder():
    R(f"[ladder {now()}] THE VALIDATION LADDER: C re-enumerates n=4..8; "
      f"SET EQUALITY vs the python bank at every level")
    all_ok = True
    for np_ in range(3, 8):          # parent levels 3..7 -> children 4..8
        n1 = np_ + 1
        bank = _load_bank(np_)
        target = _load_bank(n1)
        target_keys = set(target.keys())
        parents = []
        for ck, rec in bank.items():
            parents.append((pack_signs(ck), np_, rec["chi"], rec["pts"]))
        bpath = os.path.join(F9DIR, f"ladder_p{np_}.txt")
        opath = os.path.join(F9DIR, f"ladder_p{np_}.out")
        write_batch(bpath, parents)
        wall = run_engine(bpath, opath)
        children, stats, errors = read_engine_output(opath, n1)
        # SET EQUALITY on canonical keys (the C canon vs the bank keys)
        got = set()
        bad_selfcheck = 0
        bad_formula = 0
        for (ckh, chih, coords) in children:
            got.add(unpack_signs(ckh, ntrip(n1)))
        for i, st in stats.items():
            if st.get("selfcheck") == "0":
                bad_selfcheck += 1
            if st.get("formula") == "0":
                bad_formula += 1
        miss = target_keys - got
        extra = got - target_keys
        ok = (not miss) and (not extra) and (not errors) and bad_selfcheck == 0 \
             and bad_formula == 0
        # python-side spot certification: re-verify chi + canon on a sample
        rng = random.Random(99000 + np_)
        sample = children if len(children) <= 40 else rng.sample(children, 40)
        spot_bad = 0
        for (ckh, chih, coords) in sample:
            chi = unpack_signs(chih, ntrip(n1))
            ck = unpack_signs(ckh, ntrip(n1))
            pts = [(parse_frac(coords[2 * i]), parse_frac(coords[2 * i + 1]))
                   for i in range(n1)]
            if chi_of_points(pts) != chi:
                spot_bad += 1
                continue
            if canonical_key(chi, n1, rule_for(n1)) != ck:
                spot_bad += 1
        n_cells = sum(int(st.get("cells", 0)) for st in stats.values())
        R(f"[ladder {now()}] n={np_}->{n1}: |bank|={len(target_keys)} "
          f"|C|={len(got)} miss={len(miss)} extra={len(extra)} "
          f"parents={len(parents)} cells={n_cells} "
          f"formula_bad={bad_formula} selfcheck_bad={bad_selfcheck} "
          f"generic_fail={len(errors)} spot(cert)={len(sample)}/{len(sample) if spot_bad==0 else 'BAD'} "
          f"wall={wall:.1f}s -> {'SET EQUALITY OK' if ok and spot_bad == 0 else 'MISMATCH'}")
        if not ok or spot_bad:
            all_ok = False
            for ck in list(miss)[:3]:
                R(f"[ladder]   MISSING sample: {str(ck)[:60]}...")
            for ck in list(extra)[:3]:
                R(f"[ladder]   EXTRA sample: {str(ck)[:60]}...")
            R(f"[ladder] !! STOP — diagnose before n=9")
            return False
    R(f"[ladder {now()}] LADDER GREEN — n=4..8 SET EQUALITY at every level; "
      f"the C port is the python machinery")
    return all_ok

# ---------------------------------------------------------------------------
# THE GRIND (n=9)
# ---------------------------------------------------------------------------

PROG = os.path.join(F9DIR, "f9_progress.json")
CENSUS = os.path.join(F9DIR, "f9_census.jsonl")
CHUNKDIR = os.path.join(F9DIR, "chunks")
os.makedirs(CHUNKDIR, exist_ok=True)

def _parent_list():
    """All 6405 n=8 parents in hull-class order (hull<=4 FIRST — the
    f(5)-critical stratum), then by canonical key for determinism."""
    bank = _load_bank(8)
    rule8 = rule_for(8)
    recs = []
    for ck, rec in bank.items():
        h = len(chi_hull_vertices(rec["chi"], 8, rule8))
        recs.append((0 if h <= 4 else 1, h, ck, rec))
    recs.sort(key=lambda t: (t[0], t[1], t[2]))
    return recs

def _load_progress():
    if os.path.exists(PROG):
        return json.load(open(PROG))
    return {"done": [], "results": [], "stats": {}, "census_lines": 0}

def _save_progress(prog):
    with open(PROG, "w") as f:
        json.dump(prog, f)

def _certify_chunk(children, results_set, prog, verify_all=True, sample_rate=0.05,
                   rngseed=None):
    """The python certification layer for one chunk of C emissions.
    - chi re-verified from coords for every NEW type (and a sample of dups)
    - canonical_key re-verified (python) for every NEW type (and samples)
    Returns (n_new, n_bad, hull_hist_new)."""
    n1 = 9
    L = ntrip(9)
    rule9 = rule_for(9)
    n_new, n_bad = 0, 0
    rng = random.Random(rngseed if rngseed is not None else 1234)
    hull_hist = {}
    out_lines = []
    for (ckh, chih, coords) in children:
        ck = ckh                       # keep hex form for the census
        is_new = ck not in results_set
        do_full = is_new or (rng.random() < sample_rate)
        if not do_full:
            continue
        chi = unpack_signs(chih, L)
        pts = [(parse_frac(coords[2 * i]), parse_frac(coords[2 * i + 1]))
               for i in range(n1)]
        # 1) chi-verified from coords (python code path)
        if chi_of_points(pts) != chi:
            n_bad += 1
            R(f"[grind] !! CHI MISMATCH ck={ckh[:20]} — STOP THE WORLD")
            continue
        # 2) canon-verified (python canonical_key)
        if pack_signs(canonical_key(chi, 9, rule9)) != ckh:
            n_bad += 1
            R(f"[grind] !! CANON MISMATCH ck={ckh[:20]} — STOP THE WORLD")
            continue
        if is_new:
            results_set.add(ck)
            n_new += 1
            # hull census of the new type (chirotope method)
            h = len(chi_hull_vertices(chi, 9, rule9))
            hull_hist[h] = hull_hist.get(h, 0) + 1
            out_lines.append(json.dumps({
                "ck": ckh, "chi": chih,
                "pts": [[frac_str(x), frac_str(y)] for (x, y) in pts],
                "hull": h}))
    if out_lines:
        with open(CENSUS, "a") as f:
            for ln in out_lines:
                f.write(ln + "\n")
        prog["census_lines"] = prog.get("census_lines", 0) + len(out_lines)
    return n_new, n_bad, hull_hist

def _git(args):
    return subprocess.run(["git", "-C", HERE] + args,
                          capture_output=True, text=True)

def stage_grind(chunk=128, walk_steps=6, max_chunks=None, workers=1,
                push_every=4, wall_budget=None):
    t_start = time.time()
    prog = _load_progress()
    done = set(prog["done"])
    parents = _parent_list()
    todo = [(i, r) for i, r in enumerate(parents) if i not in done]
    R(f"[grind {now()}] resume: {len(done)}/{len(parents)} parents done, "
      f"census lines {prog.get('census_lines', 0)}, this run: "
      f"{min(len(todo), chunk * (max_chunks or 10**9))} parents max, "
      f"workers={workers}")
    results_set = _load_census_keys()
    n_chunk_id = len(prog["results"])
    n_chunks_this_run = 0
    le4_total = sum(1 for r in parents if r[0] == 0)
    census_committed = prog.get("census_committed", 0)

    def certify_and_checkpoint(cid, batch, children, stats, errors, wall):
        nonlocal census_committed
        if errors:
            R(f"[grind {now()}] !! chunk {cid}: {len(errors)} "
              f"GENERIC-FAIL parents — STOP (must not happen at n=8)")
            return False
        for i, st in stats.items():
            if st.get("selfcheck") == "0" or st.get("formula") == "0":
                R(f"[grind {now()}] !! chunk {cid}: parent {i} "
                   f"selfcheck/formula FAIL — STOP")
                return False
        n_new, n_bad, hh = _certify_chunk(children, results_set, prog,
                                          rngseed=cid)
        if n_bad:
            R(f"[grind {now()}] !! chunk {cid}: {n_bad} certification "
               f"failures — STOP THE WORLD")
            return False
        agg = prog.setdefault("stats", {})
        for i, st in stats.items():
            for k in ("cells", "conc", "par", "sweep_grabs", "walk", "children"):
                if k in st:
                    v = st[k]
                    if "/" in v:
                        a, b = v.split("/")
                        agg[k + "_crossed"] = agg.get(k + "_crossed", 0) + int(a)
                        agg[k + "_combos"] = agg.get(k + "_combos", 0) + int(b)
                    else:
                        agg[k] = agg.get(k, 0) + int(v)
            agg["parents"] = agg.get("parents", 0) + 1
        for i, r in batch:
            done.add(i)
        prog["done"] = sorted(done)
        le4_done = sum(1 for i in done if parents[i][0] == 0)
        msg = (f"chunk {cid}: +{len(batch)} parents "
               f"({len(done)}/{len(parents)}; hull<=4: {le4_done}/{le4_total}), "
               f"+{n_new} new types (census {len(results_set)}), "
               f"new-hull-hist {dict(sorted(hh.items()))}, "
               f"C-wall {wall:.0f}s, total {time.time()-t_start:.0f}s")
        prog["results"].append([f"C{cid:04d}", True, msg])
        _save_progress(prog)
        R(f"[grind {now()}] {msg}")
        # commit + push checkpoint discipline
        files = [RECEIPTS, PROG]
        milestone = ""
        if le4_done == le4_total and census_committed < 1:
            census_committed = 1
            prog["census_committed"] = census_committed
            _save_progress(prog)
            files.append(CENSUS)
            milestone = " HULL<=4 STRATUM COMPLETE (census banked)"
        _git(["add"] + files)
        _git(["commit", "-q", "-m",
              f"W81-107A grind chunk {cid}: {len(done)}/6405 parents, "
              f"census {len(results_set)} types{milestone}"])
        if (cid + 1) % push_every == 0:
            _git(["push", "-q", "origin", "w81-107a"])
        return True

    if workers <= 1:
        while todo:
            batch = todo[:chunk]
            bpath = os.path.join(CHUNKDIR, f"c{n_chunk_id:04d}.txt")
            opath = os.path.join(F9DIR, "current.out")
            write_batch(bpath, [(pack_signs(r[2]), 8,
                                 r[3]["chi"], r[3]["pts"])
                                for (_, r) in batch])
            wall = run_engine(bpath, opath, walk_steps=walk_steps)
            children, stats, errors = read_engine_output(opath, 9)
            if not certify_and_checkpoint(n_chunk_id, batch, children, stats,
                                          errors, wall):
                return False
            n_chunk_id += 1
            n_chunks_this_run += 1
            todo = todo[chunk:]
            if max_chunks and n_chunks_this_run >= max_chunks:
                break
    else:
        # parallel C workers, certification pipelined in this process
        from collections import deque
        queue = deque()
        for k in range(0, len(todo), chunk):
            if max_chunks and len(queue) >= max_chunks:
                break
            queue.append((n_chunk_id + len(queue), todo[k:k + chunk]))
        running = []
        while queue or running:
            # wall-clock budget: stop LAUNCHING new chunks near the budget
            # (running chunks always complete + certify + checkpoint first)
            if wall_budget is not None:
                elapsed = time.time() - t_start
                if elapsed > wall_budget - 70:
                    if queue:
                        R(f"[grind {now()}] wall budget {wall_budget}s at "
                          f"{elapsed:.0f}s — draining {len(running)} running "
                          f"chunks, deferring {len(queue)}")
                    queue.clear()
            while queue and len(running) < workers:
                cid, batch = queue.popleft()
                bpath = os.path.join(CHUNKDIR, f"c{cid:04d}.txt")
                opath = os.path.join(F9DIR, f"out_c{cid:04d}.txt")
                write_batch(bpath, [(pack_signs(r[2]), 8,
                                     r[3]["chi"], r[3]["pts"])
                                    for (_, r) in batch])
                t0 = time.time()
                proc = subprocess.Popen(
                    [ENGINE9, "--walk-steps", str(walk_steps),
                     "--seed", "1070707"],
                    stdin=open(bpath), stdout=open(opath, "w"),
                    stderr=subprocess.PIPE)
                running.append((cid, batch, proc, opath, t0))
                R(f"[grind {now()}] launched chunk {cid} "
                  f"({len(batch)} parents)")
            # wait for any running chunk to finish
            finished = None
            while finished is None:
                for ent in running:
                    if ent[2].poll() is not None:
                        finished = ent
                        break
                if finished is None:
                    time.sleep(0.5)
            cid, batch, proc, opath, t0 = finished
            running.remove(finished)
            err = proc.stderr.read().decode()
            wall = time.time() - t0
            if proc.returncode != 0:
                R(f"[grind {now()}] !! chunk {cid}: engine rc="
                  f"{proc.returncode}: {err[:500]} — STOP THE WORLD")
                return False
            children, stats, errors = read_engine_output(opath, 9)
            if not certify_and_checkpoint(cid, batch, children, stats,
                                          errors, wall):
                return False
            n_chunks_this_run += 1
    if (n_chunk_id + n_chunks_this_run) % push_every != 0:
        _git(["push", "-q", "origin", "w81-107a"])
    R(f"[grind {now()}] GRIND COMPLETE: {len(done)}/{len(parents)} parents, "
      f"census {len(results_set)} reflection-distinguished types")
    return True

def _load_census_keys():
    keys = set()
    if os.path.exists(CENSUS):
        with open(CENSUS) as f:
            for line in f:
                keys.add(json.loads(line)["ck"])
    return keys

# ---------------------------------------------------------------------------
# FINAL CERTIFICATION
# ---------------------------------------------------------------------------

def stage_certify(sample=400, quick=False):
    R(f"[certify {now()}] THE n=9 CERTIFICATION")
    rule9 = rule_for(9)
    types = {}
    with open(CENSUS) as f:
        for line in f:
            d = json.loads(line)
            types[d["ck"]] = d
    N = len(types)
    R(f"[certify] census: {N} reflection-distinguished types")
    # mirror closure + self-mirror count (python canonical_key)
    sm = 0
    closure_ok = True
    missing_mirror = 0
    t0 = time.time()
    for i, ck in enumerate(types):
        chi = unpack_signs(types[ck]["chi"], ntrip(9))
        negk = pack_signs(canonical_key(tuple(-s for s in chi), 9, rule9))
        if negk not in types:
            closure_ok = False
            missing_mirror += 1
        elif negk == ck:
            sm += 1
        if (i + 1) % 50000 == 0:
            R(f"[certify]   mirror pass {i+1}/{N} ({time.time()-t0:.0f}s)")
    identified = (N + sm) // 2 if closure_ok else None
    R(f"[certify] mirror closure {'OK' if closure_ok else f'FAIL ({missing_mirror})'}; "
      f"self-mirror {sm}; mirror-identified {identified} "
      f"(anchor {OT_ANCHOR[9]}) "
      f"[{'OK' if identified == OT_ANCHOR[9] else 'MISMATCH'}]")
    if identified != OT_ANCHOR[9]:
        R("[certify] !! refusing to certify — count mismatch")
        return False
    # hull census + convex-5
    census = {}
    bad = []
    wcomp = {}
    t0 = time.time()
    items = list(types.items())
    for i, (ck, d) in enumerate(items):
        chi = unpack_signs(d["chi"], ntrip(9))
        hull = chi_hull_vertices(chi, 9, rule9)
        h = len(hull)
        census[h] = census.get(h, 0) + 1
        if h >= 5:
            # hull vertices themselves contain a convex 5; still verify by
            # the two chirotope methods on a sample (quick mode: skip)
            if not quick:
                wa = chi_convex5_method_a(chi, 9, rule9)
                wb = chi_convex5_method_b(chi, 9, rule9)
                if (wa is None) != (wb is None) or wa is None:
                    bad.append((ck, "h>=5-but-no-witness"))
                elif not (chi_witness_is_convex_both(chi, 9, rule9, wa)
                          and chi_witness_is_convex_both(chi, 9, rule9, wb)):
                    bad.append((ck, "h>=5-crossfail"))
        else:
            wa = chi_convex5_method_a(chi, 9, rule9)
            wb = chi_convex5_method_b(chi, 9, rule9)
            if wa is None and wb is None:
                bad.append((ck, "CONVEX5-FREE (would kill f(5)<=9!)"))
            elif (wa is None) != (wb is None):
                bad.append((ck, "method-disagree"))
            elif not (chi_witness_is_convex_both(chi, 9, rule9, wa)
                      and chi_witness_is_convex_both(chi, 9, rule9, wb)):
                bad.append((ck, "cross-fail"))
            else:
                wcomp[(h, len(set(wa) & set(hull)))] = \
                    wcomp.get((h, len(set(wa) & set(hull))), 0) + 1
        if (i + 1) % 25000 == 0:
            R(f"[certify]   convex-5 pass {i+1}/{N} ({time.time()-t0:.0f}s)")
    R("[certify] hull census: " +
      ", ".join(f"h={h}:{c}" for h, c in sorted(census.items())))
    le4 = sum(c for h, c in census.items() if h <= 4)
    R(f"[certify] hull<=4 stratum: {le4} types (all must contain convex 5)")
    for (h, nh), c in sorted(wcomp.items()):
        R(f"[certify]   hull={h} witness-hull-vertices={nh}: {c}")
    # coordinate A/B on a certified sample + witness
    rng = random.Random(20260101)
    skeys = rng.sample(list(types), min(sample, N))
    coord_bad = 0
    for ck in skeys:
        d = types[ck]
        pts = [(parse_frac(a), parse_frac(b)) for (a, b) in d["pts"]]
        ok, A5 = two_method_agree(pts)
        chi = unpack_signs(d["chi"], ntrip(9))
        wa = chi_convex5_method_a(chi, 9, rule9)
        if (bool(A5)) != (wa is not None) or not ok:
            coord_bad += 1
    R(f"[certify] coordinate A/B cross-check on {len(skeys)} sampled types: "
      f"{'GREEN' if coord_bad == 0 else f'RED ({coord_bad})'}")
    # the banked f(5) >= 9 witness (lower side)
    wb = json.load(open(os.path.join(HERE, "engine107", "witness_best.json")))
    w8 = [(int(x), int(y)) for (x, y) in wb["pts5"]]
    okw, A5w = two_method_agree(w8)
    chi8 = chi_of_points(w8)
    wa8 = chi_convex5_method_a(chi8, 8, rule_for(8))
    wb8 = chi_convex5_method_b(chi8, 8, rule_for(8))
    R(f"[certify] banked 8-point witness: GP={is_gp(w8)}, convex-5 subsets "
      f"{len(A5w)} (must be 0), two-method {'GREEN' if okw else 'RED'}, "
      f"chi-methods A={wa8} B={wb8} (both None)")
    witness_ok = okw and (not A5w) and wa8 is None and wb8 is None and is_gp(w8)
    if bad:
        R(f"[certify] !! FAILURES: {len(bad)} — samples: {bad[:5]}")
        return False
    if coord_bad or not witness_ok:
        R("[certify] !! coordinate/witness cross-check failures")
        return False
    R(f"[certify {now()}] GREEN — all {N} 9-point order types contain a "
      f"convex 5; census = the full 158817 mirror-identified classes; "
      f"witness f(5)>=9 stands -> THEOREM f(5) = 9")
    return True

# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", required=True,
                    choices=["ladder", "grind", "certify", "status"])
    ap.add_argument("--chunk", type=int, default=128)
    ap.add_argument("--walk-steps", type=int, default=6)
    ap.add_argument("--max-chunks", type=int, default=None)
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--wall-budget", type=int, default=None)
    ap.add_argument("--sample", type=int, default=400)
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    if args.stage == "ladder":
        stage_ladder()
    elif args.stage == "grind":
        stage_grind(chunk=args.chunk, walk_steps=args.walk_steps,
                    max_chunks=args.max_chunks, workers=args.workers,
                    wall_budget=args.wall_budget)
    elif args.stage == "certify":
        stage_certify(sample=args.sample, quick=args.quick)
    elif args.stage == "status":
        prog = _load_progress()
        print(f"done parents: {len(prog['done'])}/6405")
        print(f"census lines: {prog.get('census_lines', 0)}")
        print(f"chunks: {len(prog.get('results', []))}")
        print(f"stats: {prog.get('stats', {})}")

if __name__ == "__main__":
    main()
