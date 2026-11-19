#!/usr/bin/env python3
"""fix_ot8.py — W75-107K commander surgery: the realization-diversity fix.

ROOT CAUSE (diagnosed this round): the insertion enumeration used ONE stored
realization per parent type. But the arrangement of pair-lines has face-lattice
freedom BEYOND the order type: within one order type's realization space,
cells can appear/disappear when 3 pair-lines cross a concurrency wall. Children
requiring a cell that exists only in another component were MISSED (1 mirror
failure + ~29 fully-missing chiral types at n=8: 3300 vs anchor 3315).

FIX: per parent, generate K additional TYPE-PRESERVING random perturbations
(canonical key verified unchanged), insert at ALL cells of EVERY realization.
The anchor count (2/3/16/135/3315) is the completeness certificate.

Output: engine107f5_cache/ot8.pkl with the certified 6432-ish reflection-
distinguished set + a receipt log.
"""
import pickle, sys, os, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import types as pytypes
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
os.chdir(HERE)
src = open('engine107f5.py').read()
mod = pytypes.ModuleType("eng"); mod.__file__ = os.path.abspath('engine107f5.py')
exec(compile(src.replace('if __name__ == "__main__":','if False:'), 'engine107f5.py','exec'), mod.__dict__)

random.seed(20270116)
K_EXTRA = 300         # perturbation attempts per parent
EPS = Fraction(1, 8)

def perturb_realizations(pts, key7, rule7, budget=K_EXTRA):
    """Type-preserving perturbations: small random rational jitter, verified
    by canonical key. Returns a list of DISTINCT realizations (as pts lists)."""
    outs = [ [tuple(p) for p in pts] ]
    seen_coords = { tuple(pts) }
    for _ in range(budget):
        cand = []
        for (x, y) in pts:
            dx = Fraction(random.randint(-14, 14), 10)
            dy = Fraction(random.randint(-14, 14), 10)
            cand.append((x + dx, y + dy))
        # distinct coordinates and GP
        if len(set(cand)) < len(cand): continue
        if not mod.is_gp(cand): continue
        if mod.canonical_key(mod.chi_of_points(cand), 7, rule7) != key7:
            continue
        tc = tuple(cand)
        if tc in seen_coords: continue
        seen_coords.add(tc)
        outs.append(cand)
    return outs

def main():
    t0 = time.time()
    with open('engine107f5_cache/ot7.pkl','rb') as f:
        parents = pickle.load(f)
    rule7 = mod.rule_for(7); rule8 = mod.rule_for(8)

    log = open('receipts_ot8fix.txt','w', buffering=1)
    def R(msg):
        print(msg, flush=True); log.write(msg+"\n")

    R("=== ot8 realization-diversity fix (commander surgery, W75-107K) ===")
    R(f"parents: {len(parents)} | extra perturbations per parent: up to {K_EXTRA}")

    results = {}   # ck -> chi (first seen)
    insertions = 0
    realizations_used = 0
    for idx, (pck, v) in enumerate(parents.items()):
        reals = perturb_realizations(v['pts'], pck, rule7)
        realizations_used += len(reals)
        for pts in reals:
            sheared, cells = mod.arrangement_cell_samples(pts)
            for (sx, sy) in cells:
                allpts = sheared + [(sx, sy)]
                chi = mod.chi_of_points(allpts)
                ck = mod.canonical_key(chi, 8, rule8)
                if ck not in results:
                    results[ck] = chi
                insertions += 1
        if idx % 40 == 0:
            R(f"  parent {idx}/{len(parents)}: types so far {len(results)} ({time.time()-t0:.0f}s)")

    R(f"TOTAL insertions: {insertions} | realizations used: {realizations_used} | types: {len(results)}")

    # mirror closure + identified count certificate
    self_mirror = 0
    closure_ok = True
    for ck in results:
        negk = mod.canonical_key(tuple(-s for s in ck), 8, rule8)
        if negk not in results:
            closure_ok = False
            R(f"!! mirror-closure failure: {str(ck)[:60]}")
        elif negk == ck:
            self_mirror += 1
    identified = (len(results) + self_mirror) // 2
    R(f"reflection-distinguished: {len(results)} | self-mirror: {self_mirror} | "
      f"mirror-identified: {identified} (anchor 3315)")
    if identified == 3315 and closure_ok:
        R("CERTIFIED: n=8 order-type enumeration COMPLETE (anchor match + mirror closure).")
        # store with realizations attached (store chi + the realizing pts for the n=9 step)
        store = {}
        # attach realizations lazily: recompute per type on demand later; store chi now
        for ck, chi in results.items():
            store[ck] = {'chi': chi, 'pts': None}
        # attach realizations: rerun insertion capturing pts per type
        for pck, v in parents.items():
            reals = perturb_realizations(v['pts'], pck, rule7)
            for pts in reals:
                sheared, cells = mod.arrangement_cell_samples(pts)
                for (sx, sy) in cells:
                    allpts = sheared + [(sx, sy)]
                    ck = mod.canonical_key(mod.chi_of_points(allpts), 8, rule8)
                    if ck in store and store[ck]['pts'] is None:
                        store[ck] = {'chi': mod.chi_of_points(allpts), 'pts': [tuple(p) for p in allpts]}
        missing_pts = sum(1 for v in store.values() if v['pts'] is None)
        R(f"realizations attached: {len(store)-missing_pts}/{len(store)}")
        with open('engine107f5_cache/ot8.pkl','wb') as f:
            pickle.dump(store, f, protocol=4)
        R("ot8.pkl saved — the n=9 step can proceed.")
    else:
        R(f"!! STILL MISMATCH: identified={identified} vs 3315, closure_ok={closure_ok}")
        # save for further diagnosis
        with open('/tmp/ot8_fix_partial.pkl','wb') as f:
            pickle.dump(results, f)
    R(f"wall: {time.time()-t0:.0f}s")
    log.close()

if __name__ == "__main__":
    main()
