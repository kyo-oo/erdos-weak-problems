#!/usr/bin/env python3
"""w66_dlx.py — THE DLX/EXACT-COVER RE-ATTACK with modern propagation (W66, mission 1).

The W56-era DLX drowned on the cell count (L^2 = 7.7e8..3e9 columns).  This
engine re-attacks with the column-int representation + propagation:

  (1) COLUMN-INT RESIDUAL: the whole torus residual lives as per-l Python
      ints (L bits each) — coverage verification is one OR pass (seconds);
  (2) FORCED-SWITCH SWEEP (the propagation cascade): per palette prime the
      EXACT-verified current assignment + the marginal gain of every
      candidate coset W (estimated on sampled columns, exact-verified after
      application) and the loss (cells covered ONLY by p — sampled); every
      positive-net switch is FORCED (unit-propagation fixpoint in the
      assignment lattice);
  (3) CLASS-RARITY HISTOGRAM: for sampled residual cells, the number of
      net-positive candidate primes (the DLX column-candidate count);
      0 candidates = the hard core, 1 = forced unit class;
  (4) the fixpoint uncovered count — the mission-1 measurement.

Usage: w66_dlx.py L PASSES [state.json]   (sampled columns SAMPLE=600)
"""
import json, math, os, sys, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import w66_lib as W

HERE = os.path.dirname(os.path.abspath(__file__))
PD = os.path.dirname(HERE)
SAMPLE = 600

def load_family_uv(L):
    """family rows (q, h, U, V, o2, o3): bank U,V authoritative; deep-scan
    primes get fresh dlogs (via the <2,3> walk)."""
    bank = W.load_bank()
    rows = {}
    for r in bank:
        q, h, U, V, o2, o3 = r
        if L % h == 0:
            rows[q] = (q, h, U, V, o2, o3)
    deep = {int(k): v for k, v in json.load(open(os.path.join(HERE, "w66_deep.json"))).items()}
    from w66_feas import gen_and_dlogs
    for q, r in deep.items():
        o2, o3, h = r[1], r[2], r[3]
        if L % h or q in rows:
            continue
        f = gen_and_dlogs(q, o2, o3, h)
        if f:
            rows[q] = (q, h, f[2], f[3], o2, o3)
    fam = sorted(rows.values(), key=lambda r: -1.0 / r[1])
    return fam

class Engine:
    def __init__(self, L, fam):
        self.L = L
        self.fam = fam
        self.full = (1 << L) - 1
        self.reps = {}
        for r in fam:
            o2 = r[4]
            if o2 not in self.reps:
                self.reps[o2] = W.repunit(o2, L) & self.full
        self.byq = {r[0]: r for r in fam}
        self.assign = None
        self.masks = None
        self.res = None

    def mask_for(self, q, Wv):
        r = self.byq[q]
        q_, h, U, V, o2, o3 = r
        g1 = math.gcd(U, h)
        uinv = pow(U // g1, -1, o2)
        rep = self.reps[o2]
        out = []
        for rr in range(o3):
            c = (Wv - V * rr) % h
            if c % g1:
                out.append(None)
            else:
                a = ((c // g1) * uinv) % o2
                out.append((rep << a) & self.full)
        return out

    def set_assign(self, assign):
        self.assign = dict(assign)
        self.masks = {q: self.mask_for(q, self.assign[q]) for q in self.assign}
        self.res = None

    def coverage(self):
        """recompute per-column residual; exact; returns total uncovered."""
        L = self.L
        total = 0
        res = []
        fam = self.fam
        for l in range(L):
            cm = 0
            for r in fam:
                mk = self.masks[r[0]][l % r[5]]
                if mk:
                    cm |= mk
            u = self.full ^ cm
            res.append(u)
            total += bin(u).count("1")
        self.res = res
        return total

    def gain_table(self, q, cols):
        """counts[W] over the residual, restricted to columns `cols`."""
        r = self.byq[q]
        q_, h, U, V, o2, o3 = r
        g1 = math.gcd(U, h)
        uinv = pow(U // g1, -1, o2)
        rep = self.reps[o2]
        full = self.full
        res = self.res
        cols_by_r = [[] for _ in range(o3)]
        for l in cols:
            cols_by_r[l % o3].append(l)
        counts = [0] * h
        for Wv in range(h):
            cnt = 0
            for rr in range(o3):
                c = (Wv - V * rr) % h
                if c % g1:
                    continue
                a = ((c // g1) * uinv) % o2
                mk = (rep << a) & full
                for l in cols_by_r[rr]:
                    cnt += bin(mk & res[l]).count("1")
            counts[Wv] = cnt
        return counts

    def loss_table(self, q, cols):
        """loss over the sampled columns: cells covered only by q."""
        o3 = self.byq[q][5]
        tot = 0
        for l in cols:
            cm = 0
            for r in self.fam:
                if r[0] == q:
                    continue
                mk = self.masks[r[0]][l % r[5]]
                if mk:
                    cm |= mk
            mk = self.masks[q][l % o3]
            if mk:
                tot += bin(mk & ~cm & self.full).count("1")
        return tot

    def apply_switch(self, q, Wnew):
        self.masks[q] = self.mask_for(q, Wnew)
        self.assign[q] = Wnew
        return self.coverage()

def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 27720
    passes = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    state_path = sys.argv[3] if len(sys.argv) > 3 else os.path.join(PD, "work/state27720.json")
    fam = load_family_uv(L)
    eng = Engine(L, fam)
    seed = {int(r[0]): int(r[4]) for r in json.load(open(state_path))}
    seed = {q: w for q, w in seed.items() if q in eng.byq}
    for r in fam:
        if r[0] not in seed:
            seed[r[0]] = 0
    t0 = time.time()
    eng.set_assign(seed)
    unc = eng.coverage()
    print(f"[L={L}] family={len(fam)} budget={sum(1.0/r[1] for r in fam):.4f} "
          f"budget-slack={sum(1.0/r[1] for r in fam)-1:.4f}", flush=True)
    print(f"[seed] uncovered={unc} ({100.0*unc/(L*L):.4f}%) ({time.time()-t0:.0f}s)", flush=True)
    rng = random.Random(20261116)
    report = {"L": L, "seed_uncovered": unc, "passes": []}
    scale = L / SAMPLE
    for ps in range(passes):
        t0 = time.time()
        cols = sorted(rng.sample(range(L), SAMPLE))
        moves = []
        for r in fam:
            q = r[0]
            gt = eng.gain_table(q, cols)
            lo = eng.loss_table(q, cols) * scale
            Wb = max(range(len(gt)), key=lambda i: gt[i])
            net = gt[Wb] * scale - lo
            moves.append((net, q, Wb, gt[Wb] * scale, lo, eng.assign[q]))
        moves.sort(reverse=True)
        applied = 0
        for (net, q, Wb, g, lo, Wcur) in moves:
            if net > 0 and Wb != Wcur:
                u = eng.apply_switch(q, Wb)
                applied += 1
                print(f"  [sweep {ps}] q={q} h={eng.byq[q][1]} W {Wcur}->{Wb} "
                      f"est.gain={g:.0f} est.loss={lo:.0f} => EXACT uncovered={u} "
                      f"({100.0*u/(L*L):.4f}%)", flush=True)
        unc = sum(bin(u).count("1") for u in eng.res)
        print(f"== pass {ps}: switches={applied} uncovered={unc} ({100.0*unc/(L*L):.4f}%) "
              f"({time.time()-t0:.0f}s)", flush=True)
        report["passes"].append({"ps": ps, "switches": applied, "uncovered": unc})
        json.dump({str(k): v for k, v in eng.assign.items()},
                  open(os.path.join(HERE, f"w66_dlx_L{L}_state.json"), "w"))
        json.dump(report, open(os.path.join(HERE, "w66_dlx_report.json"), "w"))

    # ---------------- rarity histogram (mission-1 measurement) ----------------
    t0 = time.time()
    cols = sorted(rng.sample(range(L), SAMPLE))
    gtables = {}
    losses = {}
    for r in fam:
        q = r[0]
        gtables[q] = eng.gain_table(q, cols)
        losses[q] = eng.loss_table(q, cols) * scale
    hist = [0] * (len(fam) + 1)
    nsamp = 0
    while nsamp < 200000:
        k = rng.randrange(L)
        l = rng.randrange(L)
        if (eng.res[l] >> k) & 1:
            cnt = 0
            for r in fam:
                q, h, U, V, o2, o3 = r
                wv = (U * (k % o2) + V * (l % o3)) % h
                if gtables[q][wv] * scale - losses[q] > 0:
                    cnt += 1
            hist[cnt] += 1
            nsamp += 1
    print(f"[rarity] {nsamp} sampled residual cells; net-positive candidate histogram:")
    for c, n in enumerate(hist):
        if n:
            print(f"   {c:3d} candidates: {n:7d} ({100.0*n/nsamp:.2f}%)")
    z = hist[0] / nsamp
    print(f"[rarity] hard core (0 candidates): {z*100:.2f}% of residual => ~{z*unc:.0f} cells")
    report["rarity_hist"] = hist
    report["total_uncovered"] = unc
    report["hard_core_estimate"] = z * unc
    json.dump(report, open(os.path.join(HERE, "w66_dlx_report.json"), "w"))
    print(f"wrote w66_dlx_report.json ({time.time()-t0:.0f}s for the histogram)")

if __name__ == "__main__":
    main()
