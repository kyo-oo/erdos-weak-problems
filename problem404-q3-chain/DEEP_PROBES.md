# DEEP PROBES — WAR-C engine (task 2-b): C class-DP for Erdős #404, g(a,2) exact

**Date:** 2026-11-03 (session 2-b) · **Dir:** `problem404-q3-chain/` · **Status: COMPLETE — both targets resolved with exact certified values.**

$$g(a,2) \;=\; \max_{B \subseteq \{a+1,a+2,\dots\} \text{ finite}} v_2\!\Big(1 + \sum_{i \in B} \tfrac{i!}{a!}\Big)$$

## HEADLINE RESULTS

| a | verdict | exact g(a,2) | certified by |
|---|---------|-------------|--------------|
| **14** | **EXACT (was ALIVE >1100)** | **g(14,2) = 1522** | L=2200 DP: first unreachable level = 1523 (two-sided) + witness \|B\|=730, v₂(14!+Σ B!)=1533 ⇒ level 1522; verified GMP **and** pure Python |
| **34** | **EXACT (was ALIVE >1100; alive at the required L=2200, killed by the extension probe)** | **g(34,2) = 18412** | L=32768 DP: first unreachable = 18413 (two-sided) + witness \|B\|=9215, v₂(34!+Σ B!)=18444 ⇒ level 18412; verified GMP **and** pure Python |

Both former "unbounded candidates" of the a-sweep are now **BOUNDED with exact, two-sided-certified values**.
a=14 died below the 2048 wall; a=34 crossed the 2048/4096/8192/**16384** walls and died at 18412, below 32768.
Complete exact a-sweep to date (p=2): g(2)=253, g(4)=3, g(6)=129, g(8)=6, g(10)=6, g(12)=3, **g(14)=1522**, g(16)=533, g(18)=45, g(24)=39, g(30)=100, **g(34)=18412**, g(38)=793.

---

## 1. The engine — `class_dp.c` (C port of `class_dp2.py`, exact semantics)

- **Source:** `class_dp.c` (731 lines). Ground truth: `class_dp2.py` (sound scheduled-precision class-DP; the campaign's certified engine, Lean-crossed for a=2). `py_ref.py` = per-class-logging exact replica of `class_dp2.py` for diffing.
- **Build (clean, 0 warnings):**
  ```
  gcc -O2 -Wall -Wextra -std=gnu11 -o class_dp     class_dp.c -lgmp     # stock: CP ≤ 6080 (L ≤ 6072)
  gcc -O2 -Wall -Wextra -std=gnu11 -DWMAX=136 -o class_dp_w136 class_dp.c -lgmp   # L ≤ 16440
  gcc -O2 -Wall -Wextra -std=gnu11 -DWMAX=514 -o class_dp_w514 class_dp.c -lgmp   # L ≤ 32832
  ```
  GMP bignums (libgmp-dev 2:6.3.0) for coin building (`mpz` running product mod 2^(CP+64), exactly like the Python) and for independent witness verification (`mpz_fac_ui` + `mpz_scan1`).
- **States:** `(t,u)`, u < 2^(CP−t), in an arena + open-addressing hash table (2 tables ping-pong; 64-bit mixed hash; load 0.5). CP = L + slack (slack 8 default). Per class V: coins {i : v₂(i!/a!) = V} (≤2 for p=2), sigmas = nonempty subset sums mod 2^(CP−V); transitions `s = (u << (t−V)) + σ mod 2^(CP−V)`; `s=0` → cap sentinel (CP,1); else `(V+v₂(s), s>>v₂(s))`; frozen states t<V dropped (their valuation already recorded as an event).
- **Witness extraction:** backward DFS from the recorded best/cap event; per-sigma parent is the exact inverse (`r = (u<<(t−V)) − σ mod 2^(CP−V)`, parent = (V+ctz(r), r>>ctz(r))); pruned by (a) per-snapshot t-bitmap and (b) **exact** per-snapshot membership via a disk-backed sorted hash store (one unlinked temp file, 8 B/state/snapshot, binary search; degrades soundly to valuation-only on disk failure). Completion = landing on (0,1) at class 0; any completing chain is a real witness; re-verified independently by GMP bigints inside the engine, and again in pure Python (stdlib only) outside it.
- **Safety:** `--mem MB` cap (default 1000; all probe runs used `--mem 1500` ⇒ two tables ≤ 1500 MB total; graceful `MEMCAP/SIGNAL-ABORT` with sound partial report + exit code 2), `nice -n 10` on every run, single-threaded (2-core box, other jobs), SIGTERM/SIGINT graceful. Peak RSS over all runs: **1230 MB** (a=34, L=32768) < 1.5 GB cap.
- **Usage:** `./class_dp A P L [slack] [--witness] [--mem MB] [--log N] [--dfs-budget N] [--no-hashstore] [--dump-coins] [--dump-sets]` (p=2 only). Exit 0 ok / 2 memcap-signal / 3 usage-assert.
- **Speed vs Python** (same semantics, `py_ref.py`): a=14 L=300: 0.47 s (py) vs <0.01 s (C); L=600: 5.0 s (py) vs 0.02 s (C); L=2200 ≈ 10 min (py, extrapolated) vs **0.15 s** (C); L=32768 infeasible in Python vs **170 s** (C). ~10³–10⁵× at depth. Final-snapshot valuation histogram (`final_t_hist`) added this session (purely additive; battery re-run after the change).

## 2. VALIDATION — all green

### 2.1 Known-value battery (`run_battery.sh`, 18/18 PASS, both stock and `-DWMAX=514` builds)

| a | L | g expected | g (C) | first unreach | capped | witness (GMP) | witness (pure Python) |
|---|---|-----------|-------|---------------|--------|---------------|----------------------|
| 4 | 4 | 3 (Lean kill) | 3 | 4 | 0 | VERIFIED | PASS (3) |
| 8 | 7 | 6 (Lean kill) | 6 | 7 | 0 | VERIFIED | PASS (6) |
| 10 | 7 | 6 (Lean kill) | 6 | 7 | 0 | VERIFIED | PASS (6) |
| 12 | 4 | 3 (Lean kill) | 3 | 4 | 0 | VERIFIED | PASS (3) |
| 2 | 254 | 253 | 253 | 254 | 0 | VERIFIED \|B\|=118, B⊆[3,254], v₂=254 | PASS (253) |
| 2 | 320 | 253 (stability) | 253 | 254 | 0 | VERIFIED | PASS (253) |
| 6 | 130 | 129 | 129 | 130 | 0 | VERIFIED | PASS (129) |
| 6 | 200 | 129 (stability) | 129 | 130 | 0 | VERIFIED | PASS (129) |
| 16 | 534 | 533 | 533 | 534 | 0 | VERIFIED | PASS (533) |
| 16 | 600 | 533 (stability) | 533 | 534 | 0 | VERIFIED | PASS (533) |
| 18 | 46 | 45 | 45 | 46 | 0 | VERIFIED | PASS (45) |
| 18 | 120 | 45 (stability) | 45 | 46 | 0 | VERIFIED | PASS (45) |
| 24 | 40 | 39 | 39 | 40 | 0 | VERIFIED | PASS (39) |
| 24 | 120 | 39 (stability) | 39 | 40 | 0 | VERIFIED | PASS (39) |
| 30 | 101 | 100 | 100 | 101 | 0 | VERIFIED | PASS (100) |
| 30 | 180 | 100 (stability) | 100 | 101 | 0 | VERIFIED | PASS (100) |
| 38 | 794 | 793 | 793 | 794 | 0 | VERIFIED \|B\|=408, v₂=828 | PASS (793) |
| 38 | 900 | 793 (stability) | 793 | 794 | 0 | VERIFIED | PASS (793) |

Every run: `capped=0`, `g_interval_crosscheck consistent`, witness exact-equality verified twice (in-engine GMP; out-of-engine `verify_witness.py` pure-Python factorials). The a=2 witness matches the Lean-proven #14 parameters (118 elements, B ⊆ [3,254], v₂(2!+Σ)=254).

### 2.2 Cross-check vs Python at L=300, a=14 (the required cross-check) — IDENTICAL

- `./class_dp 14 2 300 --log 1` vs `py_ref.py 14 2 300`: **all 300 per-class lines identical** (`diff` empty — coins, state counts, maxevent at every class V=0..299).
- Finals identical across all three engines: C / `py_ref.py` / `class_dp2.py` (original): `g=300 (L-capped, alive), first-unreachable > 300, maxevent=308`.
- C witness at L=300: \|B\|=154, B ⊆ [15,315], v₂(14!+Σ)=319 ⇒ level 308 = maxevent; pure-Python verify **PASS (308)**.
- Bonus, same protocol at a=34, L=300: 300/300 per-class lines identical; finals identical (g=300 alive, maxevent=305); witness \|B\|=146, level 305, pure-Python **PASS (305)**.

Logs: `logs/c_x_a14_L300.log`, `logs/py_x_a14_L300.log`, `logs/py2_x_a14_L300.log`, `logs/c_x_a34_L300.log`, `logs/py_x_a34_L300.log`.

### 2.3 Why an exact verdict is two-sided certified

Level-l reachability depends only on coins of class < l (any coin of class ≥ l contributes 2^l·(odd·stuff); if the class-<l part has valuation < l the total does too). The DP at any L ≥ l tracks all class-<l coins at precision CP−t with EXACT state merging (the scheduled-precision invariant). Hence "first unreachable = g+1 at L > g" is a proof that no subset of any coins reaches g+1, while the extracted witness proves g is achieved. Both sides are machine-verified (DP snapshots / GMP+Python factorial check).

## 3. DEEP PROBE a=14 @ L=2200 — **EXACT: g(14,2) = 1522**

```
g(14,2) [C class_dp] = 1522
first UNREACHABLE level = 1523        ← two-sided upper bound: nothing reaches 1523, ever
max event valuation = 1522 | capped = 0 | g_interval_crosscheck = 1522 (consistent)
peak_states = 16760 | elapsed_s = 0.15 | peak_rss_mb = 8 | hashstore ok (9 MB)
WITNESS = VERIFIED |B|=730 Bmin=15 Bmax=1534 v2(a!+sum B!)= 1533 g-level=1522
```
- **Witness** (730 distinct coins, all in (14, 1534]): v₂(14! + Σ_{i∈B} i!) = 1533, v₂(14!) = 11 ⇒ **level 1522 exactly**. Verified in-engine (GMP) and out-of-engine (pure Python): `v2(a! + sum_B i!) - v2(a!) = 1522 expected == 1522 -> PASS`. Full list: `WITNESS_LIST` line in `logs/c_deep_a14_L2200.log`.
- **Death profile** (full-res log `logs/c_deep_a14_L2200_full.log`, all 2200 classes): maxevent first hits 1522 at class V=1514 (largest witness coin 1534 = the second class-1514 coin); then a clean geometric bleed-out of the live set: 508 → 252 → 111 → 53 → 25 → 14 → 5 → 1 → 0 states at classes 1515..1523; first empty class = 1523 = first unreachable level. Peak live set 2940 states (V=1000).
- **Stability:** L=3000 and L=6072 both reproduce `g=1522, first-unreachable=1523, witness level 1522` (`logs/c_stab_a14_L{3000,6072}.log`).
- **Reading:** a=14 crossed the 256/512/1024 walls and died at 1522, **below 2048**. The "a=14 crosses every wall ⇒ g=∞ ⇒ sub-Q3 YES" scenario is **dead**.

## 4. DEEP PROBE a=34 @ L=2200 — **ALIVE** (then killed by the extension probe: g(34,2)=18412)

### 4.1 The required L=2200 run — ALIVE
```
g(34,2) [C class_dp] = 2200           ← L-capped: every level 1..2200 reachable
first UNREACHABLE level = > 2200 (all 1..2200 reachable)
max event valuation = 2208 (=CP) | capped = 1 | crosscheck consistent
peak_states = 119000 | elapsed_s = 0.58 | peak_rss_mb = 16 | hashstore ok (58 MB)
WITNESS = VERIFIED |B|=1085 Bmin=35 Bmax=2235 v2(a!+sum B!)= 2241 g-level=2209
```
- Witness verified GMP + pure Python (`v2(34!+sum_B i!)-v2(34!) = 2209 -> PASS`); v₂(34!)=32, 2241−32 = 2209 ⇒ **g(34,2) ≥ 2209** already at L=2200.
- **State profile** (full-res, 2200/2200 classes, `logs/c_deep_a34_L2200_full.log`): never an empty class (alive at every class); states min=1 / median=1145 / mean=3504 / **max 119000 at V=2004**; coin classes: 1102 double, 1 single, 1097 empty; first cap event at V=2196; final snapshot 512 states. **Live frontier (final snapshot valuation histogram, the ALIVE signature):**
  ```
  final_t_hist: 2199:256 2200:128 2201:64 2202:32 2203:16 2204:8 2205:4 2206:2 2207:1 2208:1
  ```
  a self-similar dyadic ladder riding the precision ceiling — the structure that made a=34 look unbounded.

### 4.2 Extension probe (beyond task scope; stock build to L=6072, then `-DWMAX=136/514`)

| L | g_L | capped | witness level (GMP+py verified) | peak states | RSS | time |
|------|------|--------|--------------------------------|------------|------|------|
| 2400 | 2400 (alive) | 1 | 2409 | 119000 | 20 MB | 0.7 s |
| 2600 | 2600 | 1 | 2611 | 119000 | 24 MB | 0.8 s |
| 2800 | 2800 | 1 | 2808 | 119000 | 28 MB | 1.0 s |
| 3000 | 3000 | 1 | 3008 | 119000 | 32 MB | 1.1 s |
| 3500 | 3500 | 1 | 3508 | 119000 | 44 MB | 1.5 s |
| 4000 | 4000 | 1 | 4008 | 119000 | 57 MB | 2.1 s |
| 4500 | 4500 | 1 | 4512 | 119000 | 69 MB | 2.6 s |
| 5000 | 5000 | 1 | 5008 | 119000 | 80 MB | 3.2 s |
| 5500 | 5500 | 0 | 5507 | 119000 | 85 MB | 3.9 s |
| 6000 | 6000 | 1 | 6008 | 119000 | 92 MB | 4.6 s |
| 6072 | 6072 | 1 | 6082 | 119000 | 93 MB | 4.8 s |
| 8192 | 8192 | 1 | 8201 | 174616 | 159 MB | 9.0 s |
| 8600 | 8600 | 1 | 8610 | 174616 | 170 MB | 10.0 s |
| 16384 | 16384 | 0 | 16391 | 257856 | 401 MB | 47 s |
| **32768** | **18412 EXACT** | **0** | **18412** | **257856** | **1230 MB** | **170 s** |

- a=34 crossed the **2048, 4096, 8192 and 16384 walls** (alive = every level ≤ L reachable, at every L up to 16384), then **died at L=32768**:
  ```
  g(34,2) [C class_dp] = 18412
  first UNREACHABLE level = 18413
  max event valuation = 18412 | capped = 0 | crosscheck consistent
  WITNESS = VERIFIED |B|=9215 Bmin=35 Bmax=18446 v2(a!+sum B!)= 18444 g-level=18412
  ```
- **Witness** (9215 distinct coins ⊆ (34, 18446]): v₂(34!+Σ)=18444, minus v₂(34!)=32 ⇒ **level 18412 exactly**; in-engine GMP verify + independent pure-Python verify both **PASS (18412)**.
- **Stability:** L=19000 and L=20000 both reproduce `g=18412, first-unreachable=18413, witness 18412` (`logs/c_stab_a34_L{19000,20000}.log`) — the value is L-stable on [18413, 32768].
- Reading: the dyadic frontier ladder of §4.1 is real but **finite** — it carried a=34 past four power-of-two walls and broke at 18412 (largest witness coin 18446, class 18409, final wall-jump +3).

## 5. FILES

- `class_dp.c` — the engine (this session: histogram + WMAX-override + dynamic L-bound changes, all additive; battery 18/18 re-run after each change).
- `class_dp` (stock, WMAX=96, L ≤ 6072), `class_dp_w136` (L ≤ 16440), `class_dp_w514` (L ≤ 32832) — built from the same validated source (`run_battery.sh [bin]` re-validates any build; w514 also 18/18).
- `run_battery.sh` — reproducible validation battery (known values + Lean kills + stability + double witness verification).
- `py_ref.py`, `verify_witness.py` — cross-check replica and independent witness verifier (both prior-session files, used as-is).
- `logs/` (87 files): `c_val_*` (battery), `c_x_*`/`py_x_*`/`py2_x_*` (L=300 cross-checks), `c_deep_a14_L2200*`, `c_deep_a34_L2200*` (+`_full` full-res), `c_probe_a34_L*` (extension sweep), `c_stab_*` (stability), each with `.err` progress/timing.

## 6. NEXT ACTIONS

1. **a-sweep completion (cheap now):** run every even a ≤ ~60 at adaptive L (double L until death; ~minutes total). g(34)=18412 is the current record — check its neighbors (a=32, 33, 35, 36, 40, 48…) for bigger/∞ candidates. The engine is proven at CP=32776 (L=32768, 1230 MB, 170 s).
2. **Registry update:** both #404 sub-questions for p=2 lose their last "unbounded candidates" — every probed a now has an exact finite g(a,2). If the sweep finds no ∞, sub-Q3 (p=2 subsum-set question) trends NO; a structural obstruction proof (why every ladder dies) would close it.
3. **Lean (optional):** the a=14/a=34 certificates (witness + snapshot chain) are kernel-checkable exactly like #14 (`ExactF22.lean` pattern); the upper-bound side needs the §5d induction bridge already designed.
4. **Structure hunt:** the dyadic frontier (256:128:…:1 at the alive top, stable across L) and the geometric death tails (÷2 per class) are the two universal regimes seen so far — a "ladder operator" analysis on the class-2 coin pairs could bound all ladders and maybe prove g(a,2) < ∞ for all a.
5. Push L beyond 32768 with `-DWMAX=1026` only if a new candidate survives ~32768.

**Constraints honored:** GMP bignums; hash-table states; `--mem 1500` (≤1.5 GB; peak RSS 1230 MB); `nice -n 10` on every run; single-threaded; no `.lean` files touched; nothing pushed.
