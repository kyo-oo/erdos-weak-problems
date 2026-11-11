# ERDŐS #261 — FUNNEL RESULTS: session-019 engine reconstruction + frontier push (Agent 1-b)

Working dir: `/home/z/erdos-weak-problems/problem261-funnels/`. Sources: `PROBLEM.md`,
`DERIVATION.tex`, `FunnelStructure.lean` (Kill #10, kernel-green), `funnels.py`,
`engine/war261.c`, `engine/war261_dbg.c`, `engine/war261b.c`, `engine/results/*`,
`engine/run261/*`. This report adds one new run: `run261/fr_*` (frontier push, §5).

---

## 1. WHAT THE ENGINES COMPUTE (precise semantics)

All three engines implement the #261 walk (Kill #2 convention, identical to
`FunnelStructure.lean:walkStep/walkDeathAux/walkDeath` and `funnels.py:walk`):

- State `(N, v)`, `0 ≤ v < N`. Step: `v' = (2v) mod N` (modulus = **current** N;
  "take" iff `2v ≥ N`), `N' = N+1`. Start: `n=1 → (3,2)`, `n≥2 → (n+1,n)`,
  `n=0 → (1,0)` degenerate.
- **Death**: `v == 0` at state `(N,0)`; death modulus `D = N` (state *after* the
  zeroing step; last take used modulus `D−1`). `room(n) = D−1−n`.
  `n` terminates ⟺ its walk reaches `v = 0`.
- **Parity lemma** (asserted by both engines on every death): `D` is odd for all
  `n ≥ 1` (terminal step is a take with `2v = D−1`).
- **Coalescence certificate** (Lean `death_fuel_mono`, kernel-green): the death
  modulus is a function of the *state* alone — two walks sharing a state `(N,v)`
  share their whole future and die at the same `D`. This makes state→D tables
  sound, and makes "walker i hit a state of walker o's class" a valid death
  certificate.

**`war261b.c`** (primary, 1092 lines) — five modes:

| mode | what it does |
|---|---|
| `sweep lo hi cap` | direct walks, **no** tables (independent baseline); prints `n D steps` |
| `deep n cap bits certfile emitmin` | single-walk deep verifier; resumable (`war261b.ckpt`); probes/emits certs at N aligned to `2^bits` + the start state; `certfile -` = pure direct |
| `deepmany nlist …` | deep verifier over an n-list, shared in-memory cert table, cert emission |
| `batch lo hi cap round0 mult bits tbits chunk emitmin …` | **all-n certification of [lo,hi]**: walkers (struct-of-arrays) + union-find coalescence via a walker table (state→walker-id, probed/inserted at `2^bits`-aligned N) + persistent cert table (state→D, 2^21 slots, text file `N v D`, loaded from `certin` at every chunk boundary except the first, grown in memory, deep direct deaths re-walked and appended to `certout`) |
| `funnels deathsfile [minD maxD]` | clusters deaths by D; prints head hierarchy (D, count, n-range) |

Death-file line semantics: `n D m` with `m ∈ {d,c,w}` — **d** = walked to `v=0`
directly; **w** = certified by walker-table coalescence (hit a state of a
dead/live walker class); **c** = certified by the persistent cert table
(cross-run). `n 0 N v steps` = unresolved at cap. Merges file: `n_member
n_target N` (merge detected at an aligned N; exact merge ≤ one alignment
earlier). Batch sanity gates: even `D` or `D ≤ n` ⇒ FATAL (engine bug);
`emit_walk_certs` re-walks each emitted walk and FATALs if the re-walk dies at
any `D ≠` the recorded one; cert-table conflicts FATAL. Resources: walker table
`2^tbits × 12 B`, cert table 32 MB, walkers ~66 B/n. Measured rate:
**~1.13×10⁹ steps/s** (fr_log.txt).

**`war261.c`** (engine A): `verify` (single direct walk), `batch` (walker-table
coalescence, separate probe/insert periods `2^pbits/2^ibits`), `merge`
(fine-grained merge logging), `refine na nb N0 window` (exact first-merge point
of two walks). No persistent cert table.

**`war261_dbg.c`**: war261.c + `DBG`/`DBG2` env-var tracing. **Contains an
alignment bug**: `nextA = (N + pM) & ~pM` (vs the correct `((N|pM)+1) & ~pM`)
gives zero progress when N is already aligned — it hung spinning at walker
n=3817, N=65536, producing the 492 MB `results/dbg_trace.txt` (tail = the same
`aligned i=3816 N=65536` line repeated). Do not use for production.

## 2. RUN INVENTORY (recovered from file contents + snapshot headers)

Snapshot headers (`WAR261S1`/`WAR261B2`, `lo hi clo chi round budget cap WC`)
recover every run's exact parameters:

| run | engine | range | cap | status |
|---|---|---|---|---|
| `results/b_*` | war261 | [3401,3590] | 4×10⁸ | complete, 190/190 died |
| `results/t_*` | war261 | n=3590 verify | 4×10⁸ | D=12231 |
| `results/h_*`, `results/dbg_*` | war261 / _dbg | [1,4000] | — | **killed** at n≈3590/3817 (session died; dbg hung); last line torn ("359"); 3590 logged deaths valid |
| `results/rs_*` | war261 | [3000000,3000200] | 2×10⁹ | complete, 201/201 died |
| `results/val_V1_*` | war261 | [1,4000] | 4×10⁸ | complete |
| `results/val_V2_*` | war261b | [1,4000] | 4×10⁸ | complete |
| `run261/v2_*` | war261b | [1,4000] | 10⁷ | complete (580 d / 3420 w) |
| `run261/v2b_*` | war261b | [1,4000] | 10⁷ | complete (3999 d / 1 w) |
| `run261/v3_*` | war261b | [3000000,3000199] | 2×10⁹ | complete |
| `run261/p0_*` | war261b | [3000200,3020199] | 2×10⁹ | complete |
| `run261/cert_main.txt`, `cert_p0.txt` | war261b | trunk spines | — | 1381 certs each |
| **`run261/fr_*` (NEW, this agent)** | war261b | **[3200001,3200200]** | 2×10⁹ | **complete, 7.4 s** |

## 3. CERTIFIED FINDINGS (numbers + receipts)

### F1 — [1,4000]: 4000/4000 terminate; census reproduced 5 independent ways
Death-modulus distribution identical across `funnels.py` (Python, exact), Lean
`#eval` receipts (n=1..19, 56, 100, 200, 399, 3817 — all match), `val_V1`
(war261.c), `val_V2`/`v2` (war261b coalescing), `v2b` (war261b essentially
direct) and `val_sweep_4000.txt` (war261b sweep, no tables):
**112 distinct heads**; top: `12231: 2578 (64.4%)`, `4855: 475`, `4993: 103`,
`2593: 101`, `4489: 99`, `393: 90`, `1943: 66`, `29753: 47`, `6273: 43`
(v2_deaths.txt; per-n zero mismatches vs v2b vs sweep vs val_V1 vs val_V2).
Receipts: `run261/v2_deaths.txt`, `run261/val_sweep_4000.txt` (n=3817 →
155943 = the Lean receipt; n=56 → 12231; n=100 → 393; n=200 → 217).
The v2b single 'w': n=2 — its start (3,2) is literally n=1's start state (the
first coalescence), caught by the walker table.

### F2 — [3000000, 3020199]: 20200/20200 terminate at cap 2×10⁹ steps/walk
`run261/v3_deaths.txt` (200 walks) + `run261/p0_deaths.txt` (20000 walks),
zero unresolved; independently, `results/rs_deaths.txt` (war261.c, 201 walks
[3000000,3000200]) agrees. **33 distinct heads** in p0; the hierarchy
(`war261b funnels run261/p0_deaths.txt`):

| D | walks | share | n-range |
|---|---|---|---|
| 1449322159 | 8472 | 42.4% | [3000200, 3020193] |
| 5061761 | 5388 | 26.9% | [3000216, 3020198] |
| 7466441 | 2575 | 12.9% | [3000209, 3020196] |
| 3437089 | 1608 | 8.0% | [3000203, 3020197] |
| 3254287 | 1142 | 5.7% | [3000202, 3020199] |
| 3089665 | 185 | 0.9% | [3000239, 3020127] |
| … 27 more shallow heads … | | | min D = 3002593 |

Top-5 heads absorb **95.9%** of all 20000 starts. Modes p0: 659 d / 19340 w / 1 c.

### F3 — The giant funnel D = 1,449,322,159 (the deepest known head)
- Trunk witness n=3000000: start (3000001, 3000000) (cert_main.txt line 1),
  dies at D = 1449322159 after **1,449,322,158 steps** (= D − 3000001; matches
  the campaign WORKLOG number).
- **Persistent cert spine**: `cert_main.txt` / `cert_p0.txt` — 1381 aligned
  states `N v D` on the trunk orbit, N from 3000001 to **1449132032** (last
  checkpoint before death), v up to 1423245056 (≈ 0.983·N — take-heavy finish).
  Any walk reaching any of these states is instantly certified.
- **Trunk junction**: the n=3000000 and n=3000200 spines differ for 287 states
  (N ≤ 301989888) and coincide for **1094 states from N = 303,038,464**
  (state (303038464, 259113188)) to death — the two trunks coalesce at
  N ≈ 3.03×10⁸. The frontier run then produced a merge event at **exactly
  N = 303038464** (fr_merges.txt) — a third independent walk entering the trunk
  at the same junction.
- Independent trunk entries: p0 has direct deaths 3000200 (D=1449322159),
  3000216 & 3000222 (D=5061761 — two separate trunks of the same head),
  3000209 (D=7466441); v3 had 3000001 & 3000016 both dying direct at 5061761.
  Different orbits enter the same funnel along distinct routes and coalesce
  between aligned checkpoints (hence multiple 'd' per head).

### F4 — Coalescence is front-loaded
Merge-N histogram (p0 + fr, 11089 events): **3145728 (=3·2^20): 10988,
4194304: 88, 5242880: 7, 7340032: 1, 9437184: 2, 11534336: 2, 303038464: 1**.
99.5% of detected merges happen at the first two 2^20-aligned checkpoints —
within ≤ ~1.2×10⁶ steps of start the walk has already joined its funnel. The
state space behaves like a coalescence tree with extremely shallow merge depth
relative to walk length (walks then travel ~10⁹ steps inside the funnel).

### F5 — Global invariants over all 43,969 death records
Every death line in all 12 deaths files (v2, v2b, v3, p0, fr, h, dbg, val_V1,
val_V2, b, rs, t): **D odd (parity lemma) — 0 violations; D > n — 0 violations.**

### F6 — NEW (this agent): frontier push [3200001, 3200200] — 200/200 terminate in 7.4 s
`run261/fr_*`: `war261b batch 3200001 3200200 2000000000 100000000 10 20 20 100
1000000000 fr_deaths.txt fr_merges.txt fr_snap.bin cert_p0.txt
cert_frontier.txt` (nice −10, hard timeout, 7.4 s wall, 1.96×10⁹ walk steps,
~100 MB RAM). Result: **unres=0, unlogged=0**; modes 20 d / 170 w / **10 c**.
- The 10 'c' hits (n = 3200102, 3200106, 3200125, 3200127, 3200140, 3200165,
  3200166, 3200170, 3200175, 3200185) were certified **instantly, zero
  walking**, by the cert_p0.txt spine — first demonstration of cross-run
  certificate reuse at the frontier.
- Hierarchy (8 heads): `1449322159: 94 (47%)`, `7466441: 46 (23%)`,
  `5061761: 44 (22%)`, then 3437089: 5, **3275033: 4 (new head)**, 4021505: 4,
  3254287: 2, 3217537: 1. Same top-3 heads as at 3.0×10⁶ — the deep-funnel
  architecture is stable across 2×10⁵ of n; top-3 = 92%.
- **No death modulus exceeds 1449322159** — the giant head persists, no deeper
  funnel appears in this block. Max room: 1,446,122,155 (n=3200003); median
  room 4,266,401; min 17,458.
- `cert_frontier.txt`: 1380 new trunk certs (start state (3200004, 3200003)
  → N=1449132032, all D=1449322159); the internal re-walk check verified the
  trunk re-walk (1,446,122,155 steps) dies at exactly D.

## 4. THE FUNNEL HIERARCHY PICTURE

The absolute state space under φ(N,v) = (N+1, 2v mod N) is a coalescence
forest whose sinks are the death states (D−1, (D−1)/2) → (D, 0):

- **Scale 10³** ([1,4000]): 112 heads; giant 12231 (64%), then 4855 (12%),
  4993, 2593, 4489, 393, 1943, 29753 (the deep one holding [3113,3329]), …
- **Scale 3×10⁶** ([3000000,3020199]): 33 heads per 20K starts; the hierarchy
  is *dominated by three mega-funnels* — D = 1449322159 (42%), 5061761 (27%),
  7466441 (13%) — absorbing 82%; shallow heads (D ≈ 3.0-4.0×10⁶, i.e. room
  10³-10⁶) make up the tail.
- **Head structure**: each head D has a unique pre-death state; trunks enter
  it via multiple routes (≥2 independent trunks observed for 5061761), coalesce
  late (e.g. at N=3.03×10⁸ for the giant), then run ~10⁹ steps together.
- **Dynamics**: fast sorting (merges at the first aligned N) + long shared
  tail. This is exactly the structure the termination proof program needs:
  enumerate heads, show every start orbit enters one.

## 5. ALL-n TERMINATION FRONTIER — VERDICT

- Previously certified (campaign WORKLOG + PROBLEM.md): all n ≤ 2×10⁵
  (contiguous, all-n), plus the block [3×10⁶, 3.2×10⁶] (2×10⁹-step deep
  verifier; PROBLEM.md: "verified to 3·10⁶" by the earlier 64-bit engine).
- Session 019 independently re-certified [1,4000] (5 ways) and
  [3000000, 3020199] (2 engines).
- **NEW (fr run): [3200001, 3200200] all terminate** ⇒ the contiguous
  certified range now ends at **n = 3,200,200**. **The frontier is
  3,200,201.**
- **No nontermination candidate exists anywhere**: 43,969/43,969 walks die;
  the record death modulus is still D = 1,449,322,159 (giant funnel, stable
  from 3.0×10⁶ to 3.2×10⁶); every observed room is finite (max observed
  1.446×10⁹ at n=3200003, growing ~linearly with n — consistent with the
  greedy room being unbounded, which kills the naive Q3-bridge route but not
  termination).

## 6. RECOMMENDED NEXT STRIKE (concrete)

**Frontier march with rolling cert tables** — the fr run proves the economics:
200 walks / 7.4 s with 10 free cert hits; p0 (20K walks) also finished within
the session. Concretely:

```
for block in 3200201..(+20000 each):
  war261b batch <lo> <lo+19999> 2000000000 100000000 10 20 23 10000 1000000000 \
      deaths merges snap cert_in.txt cert_out.txt    # rotate cert_in ← cert_out
```
- Cost: measured 20K-walk blocks in minutes each (≈10⁵–10⁶ n per session-hour);
  RAM ≈ 100–350 MB (tbits=23 → 100 MB walker table). Cert spine grows +1380
  states per new deep trunk and certifies ~5% of subsequent walks for free.
- What it decides: (a) extends the contiguous all-n certified frontier
  (target: 3.3×10⁶ then 4×10⁶); (b) a **new-record death modulus** (>1.449×10⁹)
  would appear as an unresolved-at-cap or novel deep D — the first genuine
  nontermination-adjacent signal; (c) measures how far the 1449322159
  mega-funnel basin extends (does its 42-47% share persist?).
- Discipline: run under `nice -n 10` with hard `timeout`, `chunk ≤ 20000`
  (chunk boundaries are where `certin` reloads — keep ≥2 chunks so certs load),
  `emitmin ≥ 10⁹` to bound the re-walk budget (engine self-limits at 2×10¹⁰).
- Secondary (free): `war261b funnels` on each new deaths file to track the head
  hierarchy; keep deaths/merges/cert files as the audit trail. Fix or retire
  `war261_dbg.c` (alignment bug, §1) before any further dbg use.
- Theory target the data begs for: the fast-sorting phenomenon (F4) — prove
  merges must happen near start (e.g. via a congruence/2-adic argument on
  v_{N+k}) ⇒ every orbit enters a funnel in bounded lookahead; combined with
  head enumeration this is the all-n proof program mapped in DERIVATION.tex §3.

---

# FRONTIER MARCH (session 020, Agent 1-e) — three 20K blocks, [3200201, 3260200]

Executed §6's recommended strike exactly. Every block: `war261b batch <lo> <hi>
2000000000 100000000 10 20 23 10000 1000000000 <deaths> <merges> <snap>
<certin> <certout>` (cap 2×10⁹/walk, round0 10⁸ ×10 → 10⁹ → 2×10⁹, probe/emit
alignment 2^20, walker table 2^23 slots, chunk 10000 → 2 chunks/block, emitmin
10⁹), `nice -n 10`, one job at a time, RSS watched (peak ≈ 92 MB ≪ 1.5 GB cap;
box 2 core / 4.2 GB, no swap, load < 0.1, no thrashing). Cert rotation:
`cert_march.txt` initialized as `cert_main+cert_p0+cert_frontier` (4142 lines /
1670 distinct states, all D=1449322159), each block reads it as `certin` and
appends its `certout` for the next block. Receipts: `run261/m{1,2,3}_*`,
`run261/cert_m{1,2,3}.txt`, `run261/cert_march.txt`, logs `m{1,2,3}_log.txt`.

## Per-block results (all: unres=0, unlogged=0, exit 0, 0 even D, 0 D≤n)

| block | n-range | walks | d / c / w | steps marched | re-walk | wall | RSS | heads | alias |
|---|---|---|---|---|---|---|---|---|---|
| m1 | [3200201, 3220200] | 20000/20000 | 1978 / 2610 / 15412 | 2.030×10¹⁰ | 1.446×10⁹ | 30.7 s | 92.2 MB | 20 | 4828 |
| m2 | [3220201, 3240200] | 20000/20000 | 2095 / 2724 / 15181 | 1.989×10¹⁰ | 1.446×10⁹ | 30.3 s | 92.3 MB | 23 | 4685 |
| m3 | [3240201, 3260200] | 20000/20000 | 1701 / 2933 / 15366 | 1.975×10¹⁰ | 1.446×10⁹ | 29.9 s | 90.1 MB | 24 | 4869 |

March total: **60000/60000 terminate in 90.9 s engine time** (≈660 n certified/s).
Contiguity machine-checked: the concatenated deaths files contain exactly
n = 3200201…3260200 once each, zero gaps (awk pass). Independent no-table
cross-check (`war261b sweep`, direct walks): 7/7 stratified n match the batch
death moduli exactly — n = 3200201, 3210200, 3230200, 3240201, 3260200 →
1449322159; 3220201 → 5061761; 3250200 → 7466441.

## Head hierarchy per block (top of `war261b funnels`)

| D | m1 walks (%) | m2 walks (%) | m3 walks (%) |
|---|---|---|---|
| 1449322159 | 9507 (47.5) | 9423 (47.1) | 9685 (48.4) |
| 5061761 | 4775 (23.9) | 4909 (24.5) | 4292 (21.5) |
| 7466441 | 3744 (18.7) | 3577 (17.9) | 4327 (21.6) |
| 4021505 | 763 (3.8) | 862 (4.3) | 711 (3.6) |
| 3437089 | 599 (3.0) | 573 (2.9) | 320 (1.6) |
| next (3275033…) | 322 | 283 | 258 |

Top-3 mega-funnels absorb 90.1% / 89.5% / 91.5% (m1/m2/m3) — vs 82.2% at p0
([3.00,3.02]×10⁶) and 92.0% at fr: **the deep-funnel architecture is stable and
slightly tightening across 2.6×10⁵ of n**. Note m3: 7466441 (21.6%) overtook
5061761 (21.5%) for second place. New shallow heads appear (3547207 in m2+m3,
3676951 in m3, plus minor churn; all D < 3.7×10⁶ ≪ record) while the head count
per 20K block stays ~20-24 — the shallow tail keeps re-mixing, the deep
mega-funnels persist.

## Record death modulus: UNCHANGED

**Max D over all 60000 walks = 1,449,322,159** (unchanged since n=3.0×10⁶;
deepest single walk: n=3240201-class trunk, 1.446×10⁹ steps). No
unresolved-at-cap walk, no novel deep D, no nontermination-adjacent signal.

## Cert-table growth + reuse economics — the spine has CONVERGED

- Chain file: 4142 → 5522 → 6902 → 8282 lines, but **distinct states only
  1670 → 1671 → 1672 → 1680**: each block's giant-trunk emission (1380 lines,
  start state e.g. `(3240202, 3240201)`) is ~99.9% already-certified states.
  Reason: the map is deterministic, so every giant-trunk walk passes the SAME
  `(N, v)` at each 2²⁰-aligned N after its junction — one trunk emission
  certifies the whole shared spine; new emissions add only their pre-junction
  entry states (1-8 per block).
- Instant-'c' reuse (chunk 2 of each block, where `certin` loads): 2610 →
  2724 → 2933 per 10000 walks (26.1% → 27.2% → **29.3%**, rising; fr baseline
  10%). March steps/block fell 2.030 → 1.989 → 1.975×10¹⁰ at a steady
  ~8.7×10⁸ steps/s — **the march is mildly accelerating**.
- Structural observation: `certin` loads only at chunk boundaries ≠ first, so
  each block's chunk 1 runs certless and pays one full deep-representative
  trunk march + re-walk (2×1.446×10⁹ steps ≈ 3 s, the `rewalk` column). Within
  a run the walker table already catches spine hits ('w'), so cross-run certs
  currently convert would-be-'w' to 'c' at equal cost; their decisive value is
  the fr-style cold-start and future blocks against retired walkers. An engine
  tweak "load certin at run start too" would recover the ~10%/block chunk-1
  tax.
- Merge histogram (m1+m2+m3, 14382 events): **4194304 (=4·2²⁰): 14355 (99.8%)**,
  5242880: 15, 9437184: 3, 7340032: 3, 11534336: 3, 303038464: 3 (the giant
  junction). F4's front-loaded coalescence confirmed at the new frontier —
  for n≈3.2×10⁶ the first 2²⁰-aligned checkpoint is 4194304 (for p0's n≈3.0×10⁶
  it was 3145728): essentially every walk is sorted into its funnel within
  ≤10⁶ steps of start, then rides ~10⁹ steps inside it.

## Frontier verdict

- **Contiguous all-n certified frontier: n = 3,260,200** (was 3,200,200; this
  session added 60000 consecutive n in 3 blocks, all terminating). Next
  unverified n: 3,260,201.
- Cost model for the next strike: ~30 s per 20K block at the current frontier
  (~2.4×10⁶ n per engine-hour; will rise slowly — deep-head walk length grows
  ~linearly with n). Target 3.3×10⁶ needs 2 more blocks (~1 min); 4×10⁶ needs
  ~37 blocks (~20 min engine time). Same command pattern, keep rotating
  `cert_march.txt` (now 8282 lines / 1680 distinct).
- Standing watch: any D > 1,449,322,159 or any unresolved-at-cap walk is the
  nontermination-adjacent alarm — none seen in 103,969 total death records
  (43,969 prior + 60,000 this session).

---

# FRONTIER MARCH RE-RUN + EXTENSION (session 021, Agent Q1) — 19 blocks, [3260201, 4400200]

**This session re-runs and extends the wiped unpushed session** (a prior agent
pushed 3,260,200 → 3,740,200 in 8 blocks / 480,000 walks, 17/17 deep
cross-checks, record-D unchanged — all lost in a sandbox wipe, never pushed).
Re-derivation here starts from the CI-green pushed frontier n = 3,260,200 with
fresh binaries and fresh receipts: blocks **e1–e8** reproduce the wiped result
(8 × 60,000 walks → frontier 3,740,200), blocks **e9–e19** extend it a further
+660,000 to **n = 4,400,200**. Total this session: **1,140,000 consecutive n,
all terminating**.

Protocol = §6 / session-020 exactly, in 60,000-n blocks (6 chunks of 10,000):
`war261b batch <lo> <hi> 2000000000 100000000 10 20 23 10000 1000000000
<deaths> <merges> <snap> <certin> <certout>`, `nice -n 10`, hard `timeout 900`,
**two blocks at a time** on the 2-core box (peak RSS 113–115 MB per job, ≈228 MB
combined ≪ 800 MB cap; no swap configured). Cert chain rotated per wave:
`cert_march.txt` 8,282 → **34,499 lines / 1,728 distinct** states. Receipts:
`run261/e{1..19}_*`, `run261/cert_e{1..19}.txt`, logs `e{1..19}_log.txt`,
wrapper `run261/run_block.sh`.

**Engine-reconstruction gate (before the march):** binaries were absent (wipe);
rebuilt with `gcc -O3 -march=native -funroll-loops`. The fresh `war261b`
reproduced the committed fr run **bit-for-bit** — deaths file identical incl.
d/c/w modes (200 lines), cert emission identical to `cert_frontier.txt`,
7.4 s, totals 1,960,925,658 steps (`run261/valq_*`); plus `war261b sweep` on
n = 3240203/3240204/3260200 and engine-A `war261 verify` on n = 3260200 all
match the committed m3/fr data exactly.

## Per-block results (all: unres=0, unlogged=0, exit 0, 0 even D, 0 D≤n, 0 FATAL)

| block | n-range | walks | d / c / w | steps marched | re-walk | wall | RSS | heads | alias |
|---|---|---|---|---|---|---|---|---|---|
| e1 | [3260201, 3320200] | 60000/60000 | 5152 / 13405 / 41443 | 5.334×10¹⁰ | 1.446×10⁹ | 52.6 s | ~113 MB* | 43 | 4813 |
| e2 | [3320201, 3380200] | 60000/60000 | 4085 / 14449 / 41466 | 5.023×10¹⁰ | 1.446×10⁹ | 67.5 s | 113.0 MB | 39 | 4605 |
| e3 | [3380201, 3440200] | 60000/60000 | 2776 / 15982 / 41242 | 4.778×10¹⁰ | 1.446×10⁹ | 65.4 s | 113.2 MB | 40 | 5787 |
| e4 | [3440201, 3500200] | 60000/60000 | 2836 / 15334 / 41830 | 4.423×10¹⁰ | 1.446×10⁹ | 60.0 s | 113.2 MB | 44 | 5757 |
| e5 | [3500201, 3560200] | 60000/60000 | 2394 / 17647 / 39959 | 4.072×10¹⁰ | 1.446×10⁹ | 56.4 s | 113.4 MB | 34 | 5680 |
| e6 | [3560201, 3620200] | 60000/60000 | 2498 / 18035 / 39467 | 3.715×10¹⁰ | 1.446×10⁹ | 68.0 s | 113.2 MB | 45 | 5647 |
| e7 | [3620201, 3680200] | 60000/60000 | 1745 / 19000 / 39255 | 3.390×10¹⁰ | 1.446×10⁹ | 63.4 s | 114.2 MB | 37 | 5908 |
| e8 | [3680201, 3740200] | 60000/60000 | 1136 / 16606 / 42258 | 3.054×10¹⁰ | 1.446×10⁹ | 63.7 s | 113.2 MB | 49 | 5692 |
| e9 | [3740201, 3800200] | 60000/60000 | 1704 / 13835 / 44461 | 2.687×10¹⁰ | 1.446×10⁹ | 60.6 s | 113.2 MB | 38 | 5870 |
| e10 | [3800201, 3860200] | 60000/60000 | 1651 / 15037 / 43312 | 2.332×10¹⁰ | 1.446×10⁹ | 51.7 s | 113.1 MB | 36 | 5618 |
| e11 | [3860201, 3920200] | 60000/60000 | 1359 / 13221 / 45420 | 1.982×10¹⁰ | 1.445×10⁹ | 48.0 s | 113.2 MB | 43 | 5655 |
| e12 | [3920201, 3980200] | 60000/60000 | 1039 / 10643 / 48318 | 1.631×10¹⁰ | 1.445×10⁹ | 39.6 s | 113.3 MB | 41 | 5423 |
| e13 | [3980201, 4040200] | 60000/60000 | 438 / 7190 / 52372 | 1.285×10¹⁰ | 1.445×10⁹ | 35.9 s | 113.2 MB | 47 | 5604 |
| e14 | [4040201, 4100200] | 60000/60000 | 197 / 8278 / 51525 | 0.937×10¹⁰ | 1.445×10⁹ | 26.7 s | 113.0 MB | 47 | 5781 |
| e15 | [4100201, 4160200] | 60000/60000 | 783 / 4192 / 55025 | 0.605×10¹⁰ | 1.445×10⁹ | 22.3 s | 112.8 MB | 45 | 5281 |
| e16 | [4160201, 4220200] | 60000/60000 | 7695 / 11226 / 41079 | 3.053×10¹⁰ | 1.445×10⁹ | 69.1 s | 113.6 MB | 41 | 5326 |
| e17 | [4220201, 4280200] | 60000/60000 | 13406 / 16832 / 29762 | 5.684×10¹⁰ | 1.445×10⁹ | 98.4 s | 113.2 MB | 40 | 5447 |
| e18 | [4280201, 4340200] | 60000/60000 | 11398 / 18842 / 29760 | 5.437×10¹⁰ | 1.445×10⁹ | 107.9 s | 114.5 MB | 42 | 5556 |
| e19 | [4340201, 4400200] | 60000/60000 | 10487 / 20459 / 29054 | 5.147×10¹⁰ | 1.445×10⁹ | 108.2 s | 113.4 MB | 30 | 5481 |

\* e1 predates an RSS-sampler fix (measured the `timeout` wrapper, not the
engine); e2–e19 measured 112.8–114.5 MB, e1 has the same allocation profile.
e1 ran solo; e2–e19 walls are under 2-way block sharing (2 cores).

March total: **1,140,000/1,140,000 terminate** — 645,680,934,127 walk steps
marched + 27,464,917,164 re-walk steps (19 trunk emissions, one per block,
each internally re-verified by `emit_walk_certs`), 1,165.4 s summed engine
time / ≈639 s wall (≈1,785 n/s wall, ≈978 n/s engine-summed). Contiguity
machine-checked: the concatenated deaths files (1,140,000 lines) contain
exactly n = 3260201…4400200 once each, zero gaps/dups (sorted awk pass).
Global invariants over all 1,140,000 death records: **D odd, D > n — 0
violations**. Mode census: 72,779 d / 270,213 c / 797,008 w.

## Deep cross-checks: 21/21 PASS, zero nontermination signals

- 19 stratified **no-table `war261b sweep`** direct walks (one per block,
  rotating position): all match the batch death moduli exactly — n = 3260201,
  3340200, 3410201 (→5061761), 3470200 (→7466441), 3530201, 3590200 (→5061761),
  3650201, 3710200, 3770201, 3800201, 3890200, 3950201, 4010200 (→5061761),
  4070201, 4130200 (→5061761), 4190201 (→7466441), 4250200, 4310201, 4400200
  (→**5079041**, the shadow-era head) — all others → 1449322159.
- 2 independent **engine-A** (`war261 verify`) confirms: n = 3800201 →
  D = 1449322159 (steps 1,445,521,957 = e10's re-walk receipt), n = 4400200 →
  D = 5079041 (678,840 steps).
- **Unresolved-at-cap walks: 0 in all 19 blocks** — the 2×10⁹-step deep
  verifier was never needed; no novel deep D, no nontermination-adjacent
  signal of any kind.

## Record death modulus: UNCHANGED — and the ALIGNMENT-SHADOW regime at n ≈ 4.19×10⁶

**Max D over all 1,140,000 walks = 1,449,322,159** (unchanged since 3.0×10⁶;
deepest single walk this session: the n = 3260201 trunk, 1,446,061,957 steps;
max room 1,446,061,957 @ n=3260201 — below the campaign max 1,446,122,155
@ n=3200003, as room shrinks ~linearly with n; median room 1,445,039,237).

**New phenomenon (first seen this session; a predictable consequence of F4's
structure):** at **n = 4,194,303 = 4·2²⁰−1** the first 2²⁰-aligned checkpoint
after start jumps 4,194,304 → 5,242,880. Every head with **D ≤ 5,242,880**
goes *sub-grid*: its new basin members have **no probe point before death**
→ no walker-table merge, no cert hit → they all die **'d'**, each walking
solo to its funnel. Effects, all visible in the table:
- 'd' share jumped from 0.3–8.6% (e1–e15, trending down to ~1% by e13–e15) to
  **12.8 / 22.3 / 19.0 / 17.5%** (e16–e19); block cost rose from the 0.605×10¹⁰ cheap peak (e15) back to
  5.1–5.7×10¹⁰ steps (the ~10⁵ extra pre-probe steps per walk, plus full-cost
  solo marches through mid-shallow basins).
- The **5061761 mega-funnel is now sub-grid** (e.g. 7,290 solo 'd' walks in
  e17) and simultaneously fades as its basin closes at n = 5,061,760:
  14,365 walks/block (e1) → 5,333 (e19).
- Deep basins unaffected: giant share stable 48.5→56.5% (53–57% after e2);
  **7466441 overtook 5061761 permanently in e16** (13.0→26.1%, 15631 walks in
  e19 — now the clear #2).
- Merge histogram (104,931 events): **4194304: 87,716 (83.6%), 5242880:
  17,091 (16.3%)**, tail 124 (7340032: 26; 6291456, 9437184, 11534336, and
  the giant junction 303038464: 19 each — exactly one new independent trunk
  entry per block; 16777216, 10485760: 11 each). F4's front-loaded
  coalescence holds; the first-checkpoint grid simply moved one period up.

## Head hierarchy across the march

| block | 1449322159 | 5061761 | 7466441 | top-3 | biggest tail head |
|---|---|---|---|---|---|
| e1 | 48.5% | 23.9% | 19.0% | 91.4% | 4021505: 3.0% |
| e2 | 52.5% | 24.8% | 15.9% | 93.2% | 4021505 |
| e3 | 60.6% | 21.8% | 13.0% | 95.4% | 4021505 |
| e4 | 57.7% | 17.2% | 20.4% | 95.3% | 4021505 |
| e5 | 56.7% | 19.2% | 20.2% | 96.0% | 4021505 |
| e6 | 56.5% | 21.7% | 17.6% | 95.9% | 4021505 |
| e7 | 58.6% | 21.9% | 16.4% | 96.8% | 4021505 |
| e8 | 57.2% | 21.7% | 18.0% | 96.8% | 4021505 |
| e9 | 57.7% | 22.0% | 15.7% | 95.5% | 4021505 |
| e10 | 56.8% | 25.3% | 14.4% | 96.5% | 5079041 born (6 walks) |
| e11 | 56.2% | 24.0% | 15.6% | 95.8% | 5079041: 302 |
| e12 | 54.2% | 20.7% | 19.0% | 93.9% | 5079041: 964 |
| e13 | 56.3% | 18.8% | 19.2% | 94.3% | 5079041: 853 |
| e14 | 57.1% | 16.9% | 19.4% | 93.4% | 5079041: 1797 |
| e15 | 52.7% | 14.8% | 20.7% | 88.2% | 5079041: 3676 |
| e16 | 53.3% | 13.1% | 20.5% | 87.0% | 5079041: 3360 |
| e17 | 55.0% | 12.2% | 22.6% | 89.8% | 5079041: 3091 |
| e18 | 56.1% | 9.2% | 24.9% | 90.2% | 5079041: 3760 |
| e19 | 56.5% | 8.9% | 26.1% | 91.4% | 5079041: 3815 |

- 557 heads birthed this march (shallow churn, all D ∈ [3.27, 5.08]×10⁶ —
  just-above-n heads, together 52,934 walks = 4.6%, all ≪ record); biggest
  birth: **D = 5,079,041** (first appears e10 with 6 walks,
  21,624 total, ~6% of walks by e19, sub-grid since e16). Others: 4322145
  (7,489), 4444479 (4,458), 4292039 (2,919), 4373889 (2,638), 4047745 (1,989).
- Per-block head count 30–49 (vs 20–24 at 3.2×10⁶): the shadow zone forces
  more distinct shallow funnels to be walked solo (each is a fresh 'd' root).
- March totals: giant 636,058 (55.8%), 7466441 215,282 (18.9%), 5061761
  214,808 (18.9%) — top-3 absorb 93.5% of 1,140,000 starts. The deep-funnel
  architecture remains stable across 1.14×10⁶ of n; the shallow tail keeps
  re-mixing on a 2²⁰ lattice.

## Cert-table growth + reuse economics

- Chain `cert_march.txt`: 8,282 → 34,499 lines / **1,680 → 1,728 distinct**
  states (+48; ≈1–8 new trunk-entry states per block on the converged giant
  spine — each block's ~1,379-line emission is ~99.9% already-certified
  states, exactly the session-020 convergence picture).
- Instant-'c' reuse: 270,213/1,140,000 = **23.7% overall**, rising 22.3% (e1)
  → **34.1%** (e19) — within a 60K block the chunk-1 giant emission serves
  chunks 2–6 from memory; the 60K block shape amortizes the certless-chunk-1
  tax over 6 chunks (vs 2 in session-020's 20K blocks).
- Walker table peaked at 65,812 entries (e16) ≪ 5.24M insert limit; cert-table
  conflicts: 0 (a conflict FATALs — none in 19 loads of the growing chain).

## Frontier verdict

- **Contiguous all-n certified frontier: n = 4,400,200** (was 3,260,200
  pushed; the wiped session's 3,740,200 is reproduced by e1–e8 and extended
  by e9–e19). Total this session: 1,140,000 consecutive n in 19 blocks, all
  terminating. Next unverified n: 4,400,201.
- Cost model: the shadow zone [4.19×10⁶, 5.06×10⁶] costs ~5.1–5.7×10¹⁰
  steps per 60K block (~108 s solo; shadow waves took 99–109 s wall for
  120K). After n = 5,061,760 the 5061761 basin closes and blocks should
  cheapen until the next shadow boundary **n = 5,242,879** (first checkpoint
  6,291,456: heads D ≤ 6,291,456 go dark; 7466441 survives to n = 7,466,440;
  the giant forever). At the measured 2-job pace: 4.5×10⁶ ≈ 1 wave (~2 min),
  5×10⁶ ≈ 5 waves (~6–9 min), 6×10⁶ ≈ 13 waves (~15–20 min).
- Standing watch: any D > 1,449,322,159 or any unresolved-at-cap walk is the
  nontermination-adjacent alarm — none seen in **1,243,969 total death
  records** (103,969 prior + 1,140,000 this session).
