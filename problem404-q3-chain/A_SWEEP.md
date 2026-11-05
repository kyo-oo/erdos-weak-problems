# A-SWEEP — exact g(a,2) for every even a ≤ 60 (Erdős #404, p=2)

**Task 1-a · Date: 2026-11-03 · Dir: `problem404-q3-chain/` · Status: COMPLETE — all 17 target values exact, two-sided certified. No ALIVE candidates.**

$$g(a,2) \;=\; \max_{B \subseteq \{a+1,a+2,\dots\} \text{ finite}} v_2\!\Big(1 + \sum_{i \in B} \tfrac{i!}{a!}\Big)$$

Engine: `class_dp.c` (sound scheduled-precision class-DP, GMP bignums — see DEEP_PROBES.md).
Every run: `nice -n 10`, `--mem 1500`, single-threaded, one at a time, `--witness`.
**All 17 targets died at the starting L=300** (max new g = 27 ≪ 300), so every death is a genuine
two-sided certificate (L ≥ g+1 with capped=0), each confirmed by L=600 stability runs.
Witness verification: in-engine GMP (all 34 logs `WITNESS = VERIFIED`) **and** out-of-engine
pure Python `verify_witness.py` — **34/34 PASS**. Total sweep cost: 34 runs, ≤ 0.02 s each, peak RSS 2 MB.

## 1. COMPLETE exact g-table — every even a ≤ 60 (30 values)

| a | g(a,2) | first unreachable | source | a | g(a,2) | first unreachable | source |
|---|--------|-------------------|--------|---|--------|-------------------|--------|
| 2 | **253** | 254 | known | 32 | 6 | 7 | **new** |
| 4 | 3 | 4 | known | 34 | **18412** | 18413 | known |
| 6 | 129 | 130 | known | 36 | 3 | 4 | **new** |
| 8 | 6 | 7 | known | 38 | 793 | 794 | known |
| 10 | 6 | 7 | known | 40 | 7 | 8 | **new** |
| 12 | 3 | 4 | known | 42 | 6 | 7 | **new** |
| 14 | **1522** | 1523 | known | 44 | 3 | 4 | **new** |
| 16 | 533 | 534 | known | 46 | 27 | 28 | **new** |
| 18 | 45 | 46 | known | 48 | 6 | 7 | **new** |
| 20 | 3 | 4 | **new** | 50 | 14 | 15 | **new** |
| 22 | 11 | 12 | **new** | 52 | 3 | 4 | **new** |
| 24 | 39 | 40 | known | 54 | 12 | 13 | **new** |
| 26 | 6 | 7 | **new** | 56 | 7 | 8 | **new** |
| 28 | 3 | 4 | **new** | 58 | 6 | 7 | **new** |
| 30 | 100 | 101 | known | 60 | 3 | 4 | **new** |

**ALIVE candidates: NONE.** Every even a ≤ 60 now has an exact finite g(a,2).

## 2. Per-target detail (17 new values; death L=300, stability L=600, both witness-verified)

| a | g | first unreach. | L death→stab | witness \|B\| (Bmin–Bmax) | py-verify | peak states | RSS | time |
|----|----|---------------|--------------|---------------------------|-----------|-------------|-----|------|
| 20 | 3 | 4 | 300→600 | 2 (21–23) | PASS | 4 | 2 MB | <0.01 s |
| 22 | 11 | 12 | 300→600 | 4 (23–31) | PASS | 32 | 2 MB | <0.01 s |
| 26 | 6 | 7 | 300→600 | 2 (27–29) | PASS | 8 | 2 MB | <0.01 s |
| 28 | 3 | 4 | 300→600 | 2 (29–31) | PASS | 4 | 2 MB | <0.01 s |
| 32 | 6 | 7 | 300→600 | 3 (33–37) | PASS | 8 | 2 MB | <0.01 s |
| 36 | 3 | 4 | 300→600 | 2 (37–39) | PASS | 4 | 2 MB | <0.01 s |
| 40 | 7 | 8 | 300→600 | 4 (41–46) | PASS | 8 | 2 MB | <0.01 s |
| 42 | 6 | 7 | 300→600 | 2 (43–45) | PASS | 8 | 2 MB | <0.01 s |
| 44 | 3 | 4 | 300→600 | 2 (45–47) | PASS | 4 | 2 MB | <0.01 s |
| 46 | 27 | 28 | 300→600 | 9 (47–68) | PASS | 64 | 2 MB | <0.01 s |
| 48 | 6 | 7 | 300→600 | 3 (49–52) | PASS | 8 | 2 MB | <0.01 s |
| 50 | 14 | 15 | 300→600 | 5 (51–63) | PASS | 24 | 2 MB | <0.01 s |
| 52 | 3 | 4 | 300→600 | 2 (53–55) | PASS | 4 | 2 MB | <0.01 s |
| 54 | 12 | 13 | 300→600 | 4 (55–62) | PASS | 32 | 2 MB | <0.01 s |
| 56 | 7 | 8 | 300→600 | 4 (57–62) | PASS | 8 | 2 MB | <0.01 s |
| 58 | 6 | 7 | 300→600 | 2 (59–61) | PASS | 8 | 2 MB | <0.01 s |
| 60 | 3 | 4 | 300→600 | 2 (61–63) | PASS | 4 | 2 MB | <0.01 s |

Logs: `logs/c_sweep_a{A}_L{300,600}.log` (+`.err`), full-res per-class death logs `logs/c_sweep_a{A}_L300_full.log`
(85 sweep files total). Stability runs reproduce g / first-unreachable / witness identically at L=600 (2× death L).

**Two largest g values (all even a ≤ 60): g(34) = 18412, then g(14) = 1522** (both prior-session, multi-wall crossers).
Largest new: g(46) = 27.

## 3. Structure observations

### 3.1 The (a+2)³ identity — a universal lower bound, tight on two full residue classes

$$1 + \tfrac{(a+1)!}{a!} + \tfrac{(a+3)!}{a!} \;=\; 1 + (a+1) + (a+1)(a+2)(a+3) \;=\; (a+2)^3$$

So **B = {a+1, a+3} always achieves level 3·v₂(a+2)** — an algebraic lower bound g(a,2) ≥ 3·v₂(a+2), and the engine's
exact values show it is **TIGHT** on two complete residue classes:

- **a ≡ 4 (mod 8) ⇒ g(a,2) = 3**, for all 8 points {4,12,20,28,36,44,52,60}; witness = exactly {a+1,a+3}; state trajectory identical in all 8 (states 2,4,2,1 → empty at class 4).
- **a ≡ 10 (mod 16) ⇒ g(a,2) = 6**, for all 4 points {10,26,42,58}; witness = exactly {a+1,a+3}.

These two families (12 of the 30 values) are completely solved by the identity: the DP certificates confirm nothing beats the 2-coin cube trick. Everywhere else g > 3·v₂(a+2) (e.g. a=46: bound 12, actual 27; a=34: bound 6, actual 18412).

### 3.2 Residue-class map of the whole table (mod 16)

| a mod 16 | g values | behavior |
|----------|----------|----------|
| 4, 12 | 3, 3, 3, 3 / 3, 3, 3, 3 | **flat: g = 3** (= bound, tight) |
| 10 | 6, 6, 6, 6 | **flat: g = 6** (= bound, tight) |
| 2 | 253, 45, 18412, 14 | **monster class** — all > bound 6; 1300× spread, no monotonicity |
| 6 | 129, 11, 793, 12 | split by mod 32: a≡6 (mod 32) → 129, 793 (≥100); a≡22 (mod 32) → 11, 12 (≈3·v₂(a+2)+2..3) |
| 14 | 1522, 100, 27 | spread 56×; the deepest value g(14)=1522 lives here |
| 0 | 533, 6, 6 | a=16 is the ONLY g ≥ 100 at a ≡ 0 (mod 4) |
| 8 | 6, 39, 7, 7 | for a ≥ 32: a≡0 (mod 16)→6, a≡8 (mod 16)→7; small anomalies at 8, 24 |

**Every g ≥ 100 occurs at a ≡ 2 (mod 4) except g(16) = 533.** The deep ladders (a = 2, 6, 14, 30, 34, 38) all have a/2 odd.

### 3.3 Death profiles — one universal pattern

- **Geometric bleed-out at ratio ≈ ½ per class.** The live set halves every class through the death tail and hits 0 exactly at class g+1 = first unreachable. Examples (states per class, tail): a=54: 32→16→8→4→1→1→0 (classes 7–13); a=50: 24→12→4→2→2→0; a=22: 16→10→3→1→0; a=20: 2→4→2→1→0. Same signature as the deep deaths a=14 (508→252→111→53→25→14→5→1→0) and a=34 (at 18412): **the tail is scale-invariant — the a=34 monster died exactly like a=20, just 4 decades later.**
- **final_t_hist is empty at every death** (final snapshot 0 states). The dyadic-ladder hist (256:128:…:1) appears only in ALIVE (L-capped) runs — a clean death/alive discriminator.
- **No new wall-crossers.** All 17 targets died at the starting L=300; deepest new ladder is a=46 (g=27). The multi-wall crossings of a=14 (died below 2048) and a=34 (crossed 2048–16384, died 18412) have no analog ≤ 60 beyond a=34 itself.
- **Mild "second wind" anomaly at a=46:** late coin pairs at classes 21–22 re-inflate the live set (4→12→24 states) after it had bled to 4, before halving resumes to 0 at class 28 — a miniature echo of a=34's wall-jump behavior (its final wall-jump was +3 over the top coin class).
- **Witness coins end well below g:** the top witness coin class vs g overshoot is +2…+5 for the new values (a=22: top coin class 7, g=11; a=50: class 10, g=14; a=54: class 7, g=12) — the last rungs of every ladder are built purely by combination of small coins, not by fresh large ones (same as a=14: +8; a=34: +3).

### 3.4 Consequence for the campaign

With zero ALIVE candidates left ≤ 60 and the two surviving monsters already killed (DEEP_PROBES.md), **every even a ≤ 60 has exact finite g(a,2)**. The (a+2)³ identity plus the two flat residue classes (g = 3·v₂(a+2) for a ≡ 4 mod 8 and a ≡ 10 mod 16, certified 12/12) is ready-made structure-theorem material: the natural conjecture is that the flat classes extend to all a ≡ 4 (mod 8) / ≡ 10 (mod 16), and that all monsters live in a ≡ 2 (mod 4).

## 4. Files

- `sweep_one.sh` — adaptive-L driver (300→600→1200→…→32768, binary by L, `--witness`, timeout guard).
- `post.sh` — per-a post-processing: witness verify (pure Python), stability run, full-res death log, structure summary.
- `verify_from_log.sh` — extracts WITNESS/WITNESS_LIST from a log and runs `verify_witness.py`.
- `logs/c_sweep_a{A}_L{300,600}.log/.err`, `logs/c_sweep_a{A}_L300_full.log` — 85 files, all 34 runs `WITNESS = VERIFIED` in-engine, 34/34 pure-Python PASS, `g_interval_crosscheck` consistent 34/34.

**Constraints honored:** `nice -n 10` and `--mem 1500` on every run; single-threaded; one run at a time; peak RSS 2 MB; no Lean files touched; nothing pushed.
