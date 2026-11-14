# W64-B STATUS — Erdős #708 (Task W64-B, worktree w63-d1-p708, branch w63-d1-p708)

## THE RESULT: KERNEL62 GREEN ON CI — THE g(4) MASTER IS CERTIFIED

**Run 43602748433** (branch w63-d1-p708, HEAD 064806a4, started 14:02:16Z):
- **kernel-c: SUCCESS (completed 14:22:20Z, job 132470819408)** — kernel62 (#708) GREEN.
- kernel-a: SUCCESS (14:12:56Z). kernel-b: see run verdict below (all recent runs green).
- The kernel62 lean run elaborated ALL of Erdos708.lean (60151 lines, witness
  table + 114 chunk decides) in ~4.5 min at the 4M default heartbeat —
  vs the 60-min runner death of run 43589088597. NO-OOM structure PROVEN.

### CI receipts (kernel-c log, saved verbatim: kernel62-green-receipt-43602748433.log)
- `'E708.e708_g4_box_exact' depends on axioms: [propext, Classical.choice, Quot.sound]`
- `'E708.e708_g4_box_corpus' depends on axioms: [propext, Classical.choice, Quot.sound]`
- `'E708.e708_exact_2_3_4_5' depends on axioms: [propext, Classical.choice, Quot.sound]`
- `'E708.erdos708_g4_master' depends on axioms: [propext, Classical.choice, Quot.sound]`
- `'E708.erdos708_g4_box_max' depends on axioms: [propext, Classical.choice, Quot.sound]`
- `"E708_PRODUCT_DIVISIBILITY_GREEN"` and `"E708_G4_MASTER_GREEN"` receipts printed
- Step echo: `KERNEL62_GREEN=1`
- Only the three standard foundational axioms — zero sorryAx, zero admits.
- kernel62's guard now greps the five-name master axis directly (kills.yml).

## THE LANDED THEOREMS (Erdos708.lean, dual-direction g(4) master)

**`erdos708_g4_master`** (line 60026) — the box master, BOTH directions:
- (i) CONSTRUCTION: ∀ A ∈ box708 (all 1365 four-element A ⊆ [2,16]), ∀ t = 1..40,
  ∃ B, sub708 B (win708 t (maxA A)) ∧ B.length = 4 ∧ prod708 A ∣ prod708 B
  (every instance admits an EXACTLY-4 covering battery);
- (ii) EXCLUSION (g(4) ≥ 4): ∃ A ∈ box708, ∃ t = 1..40 (witness **A = [2,3,4,5],
  t = 24**, window {25,…,29}), ∀ B ⊆ window with B.length ≤ 3: ¬(prod A ∣ prod B)
  — no battery of 3 or fewer cells covers;
- (iii) the exact row: minB [2,3,4,5] 24 = 4 (`e708_exact_2_3_4_5`, decide-exhibited
  witness {25,26,27,28}: 491400 = 4095 · 120 = prod cover of 2·3·4·5 = 120).
- W60-T2c original forcing witness also live: `erdos708_g4_lower` (line 1387):
  A = [6,10,14,15] at t = 1 — no ≤3 cover, a 4-cover exists (e708_exact_6_10_14_15).
**`erdos708_g4_box_max`** (line 60050): the box-max of instance-minima = EXACTLY 4
(∀ (A,t) minB ≤ 4 ∧ ∃ (A,t) minB = 4) — the case-value g(4) = 4 on the certified box.
**`e708_g4_box_exact`** (line 59925): the 54600-instance aggregate statement, VERBATIM,
now proven from the explicit witness table (`wrows708` = 114 chunks `wchunk708_0..113`,
each ≤ 480 instances, chunk-decided at 4M; alignment cert `e708_wrows_dom`;
assembly `e708_g4_rows_exact`; bridge via List.all_eq_true + e708_exact_enum_complete).

## ROOT CAUSE CHAIN (the three failures, all diagnosed, all dead)
1. **43585957179 (5536ed9):** deterministic heartbeat timeout of the 54600-instance
   aggregate decide at the 4M default — clean failure, the guard-rail worked.
2. **43589088597 (ae020570):** the 32M heartbeat override REMOVED the guard-rail;
   the elaborator ground ~60 min and the HOSTED RUNNER DIED ("lost communication"
   — the only annotation; OOM/starvation mode, 70-min job vs the 13.6-min healthy
   baseline). NOT a Lean error. Fix = the NO-OOM witness-table restructure (9fc45c3):
   114 bounded chunk decides at the 480-instance discipline, 32M override deleted.
3. **43600972276 (9fc45c3):** the restructure's math was ALREADY GREEN (every #708
   theorem elaborated; kernel62 lean ~4.5 min) but ONE parse error killed the step:
   Erdos708.lean:1595:69 `unexpected token '/--'; expected 'lemma'` — a stacked
   doc-comment (post-mortem `/-- … -/` immediately followed by `w708OK4`'s own
   `/--`). Fix = demote the post-mortem to a plain `/-` comment (064806a) — one
   character, zero math drift. Full-file doc-attachment scan: 0 remaining defects.
4. **43602748433 (064806a): GREEN.** kernel-c SUCCESS; kernel62 receipts above.

## DUAL-METHOD VERIFICATION (local Python, banked in 9fc45c3)
- gen708_witab.py: coverExact DFS mirror (Lean def transcribed literally) hunted
  all 54600 witnesses — 0 failures; every emitted row re-checked (subset-of-window
  + length 4 + ascent + gmpy2 exact divisibility): 54600/54600 GREEN
  (g4_witgen_out.txt). Parse-back self-check of the FILE's own data: 0 failures;
  A-column equals box708's exact order. Witness checksum 5500392 (determinism).
- CI-side: kernel-decided alignment cert `e708_wrows_dom : wrows708.map Prod.fst = box708`.

## THE #411 SYNC (mandatory, done in 9fc45c3)
`git checkout w63-a1-p411 -- .github/workflows/kills.yml problem411-iterated-totient/Erdos411.lean`
executed (the FULLY GREEN state: run 43598294749 + double-green 43599564453);
kernel61's Erdos411-namespace grep fix inherited; kernel62's guard extended with
the g4-master receipts (superset diff, verified intentional).

## HONEST RESIDUE + NEXT-ROUND PATH
- The master is BOX-CONDITIONAL: {four-element A ⊆ [2,16]} × {t = 1..40} certified
  (54600 instances). The UNCONDITIONAL g(4) = 4 over all four-element A ⊆ [2,∞) and
  all windows remains open — the census gives NO forcing-5 evidence on
  [2,25] × t ≤ 40 ∪ [2,16] × t ≤ 300, so g(4) = 5 is nowhere in sight; the next
  rounds' war is widening the box (A ⊆ [2,25], t ≤ 300 census rows already computed
  in g4_census2_ckpt.json / g4_widet_ckpt.json) or finding the forcing structure.
- ErSu59 lane: g(2)=2, g(3)=4 known; g(4) ≥ 4 now CI-certified (this kernel);
  the g(4) ≤ 4 side holds on the box (construction (i)); unboxed upper bound open.
- Next round: widen the witness table to [2,25] × t ≤ 40 with the same chunk
  discipline (the generator + dual-method verifier are banked and reusable).
