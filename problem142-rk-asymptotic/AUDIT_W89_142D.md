# AUDIT W89-142D — adversarial proof audit of kernel 142DM-D (THEOREM V-GEN)

- **Target:** `problem142-rk-asymptotic/DM142_Proof_D.lean` (632 lines), tip `d290274`, branch `campaign`, worktree clean for the file.
- **Claim under audit:** DM142D.v_gen / v_gen_witness / aff_k / v_gen_board, CI-green on job `kernel-dm-w85`, run 45497202986 (commit 8a96fa5).
- **Auditor lane:** W89-A142. Research + audit only — no proof code written, no lake/lean run, no push.

## VERDICT: **PASS** — the green is REAL

Zero sorry, zero native_decide, zero custom axioms; the four headline theorems
depend on exactly `[propext, Classical.choice, Quot.sound]` (pulled CI log,
run 45497202986, lines 553–556 of `problem406-ternary-powers/CI_LOGS_W89/kernel-dm-w85.log`);
statements match the official `r` and the UPPER_STACK.md paper exactly; the
math is sound at the boundary and was re-verified independently in this audit
(fresh r_3 brute force + the campaign's W85 adversarial engine re-run).
No defects found that touch soundness. Two informational notes, one LOW
tooling note (all listed in §7).

## 1. Statement fidelity (side-by-side)

| Item | Official / paper side | Kernel side (DM142_Proof_D.lean) | Match |
|---|---|---|---|
| r definition | `noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard` — DM_142.lean:32 (google-deepmind/formal-conjectures @ 2207c54d); maxCard = `sSup {Finset.card S | S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k}` (vendored FC/Combinatorics/AP/Basic.lean:223–224) | L46: `noncomputable abbrev r : ℕ → ℕ → ℕ := Set.IsAPOfLengthFree.maxCard` — identical | ✓ exact |
| r semantics | "largest possible size of a subset of {1,…,N} that does not contain any non-trivial k-term arithmetic progression" (challenge.json `statement_verbatim`; DM_142.lean docstrings; conventions: k-AP = a,…,a+(k−1)d, d ≥ 1) | The official `IsAPOfLengthWith` set-builder forces `ENat.card s = k`, so d = 0 is impossible for k ≥ 2 — non-triviality is definitional; used as-is throughout | ✓ exact |
| V-GEN | UPPER_STACK.md:41–44: ∀ k ≥ 3, m ≥ 2, N ≥ 16m², every k-AP-free A ⊆ [1,N]: `|A| ≤ rho_m·N + N/(2m)`, rho_m = r_k(m)/m | L568–569 v_gen: `(hk : 3 ≤ k) (hm : 2 ≤ m) (hN : 16*m*m ≤ N) : 2*m*(r k N) ≤ (2*(r k m)+1)*N`; witness form L243–247. Multiply the paper by 2m: `2m|A| ≤ 2·r_k(m)·N + N` — the Lean all-integer form, identical | ✓ exact |
| AFF-K | UPPER_STACK.md:31–39: every homothetic copy c(a,d) = a+d{0..m−1} hosts ≤ r_k(m) points of any k-AP-free set | L109–112 aff_k: for k ≥ 2, d ≥ 1: `|(range m).filter (fun j => a + j*d ∈ S)| ≤ maxCard k m`. `hd : 1 ≤ d` is genuinely needed (d = 0 collapses the copy) and present; used 3× via `Nat.eq_of_mul_eq_mul_right hd` | ✓ exact |
| Board | paper instance k=3, m=8; 16·8² = 1024 | L615–616 v_gen_board: `(hN : 1024 ≤ N) : 16 * (r 3 N) ≤ (2 * (r 3 8) + 1) * N` | ✓ exact |
| Open core | erdos_142 asymptotic formula = research open | claimed by no one; DM142_Official.lean:56–62 and OFFICIAL_POSITION_W82.md record it honestly as OPEN | ✓ honest |

Vendored-FC byte check: local diff of `FC/Combinatorics/AP/Basic.lean` vs
`dm-fc/FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` differs ONLY by
the documented import replacement (4 `Mathlib.*` imports + blank line); the
definitions region is identical. The official `r` is carried verbatim.

## 2. Zero-sorry scan

- Word-boundary rg for `sorry|admit|native_decide` on DM142_Proof_D.lean: **0 hits** (L38 is the doc-comment that asserts it).
- `axiom` declarations in the file: **0** (only `#print axioms` commands, L627–630). `axiom`/`unsafe`/`implemented_by` declarations in the three imported non-Mathlib files (FC/Combinatorics/AP/Basic.lean, Arsenal/ErdosTernary2/Basic.lean, Arsenal/CardinalWorlds.lean): **0** — no custom axiom can enter through imports.
- Global W89 sorryAx sweep (`problem406-ternary-powers/CI_LOGS_W89/sorryax_sweep_45497202986.txt`): kernel-dm-w85 hits=6, all guard-command echoes, **REAL=0**; across all 33 green jobs: **0 REAL**.
- **Greenness is current at tip:** `git diff 8a96fa5 d290274` touches ONLY `WORKLOG_S085.md` (+35 record lines). DM142_Proof_D.lean and .github/workflows/kills.yml are byte-identical between the CI-green commit and tip; worktree clean.
- Pulled log `kernel-dm-w85.log`: `lake env lean problem142-rk-asymptotic/DM142_Proof_D.lean` present (L470), zero `error[:(]` lines, only two benign `push_neg` deprecation warnings (L135, L484), both `DM142D_VGEN_GREEN` markers and `KERNEL_142DM_D_GREEN=1` present, and the four axiom lines exactly `[propext, Classical.choice, Quot.sound]`.

## 3. Critical-path composition map (line numbers)

```
L46   r (official abbrev, verbatim)
§0 house machinery:
  L51    nsmul_nat            (i•d = i*d — the official builder's smul)
  L54    coe_sub              [DEAD in this file — see §7-N2]
  L59    apFree_subset        [DEAD in this file — see §7-N2]
  L67-74 maxCard_ge_of_witness (sSup membership transfer: le_csSup + BddAbove via card_mono)
  L77-84 sum_const_nat        (DIY: ∑_∈Q c = Q.card*c, Finset.induction_on)
  L87-98 card_bUnion_le'      (DIY: |⋃F| ≤ ∑|F|, Finset.induction_on)
§1 AFF-K (L109–233), the copy cap:
  L114   T := (range m).filter (a + j*d ∈ S)          — index set of the copy
  L115   T' := T.image (·+1); L117-124 T' ⊆ Icc 1 m
  L126   T' is officially k-AP-free:
    L133-151  d' ≥ 1 (else u singleton, encard 1 ≠ k ≥ 2)
    L153-161  a' ≥ 1 (a' ∈ u ⊆ T' ⊆ [1,m])
    L163-166  A := a+(a'−1)d, D := d'·d, W := image of range k
    L168-189  W ⊆ S (element chain through T'-membership)
    L191-225  W is an official k-AP: card W = k (injectivity, d ≥ 1 AND d' ≥ 1,
              L196-202) + set-equality ↑W = {A+n•D | n<k} (L204-225)
    L226      fed to hfree (goal is literally k ≤ 1 — the official def's shape)
  L228-233 witness transfer: |T| = |T'| ≤ maxCard k m
§2–§4 v_gen_witness (L243–555), the double count:
  L255   D0 := N / (4*m*(m-1))
  L257-278 F1 4m(m−1) ≤ N; F2 D0 ≥ 1 (Nat.div_pos); F3 4m(m−1)·D0 ≤ N
           (Nat.mul_div_le); F4 (m−1)D0 ≤ N
  L280-281 bandS (two-sided margin (m−1)D0); L283-285 Q (copy indices
           {(d,a)}); L288-291 P (incidence triples (x,(d,j)))
  L308-319 |Q| ≤ D0·N (product card + filter_subset)
  L321-338 every p ∈ P lands its copy index (p.2.1, p.1 − j·d) in Q
  L340-377 LOWER: bandS ×ˢ ([1,D0]×[0,m)) ⊆ P  ⟹ |bandS|·(D0·m) ≤ |P|
  L379-475 UPPER: P = ⋃_{q∈Q} fiber_q (L381-391);
           each fiber injects into T_q via p ↦ j (L433-458) and
           |T_q| ≤ r k m by aff_k (L401-402)  ⟹  |P| ≤ (r k m)·|Q|
  L477-493 CANCEL: |bandS|·m ≤ (r k m)·N (strict×D0>0 contrapositive, no division)
  L495-536 FRINGE: S = bandS ∪ off-band; off-band ⊆ Icc 1 ((m−1)D0) ∪
           Icc (N−(m−1)D0+1) N; |S| ≤ |bandS| + 2(m−1)D0
  L538-555 FINAL (all-integer): 2m|S| ≤ 2(bandS·m) + 4m(m−1)D0
           ≤ 2·(r k m)·N + N = (2(r k m)+1)·N
§5 v_gen (L568–611), the sup transfer:
  L570-576 N ≥ 64 ≥ 1; L577-604 csSup_le with nonempty witness {1}
           (singleton is k-AP-free, L586-600); every witness card:
           2m·S.card ≤ B ⟹ S.card ≤ B/(2m) (Nat.le_div_iff_mul_le)
  L605-611 2m·maxCard ≤ 2m·(B/(2m)) ≤ B (Nat.mul_div_le — floor slack)
Board (L615–623): v_gen 3 8 N + 16·8·8 = 1024 + 2·8 = 16 rewrite.
```

**No circularity:** the dependency chain is strictly
`maxCard_ge_of_witness → aff_k → v_gen_witness → v_gen → v_gen_board`.
v_gen_witness never mentions v_gen; aff_k never mentions the double count.
**No hypothesis strengthening:** hypotheses are exactly the paper's (k ≥ 3,
m ≥ 2, N ≥ 16m²; aff_k: k ≥ 2, d ≥ 1 — the d ≥ 1 is necessary and present).
**No definition drift:** every AP-freeness hypothesis has the official shape
`(↑S : Set ℕ).IsAPOfLengthFree ((k : ℕ) : ENat)`; the maxCard call sites use
the official signature.
**L86 / L90 / L91 traps:** zero `decide` occurrences (kernel or otherwise),
zero `==`/BEq/`native` occurrences — the file is Prop-level `=`/`≤` throughout
(classical, omega, ring, explicit calc). No law violations.

## 4. Math spot-checks (independent)

1. **r_3 table (fresh DFS, this audit):** r_3(3)=2, r_3(4)=3, r_3(8)=4,
   r_3(9)=5, r_3(12)=6, r_3(16)=8, r_3(20)=9 — matches OEIS A003002, the
   kernel-142a certified table, and the campaign B&B (three independent codes).
2. **Board constant:** r_3(8) = 4, so v_gen_board is `16·r_3(N) ≤ 9·N` —
   strictly STRONGER than the "17·N" sometimes quoted (17 = 2m+1 is the
   trivial r_k(m) ≤ m corollary). The Lean statement itself (L616) is the
   sharp symbolic form `(2*(r 3 8)+1)*N` — no inflation anywhere.
3. **Boundary arithmetic (m=8, N=1024, recomputed by hand and by script):**
   D0 = ⌊1024/224⌋ = 4; band = [29, 996]; ≥ m·D0 = 32 incidences per band
   point; #copies = Σ_{d≤4}(1024−7d) = 4026 ≤ D0·N = 4096; fringe 2·7·4 = 56;
   4m(m−1)D0 = 896 ≤ 1024 ⟹ |S| ≤ 512+56 = 568 and 16·568 = 9088 ≤ 9·1024 =
   9216. Chain closes with slack 128. Matches engine receipt
   `VGEN-band-m8-N1024` (#C0=4026, min_nu=32) and this audit's re-run of
   `audit_w85_adversarial.py` Part B/C+D+E (all OK, including the k=4, m=8,
   N=1024 planted-set double count).
4. **AFF-K relaxed-shape brute force:** the Lean aff_k does NOT require the
   copy inside [1,N] — the campaign's adversarial engine brute-forced exactly
   this relaxed variant (all 2^N AP-free subsets, N ≤ 13/14, all copies,
   2,412,020 checks): **0 failures**. The relaxed statement is sound (only
   S-membership of copy points matters).
5. **Plausibility of the sup:** v_gen at the board gives r_3(1024) ≤ 576 —
   far above every known lower bound (campaign witness r_3(1024) ≥ 10 from
   DM142B; literature ~10²) and below the trivial r_3(N) ≤ N − ⌊N/3⌋ = 683 —
   a genuine (if modest) improvement, exactly as the paper's crossover section
   honestly states (V-GEN loses to BLOCK at current stones; it is the
   conversion engine for future stones).
6. **Paper–Lean equivalence:** UPPER_STACK THEOREM V-GEN `|A| ≤ rho_m·N +
   N/(2m)` times 2m is `2m|A| ≤ 2·r_k(m)·N + N`, with the paper's
   2(m−1)D0 ≤ N/(2m) instantiated by the Lean's F3 (4m(m−1)D0 ≤ N) — the
   Lean all-integer assembly is the faithful undivided form. Constants,
   hypotheses and the D0 definition all match.

## 5. Supporting kernels and CI gates (.github/workflows/kills.yml)

| Job (line) | File | Gates (marker) | Theorems |
|---|---|---|---|
| kernel-dm-w82 → step "Kernel 142DM-A" (:152) | DM142_Proof_A.lean | DM142A_UPPER_GREEN | r_mono (M-1 ladder), r_mono_unrestricted_false (honesty counterexample), apFree_of_pairscan, stone witnesses r3_61_ge…r7_45_ge, dm142a_board |
| kernel-dm-w82 → step "Kernel 142DM-B" (:165) | DM142_Proof_B.lean | DM142B_LOWER_GREEN | 19 decide-certified witness stones over the official r (r3_216_ge … r5_1000_ge, incl. r3_1024_ge : 10 ≤ r 3 1024, w1024_not_cantor), dm142b_board |
| kernel-dm-w84 → step "Kernel 142DM-C" (:190) | DM142_Proof_C.lean | DM142C_UGEN0_GREEN | u_gen_zero (r k N ≤ N − N/k), u_gen_zero_tight (r k k = k−1), window_bound/union_bound/core_bound, r_kk_ge, dm142c_board |
| kernel-dm-w85 → step "Kernel 142DM-D" (:249) | **DM142_Proof_D.lean** | DM142D_VGEN_GREEN | **aff_k, v_gen_witness, v_gen, v_gen_board (this audit's target)** |
| kernel-142k (:2321) | problem142-ap-free/Erdos142.lean | E142_*_GREEN | E142.t3free, cantor_lower, block_upper, r3_upper, k2_edge, r3_exact_small, erdos142_board |
| kernel-142d (:2349) | engine142/doubter (python+z3) | E142_DOUBTER/CROSSAUDIT | mirror battery C1–C5 + cross-audit of the ternary kernel |
| kernel-142a (:2374) | engine142/audit_w69b.py (python+z3) | AUDIT_W69B_GREEN | fresh re-derivation of the exact r_3 table N=1..30, Cantor census, block-bound torture |
| kernel-142cmp (:2451) | comparator (python+z3, no Lean) | comparator lane | challenge.json vs solution.json direct verification |

Every Lean gate uses the same hard guard stack: `! grep -E 'error[:(]|sorryAx|
unknown identifier|unsolved goals|declaration uses .sorry.'` + positive greps
for the `#eval` marker and the `#print axioms` lines + `! grep sorryAx` on the
whole namespace. The kernel-dm-w85 job compiles all three W85 kernels with
`if: always()` (independent per-step verdicts).

## 6. Comparator (official lane)

`comparator-official/challenges/142/RECEIPTS_official.txt`: **24/24 PASS**
(official=5, solution=11, controls=8), wall 201.17s,
**VERDICT: YOUR SOLUTION IS OKAY.** Includes S-VARNVIDES (the k=3 ancestor of
V-GEN: copy double-counting, ν(x) ≥ N/16 middle band, copy cap ≤ r_3(m)) and
negative controls N-AP/N-CAP/N-R3 (planted corruptions detected). Engine
receipt for the paper layer: `problem142-ap-free/receipts142uppergen.txt` —
**PASS=56 FAIL=0** (incl. VGEN-band exhaustive at 5 scales, VGEN-dblcount
exact at (3,9,1296) and (4,8,1024), negative control on the copy cap).

## 7. Findings (defects & notes)

| # | Severity | Location | Finding |
|---|---|---|---|
| N1 | INFO | DM142_Proof_D.lean L615–616 vs briefing text | The board theorem is the SHARP symbolic form `16*(r 3 N) ≤ (2*(r 3 8)+1)*N` = `16·r_3(N) ≤ 9·N` (r_3(8)=4). Briefings quoting "17·N" (the 2m+1 conservative corollary) UNDERSTATE the proven theorem. No action needed; quote 9 (or the symbolic form) in future records. |
| N2 | INFO | L54–62 | Dead lemmas: `coe_sub` and `apFree_subset` are declared in §0 but never used in this file (they are used in siblings A/C). Zero soundness impact; cosmetic carry-over of house machinery. |
| N3 | INFO | L3–4 | Dead imports: `Arsenal.ErdosTernary2.Basic` / `Arsenal.CardinalWorlds` have no call sites in this kernel — honestly recorded in WORKLOG_W85_142D.md ("honest omission > fake bridge"). Zero soundness impact (`#print axioms` proves nothing snuck in). |
| N4 | LOW (tooling, not the kernel) | audit_w85_adversarial.py L53–56 | The hand-typed "sanity anchor" dict has 5 wrong values ((3,4):4→3, (3,8):6→4, (3,20):8→9, (4,8):7→6, (4,9):8→7). The engine's own B&B (correct: matches OEIS + certified table + this audit's fresh DFS) flags them as "anchor disagreements" and continues — informational output, no gate depends on it. Recommend fixing the dict or deleting the anchor check in a future tooling pass. Does NOT touch DM142_Proof_D.lean, CI, or any receipt. |

**Adversarial holes hunted and NOT found:** no sorryAx anywhere in the run
(global sweep REAL=0); no custom axioms in any imported file; no circularity
in the lemma chain; no quiet hypothesis strengthening (paper hypotheses are
matched exactly, and aff_k's `hd : 1 ≤ d` is necessary, used, and
engine-verified in the relaxed no-containment form); no definition drift
(official abbrev verbatim, ENat coercion shapes exact, vendored FC
byte-checked); no non-closed-term `decide`; no `==`/BEq traps; the CI green
commit and the audited tip are byte-identical on the kernel and the workflow.

## 8. Next actions (recommendations, none blocking)

1. Record the sharp board constant (9, from r_3(8)=4) in WORKLOG/briefing text
   where "17" currently appears.
2. Optional hygiene: drop the two dead §0 lemmas and the two dead Arsenal
   imports from DM142_Proof_D.lean in the next kernel touch (would require a
   fresh CI round; not worth it on its own).
3. Fix or remove the mistyped anchor dict in audit_w85_adversarial.py (N4).

— W89-A142, audit complete. The green is real.
