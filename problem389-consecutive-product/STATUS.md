# P389 STATUS — W59-B-2 round-1 kernel (E389_CONSECUTIVE_PRODUCT_GREEN)

1. FILE: `problem389-consecutive-product/Erdos389.lean` (549 lines, namespace
   `E389`, Kernel 67, W59-B-2). Only-imports law obeyed
   (`Arsenal.ErdosTernary2.Basic` + `Arsenal.CardinalWorlds` +
   `Arsenal.CardinalWorldsV2`); zero sorry / admit / native_decide / axiom
   (bracket- and token-audited); decide only on closed terms (bounded
   `List.range` sweeps ≤ 500 rows — the NO-OOM law, largest single chunk 500);
   `∣`-decidability only through the core Nat instances (the Kernel-45-green
   `2 ^ 254 ∣ _` pattern); binder law clean (no index-unified constructor
   args); L86/L90/L91/L92/L93 respected (omega only on consistent atoms, the
   ite-row heads split by by_cases/if_pos/if_neg first; no variable-level
   defeq trust; Bool ops parenthesized by construction).
2. RESEARCH BASE: the W59-T4r3 draft (Kernel 66, 305 lines) had the habitat
   (prodRange/countQ), the two corpus witnesses, the n ≤ 5 witness rows, the
   n ≤ 3 censuses, the mono/mod-shift/shift-law layer and the bridge — but
   (a) its mod-shift used an unverified `Nat.mul_mod_right` route (replaced
   with the CI-green Erdos700 chain `Nat.mul_mod/mod_self/zero_mul/zero_mod`
   under `Nat.add_mod`), (b) it lacked the battery's chain machinery
   (mCount/countChain/depthSum, the swap and crown laws), the Bool failRow
   exclusion mirror, the chunked minimality sweeps for n = 4..7, and the
   witness rows n = 6..11. The battery389.py ledger (93/93 GREEN,
   two-method cross-check: exact division + prime-valuation comparison)
   defines the kernel's target content; this kernel mirrors B1–B8 (B9's
   re-scan is the banked table itself).
3. DEFINITIONS (all equation-compiler structural, all folds rfl-unfolding):
   `prodRange n k` (the consecutive product n···n+k−1), `countQ q n k` (the
   window's q-multiple count), `mCount q m E` (the capped q-adic depth of a
   single integer), `countChain q n k E` (Σ_{e=1}^{E} countQ (q^e) n k), 
   `depthSum q n E k` (Σ_{i<k} mCount q (n+i) E), `failRow n j` (the
   battery's `fail_row` Bool mirror: j = 0 or the j-window fails), `k389`
   (the banked A375071 ledger [1,5,4,207,206,2475,984,8171,8170,45144,45143]).
4. COUNT LAWS (structural, full generality): `e389_count_mono` (widening the
   window never drops the count); `e389_mul_mod_self` + `e389_mod_shift` (the
   per-index congruence (a + q·t) % q = a % q); `e389_count_shift` +
   `e389_shift_law` (q ∣ k → the two k-blocks [n,n+k) and [n+k,n+2k) carry
   the SAME q-count — the symmetry core under every witness's window
   matching); `failRow_true_ne` (the Bool→Prop exclusion bridge).
5. CHAIN LAYER (THE CROWN CORE, structural): `e389_pow_le_dvd` (e ≤ f →
   q^e ∣ q^f); `e389_mCount_full`; `e389_depth_dvd` (q^mCount ∣ m); 
   `e389_chain_dvd` (q^depthSum ∣ prodRange — via `Nat.mul_dvd_mul`);
   `e389_chain_step` + `e389_chain_zero`; **THE SWAP LAW** `e389_swap`
   (countChain = depthSum — the battery's chain-identity, both double-
   counts of {(i,e)} proven structurally); `e389_chain_shift`; **THE CROWN
   LAW** `e389_crown` (q^e ∣ k for all 1 ≤ e ≤ E → q^countChain q n k E ∣
   the RIGHT block (n+k)···(n+2k−1) — the engine's crown-law instances made
   a theorem).
6. WITNESS TABLE (closed-term `∣`-decides, kernel-exact big-Nat arithmetic):
   the corpus pair `e389_witness_2_5` (720 ∣ 55440) and `e389_witness_3_4`
   (360 ∣ 5040); the A375071 rows `e389_witness_1_1`, `_4_207`, `_5_206`
   (≈10^397-digit left blocks vs ≈10^515-digit right blocks), `_6_2475`,
   `_7_984`, `_8_8171`, `_9_8170`, `_10_45144`, `_11_45143` (the n=10/11
   rows carry ≈2.1·10^5-digit blocks — the heaviest decides in the file).
   Receipts: `e389_habitat_values`, `e389_quotient_residues` (quotients 77
   and 14; near-miss residues 24 and 36; deficit primes 5 ∣ left-block,
   5 ∤ right-block — the battery's method-B diagnostics).
7. MINIMAL-K CENSUS n = 1..7 (B4/B8 mirror): the 13 failRow sweeps
   (`e389_sweep_1..5`, `_6a..6e`, `_7a/7b` — chunked ≤ 500 rows over
   [0,k(n)), n=6 needing 5 chunks, n=7 two) + the chunk assemblies
   `e389_min_value_6/7` + the full minimality theorems `e389_minimal_1..7`
   (works at k(n) AND every 1 ≤ j < k(n) fails — consumed through
   `List.all_eq_true.mp` + `List.mem_range.mpr`, the CI-green E317/E708
   idiom).
8. RECEIPTS (B5/B6/B7): `e389_count_receipts` (countQ values + the three
   shift instances at 5 ∣ 5, 2 ∣ 4, 3 ∣ 207-the-k(4)-scale);
   `e389_chain_receipts` (chain/mCount values + the two swap identities);
   the crown instances `e389_crown_inst_5_2_5` (5 ∣ 55440), `_2_3_4_2`
   (8 ∣ 5040), `_2_3_4_1` (4 ∣ 5040) — all decide-certified and all
   derivable from THE CROWN LAW; `k389_length` (the 11-row table).
9. ARSENAL BRIDGE: `e389_arsenal_bridge` — `ErdosTernary2.isTernaryDigit 2 =
   true` + three `CardinalWorldsV2.v2r_ternary_scaling` instances at the
   campaign anchors 44 and 14 and the #389-native anchor 720.
10. BOARD: `erdos389_board` — 26 conjuncts / 26 anonymous-constructor terms
    (11 witnesses + 7 census rows + mono/shift/swap/crown + 3 crown
    instances + the bridge), arity-audited. Receipts: 15 `#print axioms` +
    `#eval E389_CONSECUTIVE_PRODUCT_GREEN` (the CI grep target).
11. UNCOMPLETED (honest, future rounds): the count-soundness direction
    (dominance of the right block's q-counts for every q ≤ n+k−1 implying
    the divisibility — the draft's docstring-only lane, kept); the n ≥ 8
    minimality rows (k = 8171-scale sweeps ≈ 2·10^8 kernel steps — battery
    B4 stops at n=7); the n = 12..18 deep-scan witnesses (k = 3648830-scale
    products, battery-only); the k ≤ n/2 lane of THE_LIST §C-11 (the open
    mathematics).
12. VERDICT LAW: GitHub CI (`lake env lean problem389-consecutive-product/
    Erdos389.lean`, Mathlib v4.33.0-rc2 toolchain) is the verifier of
    record; author blind (no local toolchain); axioms must stay ⊆
    [propext, Classical.choice, Quot.sound].

## CI-RISK FLAGS (for the commander's root-repair round)

- **R1 (runtime, moderate):** the witness decides for n=10/11 (k=45144/
  45143 — ≈2·10^5-digit products, ~45K-step folds each) and the n=6 sweep
  (2475 rows × two ≤ 2475-step folds per row) put the file's total decide
  load at an estimated 20–60 s of kernel time. Precedent: Kernel 60b was
  SPLIT OUT of Erdos939 after a W58-E runner kill — if this file trips a
  runner timeout, the split point is the witness table (move rows n=8..11
  into a `Erdos389Heavy.lean` module with its own CI step, mirroring
  problem939-rpowerful/Erdos939R4.lean).
- **R2 (elaboration, low):** `e389_mod_shift` relies on the exact core form
  `Nat.add_mod a b n : (a + b) % n = (a % n + b % n) % n` (verified against
  the CI-green Erdos1073 usage at line 210); `e389_mul_mod_self` mirrors
  Erdos700 line 115 verbatim. If either lemma's form differs in this
  toolchain, the symptom is a rewrite-failure in those two proofs only —
  root-repair is replacing the two have-chains, no statement changes.
- **R3 (instance, low):** `by decide` on `∣`-Props relies on the core Nat
  dvd Decidable instance — the Kernel-45-green Erdos404Full precedent
  (`2 ^ 254 ∣ sumFacts22 witnessB22 := by decide`) proves the pattern.
- **R4 (rcases, low):** `e389_min_value_6/7` use `rcases (show A ∨ (B ∧ C)
  ∨ … by omega) with h | ⟨h, hu⟩ | …` — the Erdos1073 `show-by-omega`+
  rcases idiom flattened; if the 5-way rcases pattern line trips a parse
  issue, the E317 nested-rcases form is the drop-in replacement.
- **R5 (unused, none):** `e389_sweep_1` and `prodRange_zero/succ`,
  `countQ_zero/succ` are receipt-style only (the n=1 sweep mirrors the
  battery's B8 row; the equation theorems mirror the green-kernel habitat
  style) — not load-bearing.

## SUGGESTED kills.yml STEP (for the wiring owner; NOT applied by this agent)

```
      - name: "Kernel 67 - Erdos 389 CONSECUTIVE-PRODUCT DIVISIBILITY r1 (S059, W59-B-2): the consecutive-product kernel — prodRange/countQ/mCount/countChain/depthSum/failRow (the structural window folds + the battery's Bool exclusion mirror) + THE COUNT LAWS (mono, mul_mod_self, the repaired mod-shift, count_shift, THE SHIFT LAW) + THE CHAIN LAYER (pow_le_dvd, mCount_full, THE DEPTH LAW, THE CHAIN-POWER LAW, THE SWAP LAW countChain = depthSum, THE CHAIN-SHIFT, THE CROWN LAW) + THE 11-ROW WITNESS TABLE (A375071 n=1..11: 1, 5, 4, 207, 206, 2475, 984, 8171, 8170, 45144, 45143 — big-Nat kernel-exact decides) + THE MINIMAL-K CENSUS n=1..7 (13 failRow sweeps chunked ≤ 500 + the full minimality theorems) + the quotient/residue/deficit receipts + the count/chain/crown receipts + the k389 table + the arsenal bridge + the 26-conjunct board"
        if: always()
        shell: bash
        run: |
          set -euo pipefail
          lake build Arsenal.ErdosTernary2.Basic
          lake build Arsenal.CardinalWorlds
          lake build Arsenal.CardinalWorldsV2
          lake env lean problem389-consecutive-product/Erdos389.lean 2>&1 | tee kernel67.log
          ! grep -E 'error:|sorryAx|unknown identifier|unsolved goals|declaration uses .sorry.' kernel67.log
          grep -F "E389_CONSECUTIVE_PRODUCT_GREEN" kernel67.log
          grep -E "E389.(e389_shift_law|e389_swap|e389_crown|e389_witness_10_45144|e389_witness_11_45143|e389_minimal_6|e389_crown_inst_2_3_4_2|erdos389_board)' (does not depend on any axioms|depends on axioms)" kernel67.log
          echo KERNEL67_GREEN=1
```
