# WORKLOG_W84_61D — THE K5/E5 RAMSEY LADDER KERNELLED (lane W84-61B)

Task ID: W84-61B. The W83-named continuation of DM61_Closure's ledger
("K5, E5 = K̄5 | derived (the R(5,t) ≤ C(t+3,4) ladder at c = 1/5,
K5_PROOF.md); NOT in this kernel — named continuation (W83)") — now
executed: **BOTH K5 AND E5 ARE IN LEAN** (DM61_Proof_D.lean).

## The theorems

- `Erdos61D.eh_K5 : IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin 5))
  (fun n => (n:ℝ)^((1:ℝ)/5))` — the official predicate, verbatim
  DeepMind @ 2207c54d, at c = 1/5.
- `Erdos61D.eh_E5` — E5 = K̄5 by the complement transfer.
- `Erdos61D.erdos_61_k5_e5` — the family board.

## The Lean architecture (DM61_Proof_D.lean, ~700 lines)

| step | content |
|---|---|
| §1 | core-only power floors: one_le_pow, le_pow5, pow_le_pow_of_le (Nat.mul_le_mul induction — zero exotic API) |
| §2 | THE FALLING-FACTORIAL LADDER: 2·C(m,2) ≤ m², 6·C(m,3) ≤ m³, 24·C(m,4) ≤ m⁴ — sequential inductions on `choose_succ_succ'`, omega closing on choose/pow atoms |
| §3 | the integer fifth root: root5 := (range (n+1)).filter (t⁵ ≤ n) |>.max' — w⁵ ≤ n < (w+1)⁵ via max'_mem/le_max' + le_pow5 |
| §4 | THE RAMSEY LADDER (custom module): explicit-SET conclusions (∃ K, card = r ∧ IsClique ∨ ∃ I, card = s ∧ IsIndepSet) — plain induction on r+s; base r=2 (edge/edgeless) + s=2 (non-edge/complete); peel: N(v) vs V∖N[v] split via card_sdiff_add_card_eq_card; Pascal pays both recursive bounds; clique_extend/indep_extend through G.comap Subtype.val (defeq comap-adj) + v-extension |
| §5 | the bridge: a card-5 clique Finset + orderIsoOfFin + top_comap_of_pairwise → induced ⊤-copy (green pattern) |
| §6 | the ℕ spine: n ≥ 1024 → w ≥ 4 → (w+4)⁴ ≤ (3w)⁴ = 81w⁴ ≤ 24w⁵ ≤ 24n → C(w+4,4) ≤ n |
| §7 | the green rpow template: (n:ℝ)^(1/5) ≤ (w+1:ℝ) from n ≤ (w+1)⁵ (Real.rpow_le_rpow + rpow_natCast + REVERSED rpow_mul — DM61A's rpow_quarter_le_sqrt verbatim adapted) |
| §8 | eh_K5 (threshold 1024 rides eventually_atTop) + isEH_compl (green §5 verbatim) + eh_E5 |

## API receipts (all verified: Mathlib v4.33.0-rc2 sources fetched or green-kernel usage)

- `Nat.choose_succ_succ' (n k) : choose (n+1) (k+1) = choose n k + choose n (k+1)` — Choose/Basic.lean:66
- `Nat.choose_one_right (n) : choose n 1 = n` — Choose/Basic.lean:102
- `Nat.choose_pos {n k} (k ≤ n) : 0 < choose n k` — Choose/Basic.lean:117
- `Nat.choose_eq_zero_of_lt : n < k → choose n k = 0` — Choose/Basic.lean:85
- `Fintype.card_coe (s : Finset α) : Fintype.card ↥s = s.card` — Fintype/Card.lean:366 (as Fintype.card_coe)
- `Fintype.card_pos_iff : 0 < card α ↔ Nonempty α` — Fintype/Card.lean:294
- `Finset.card_sdiff_add_card_eq_card` — GREEN (DM107A:539)
- `Finset.max'_mem` / `Finset.le_max'` — GREEN (DM107A:752/762)
- `SimpleGraph.IsIndepSet.card_le_indepNum`, `indepNum_compl`, `G.irrefl`, `G.mem_neighborFinset` (G-first) — GREEN (DM61A)
- `Real.rpow_le_rpow`/`rpow_natCast`/`rpow_mul` (REVERSED) — GREEN (DM61A §4)
- `two_pow_pos`/`two_pow_ge2` — Arsenal/CardinalWorlds.lean:420/431 (genuine: the 1024 = 2¹⁰ threshold gates)

## Honest scope

- P4 (Seinsche) and the substitution closure: NOT this lane — the
  sibling lanes (W84-61A wrote the plan; the Seinsche MASTER analysis is
  fully derived in WORKLOG_W82_61A.md §2 and stands ready for the next
  kernel). erha89/bnss23/p5/c5: research-solved in the literature, not
  formalized here. The official open core `erdos_61`: claimed by no one.

## Residual risks for the warlord

1. `(G.comap Subtype.val).Adj x y` vs `G.Adj ↑x ↑y` — closed by `exact`
   through defeq; fallback `simp only [SimpleGraph.comap_adj] at hcl`.
2. `Finset.mem_coe.2 hx1` for the subtype set-membership of ↑K — the
   coe-of-subtype-Finset shape; fallback `Finset.mem_coe.mpr`.
3. `rw [h2']; decide` small-choose evaluations (choose 2 2 = 1 etc.) —
   decide evaluates closed Nat.choose ✓ (computable).

The engine never stops; it never lies. In English, always.

## REPAIR R2 (run 45071141985 post-mortem, 9 defects fixed — the S085 commander strike)

1. 119:45 `rw [← Nat.pow_add]` auto-closed via rfl (2+8 kernel-reduces to 10) — the
   trailing `norm_num` had no goals; DROPPED it.
2. 225:4 / 402:12 — `simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`
   made NO progress on Finset-coe membership (`↑({a,b} : Finset)` is not a Set
   insert); replaced with the VERIFIED Finset route `Finset.mem_coe,
   Finset.mem_insert, Finset.mem_singleton` (the combo CI-verified at lines 257/332
   of this very file).
3. LATENT (behind the 225 abort): both `{a,b}` branch ladders rewrote only ONE of
   x/y (`rw [hxa]` left `G.Adj a y` against `hab : G.Adj a b`); now
   `rw [hxa, hyb]` in all four branches (two_clique + the s=2 base).
4. 293:23 — THE MATH DEFECT: `indep_extend` was FALSE as stated (v ∈ B with
   ⟨v⟩ ∈ I breaks the card claim: insert v (image I) collapses). Added the
   hypothesis `(hvnotB : v ∉ B)`; hvnot now: v ∈ image → ⟨x, hx1, hx2⟩ with
   ↑x = v → `rw [← hx2]; exact x.2` → v ∈ B → contradiction. Caller updated
   (hvnotinB: v ∉ univ \ insert v N(v) via mem_sdiff + mem_insert (Or.inl rfl)).
5. 394:10 — `simpa using Nat.choose_succ_self_right (r-1)` simplified its own TYPE
   to True (simp couldn't bridge (r-1)+1 = r without positivity); replaced by the
   explicit `obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1` + `rw [show r'+1-1 = r' by omega]`
   + `exact Nat.choose_succ_self_right r'`.
6. 425:51 — `lt_of_le_of_lt` argument-shape error (choose_pos gives STRICT `<`,
   hcard gives `≤`); corrected to `Nat.lt_of_lt_of_le (Nat.choose_pos ...) hcard`
   (0 < choose ≤ card → 0 < card).
7. 511:4 — `Finset.exists_smaller_set` DOES NOT EXIST in Mathlib v4.33.0-rc2
   (unknown constant); wrote the CUSTOM MODULE (BOSS-authorized):
   `exists_subset_card_le` — Finset.induction_on, the m ≤ card split, the
   m = S.card+1 branch via ih S.card + insert-extend. Call site replaced.
8. 572:2 — `Nat.le_of_mul_le_mul_left hfin` missing the positivity argument
   (signature takes (h : mul_le) (hk : 0 < k)); now
   `Nat.le_of_mul_le_mul_left hfin (by norm_num)`.
9. 616:19 — the third `by omega` proves `2 ≤ root5 n + 1` which needs the REAL
   fact root5 n ≥ 1 (root5 n is an OPAQUE atom to omega); hoisted
   `hr5pos : 1 ≤ root5 n` before the ladder call: root5 n = 0 →
   root5_lt_succ_pow gives n < (0+1)^5 = 1 (norm_num) → contradiction with
   hn : 1024 ≤ n. omega then closes with hr5pos in context.

All nine from the run's log; the latent branch-ladder defects caught by
commander audit BEFORE they cost a CI round. 142C: CI-GREEN on the same run
(all 8 theorems axiom-clean [propext, Classical.choice, Quot.sound],
DM142C_UGEN0_GREEN printed). The wall is 61D alone.

## R4 + THE VERDICT (run 45083231558, job kernel-dm-w84, commit f43cab7): **GREEN — ALL EIGHT THEOREMS AXIOM-CLEAN**

The last defect on earth was the Or.imp ETA (hTsub : T ⊆ S does not unify as a
bare function argument at reducible transparency — the implicit-binder ∀ under
the Subset abbreviation; eta-expanded to (fun h => hTsub h)). With it:

    'Erdos61D.ramsey_ladder'            [propext, Classical.choice, Quot.sound]
    'Erdos61D.choose_le_of_ge_1024'     [propext, Classical.choice, Quot.sound]
    'Erdos61D.rpow_fifth_le_root5_succ' [propext, Classical.choice, Quot.sound]
    'Erdos61D.eh_K5'                    [propext, Classical.choice, Quot.sound]
    'Erdos61D.eh_E5'                    [propext, Classical.choice, Quot.sound]
    'Erdos61D.erdos_61_k5_e5'           [propext, Classical.choice, Quot.sound]
    'Erdos61D.arsenal_threshold_K5'     [propext, Quot.sound]
    'Erdos61D.four_and_twenty_choose_four_le' [propext, Quot.sound]

ZERO sorryAx. KERNEL_61DM_D_GREEN=1. DM61D_K5_GREEN printed. The K5/E5
official-form family theorem — the custom Ramsey ladder over the verbatim
DeepMind predicate at c = 1/5 — is KILLED, four repair rounds, one math
repair (the false-as-stated indep_extend), one custom Mathlib module
(exists_subset_card_le), 34 defects total.

The #61 official lane scoreboard: kernel-A (7-member family, c=1/4) GREEN,
kernel-B (closure ledger) GREEN, kernel-D (K5/E5 Ramsey) GREEN. The named
next: 61E (P4/Seinsche — architecture banked + probe receipts, all green).
