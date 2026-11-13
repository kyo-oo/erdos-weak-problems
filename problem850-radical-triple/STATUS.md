# P850 STATUS — W57-2r (radical triple kernel r1)

1. FILE: `problem850-radical-triple/Erdos850.lean` (~290 lines, namespace
   E850, zero sorry, zero native_decide, header per campaign law).
2. BOARD (16 theorems): `sameRad_refl/symm/trans`, `radCode_congr`,
   `rad_dvd`, `radSet_one`, `e850_radSet_table`, `ew3Row_sound`,
   `e850_row_50`, `e850_no_witness_50`, `ew2_pair_6_48`,
   `ew2_pair_6_48_code`, `ew2_pair_75_1215`, `ew2_pair_75_1215_code`,
   `e850_arsenal_bridge`, `e850_board` + receipt `#print axioms` ×16 +
   `#eval "E850_RADICAL_TRIPLE_GREEN"`.
3. CENSUS: `e850_no_witness_50` — NO length-3 witness pair x,y < 50 —
   assembled from the single-guard decide chunk `e850_row_50`
   (`∀ x < 50, ew3Row x 50 = true := by decide`, the E677 green shape) via
   the soundness induction `ew3Row_sound`; python confirms NO witness
   < 100 (and no walker failure at 50×50).
4. LENGTH-2 PAIRS: (6,48) Erdős family r=2 and (75,1215) Makowski — both
   decide-certified at radical-set level AND code level.
5. BRIDGE: cites all five Arsenal anchors — isTernaryDigit (1215 % 3),
   sq_sub_one 48, mod_mod_mul 1216 19 2, carryAtPos_bound 1216 1,
   CardinalWorldsV2.v2r_ternary_scaling 1 25 (v2r top-level).
6. Python (0.01s): radSet values, radCode 97-base injectivity on the
   board (all entries < 97), pair identities, census sweep — all PASS.
7. RISKS (author-blind, CI will verify): decide on List-eq
   (radSet-table/pairs — standard Lean 4, no in-campaign precedent);
   `List.mem_filter`/`Bool.and_eq_true`/`decide_eq_true_iff`/
   `Nat.dvd_of_mod_eq_zero` — all green-precedented in E411/E711.
8. NEXT: if CI green, bank W57-2r; if red, the error line pins the one
   lemma to swap (fallbacks: Nat.mod_add_div route for rad_dvd; rfl route
   for list-values).
