import MonolithGate.TailAssault406

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE TAIL ASSAULT, FACE C — the circle closed

THE composition BOSS ordered, round three.  Face A (r27-r29, CI-green,
run 45478223728) built the trit-tree law: the climb iff the exponent's
own ternary tree owns a bad edge.  The obstruction chamber
(GSTFourPowerExponentTritObstruction, CI-green inside Face A's import
closure) built the row law: the common two iff the prefix pair agrees
and the exponent trit is the killing trit.

THE TWO LAWS ARE ONE.  Chained, they close the circle unconditionally:

  treeBad K p  ↔  common two of `4^K` and `4^(K+1)` at row `p+1`

at EVERY level — no regime restriction, no edge cases.  The tree fire,
the row common two, and the climb's Happy row are one object read from
three sides.

* **SECTION 14 THE UNCONDITIONAL CIRCLE LINK** — `treeBad_iff_common_two`:
  one line, two green theorems, the whole sieve-to-climb dictionary.
* **SECTION 15 THE CLIMB'S COMPLETE CIRCLE** — `happy_iff_common_two_
  ge_three`: the climb iff the common-two statement, through the tree.
* **SECTION 16 THE TREE SILENCE** — a counterexample is exactly an
  exponent whose trit-tree never fires: the sieve's completeness, both
  directions.
* **SECTION 17 THE ONE-TRIT DODGE LAW** — the counterexample's exponent
  trit dodges the unique killing value whenever the prefix pair agrees:
  at most one trit value dies per tree node, which is why the survivor
  tree is immortal (growth ratio two-and-a-half per level, S_14 =
  1,255,248 survivors at depth fourteen).  The counterexample lives in
  the immortal tree's Cantor set AND keeps every power-digit two loud —
  the collision Face B stated, now on the circle's own terms.
* **SECTION 18 THE CIRCLE'S VERDICT** — Erdos #406's universal verdict
  from the common-two tail above the kernel base alone.

The engine never stops; it never lies.
-/

namespace GSTTailAssault406C

open GSTFourPowerDirectAdditionCarry

/-! ## SECTION 14 The unconditional circle link -/

open GSTFourPowerDirectResidue in
/-- **THE UNCONDITIONAL CIRCLE LINK.**  At every level `p`, the
trit-tree's bad edge IS the common two of `4^K` and `4^(K+1)` at row
`p+1` — no regime restriction, no edge cases.  Face A's tree law and
the obstruction chamber's row law are one theorem read from two sides. -/
theorem treeBad_iff_common_two (K p : Nat) :
    GSTTailAssault406.treeBad K p = true ↔
      (digit3 (4^K) (p+1) = 2 ∧ digit3 (4^(K+1)) (p+1) = 2) := by
  rw [GSTTailAssault406.treeBad_iff_prefix_killing_trit K p,
    GSTFourPowerExponentTritObstruction.row_common_two_iff_prefix_killing_trit K p]

/-! ## SECTION 15 The climb's complete circle -/

/-- **THE CLIMB'S COMPLETE CIRCLE.**  The climb's physical Happy rows,
the tree's bad edges, and the common-two statement are one object: the
climb holds exactly when the power owns a common ternary digit two at
some row at least three.  Stated in the tree law's own fully-qualified
form so the circle link fires verbatim. -/
theorem happy_iff_common_two_ge_three (K : Nat) :
    (∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)) ↔
      GSTFourPowerHappyProvider.CommonTwoGeThree K := by
  rw [GSTTailAssault406.happy_iff_treeBad K]
  constructor
  · rintro ⟨p, hp, hbad⟩
    exact ⟨p+1, by omega, ((treeBad_iff_common_two K p).1 hbad).1,
      ((treeBad_iff_common_two K p).1 hbad).2⟩
  · rintro ⟨q, hq, hd, hd'⟩
    have hqe : q - 1 + 1 = q := by omega
    refine ⟨q - 1, by omega, ?_⟩
    have hpair : GSTFourPowerDirectResidue.digit3 (4^K) (q - 1 + 1) = 2 ∧
        GSTFourPowerDirectResidue.digit3 (4^(K+1)) (q - 1 + 1) = 2 := by
      rw [hqe]
      exact ⟨hd, hd'⟩
    exact (treeBad_iff_common_two K (q - 1)).2 hpair

/-! ## SECTION 16 The tree silence — the sieve's completeness -/

open GSTFourPowerDirectResidue in
/-- **THE TREE SILENCE.**  A counterexample to the climb is exactly an
exponent whose trit-tree never fires at any level at least two: the
sieve's completeness, both directions.  Every kernel-decided tree fire
IS a common two, and every common two IS a tree fire. -/
theorem no_common_two_iff_tree_silence (K : Nat) :
    (¬ GSTFourPowerHappyProvider.CommonTwoGeThree K) ↔
      (∀ p : Nat, 2 ≤ p → GSTTailAssault406.treeBad K p = false) := by
  constructor
  · intro hNo p hp
    by_contra hfire
    have hf : GSTTailAssault406.treeBad K p = true := by
      cases h : GSTTailAssault406.treeBad K p with
      | true => rfl
      | false => exact absurd h hfire
    have hc := (treeBad_iff_common_two K p).1 hf
    exact hNo ⟨p+1, by omega, hc.1, hc.2⟩
  · intro hSil hC
    obtain ⟨q, hq, hd, hd'⟩ := hC
    have hqe : q - 1 + 1 = q := by omega
    have hpair : digit3 (4^K) (q - 1 + 1) = 2 ∧
        digit3 (4^(K+1)) (q - 1 + 1) = 2 := by
      rw [hqe]
      exact ⟨hd, hd'⟩
    have hfire : GSTTailAssault406.treeBad K (q - 1) = true :=
      (treeBad_iff_common_two K (q - 1)).2 hpair
    rw [hSil (q - 1) (by omega)] at hfire
    exact absurd hfire (by simp)

/-! ## SECTION 17 The one-trit dodge law — why the survivor tree is immortal -/

open GSTFourPowerDirectResidue in
/-- **THE ONE-TRIT DODGE LAW.**  A counterexample's exponent trit at
every level at least two dodges the unique killing value whenever the
prefix pair agrees.  At most one trit value dies per tree node — which
is why the survivor tree is immortal: each surviving node keeps at
least two of its three children, growth ratio two-and-a-half per level
(the engine's S_14 = 1,255,248 at depth fourteen).  The counterexample
is an infinite path through this immortal tree. -/
theorem counterexample_trit_dodge (K p : Nat) (hp : 2 ≤ p)
    (hNo : ¬ GSTFourPowerHappyProvider.CommonTwoGeThree K)
    (heq : digit3 (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1) =
      digit3 (4^((GSTFourPowerExponentTritObstruction.exponentPrefix K p)+1)) (p+1)) :
    GSTFourPowerExponentTritObstruction.exponentTrit K p ≠
      2 - digit3 (4^(GSTFourPowerExponentTritObstruction.exponentPrefix K p)) (p+1) := by
  intro hkill
  have hrow :=
    (GSTFourPowerExponentTritObstruction.row_common_two_iff_prefix_killing_trit K p).2
      ⟨heq, hkill⟩
  apply hNo
  exact ⟨p+1, by omega, hrow.1, hrow.2⟩

/-! ## SECTION 18 The circle's verdict -/

/-- **THE CIRCLE'S VERDICT.**  Erdos #406's universal verdict from the
common-two tail above the kernel base alone: the base band is
kernel-certified to 1500 through the circle, the composition is
machine-proven, and the entire remaining mathematical content of the
problem is the single named common-two tail — every exponent above the
base owning a shared ternary digit two with its successor power. -/
theorem erdos406_universal_verdict_of_common_two_tail
    (htail : ∀ K : Nat, 1500 < K →
      GSTFourPowerHappyProvider.CommonTwoGeThree K) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  erdos406_universal_verdict_of_climb
    (fun K hK8 => by
      rcases Nat.lt_or_ge K 1501 with h | h
      · exact GSTTailAssault406.erdos406_climb_base_1500 K hK8 (by omega)
      · exact (happy_iff_common_two_ge_three K).2 (htail K (by omega)))

/-! ## SECTION 19 Receipts -/

#print axioms treeBad_iff_common_two
#print axioms happy_iff_common_two_ge_three
#print axioms no_common_two_iff_tree_silence
#print axioms counterexample_trit_dodge
#print axioms erdos406_universal_verdict_of_common_two_tail

#eval "TAIL_ASSAULT_C_GREEN"

end GSTTailAssault406C
