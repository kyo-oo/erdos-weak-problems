import Mathlib
import GSTGradedWorldAlgebra
import GSTWorldCrownBridge

/-!
# GST UNIVERSAL LEFSCHETZ DYNAMICS

The original 4 x 3 crown proves a fixed degree-descent theorem and L^6 = 0.
Those are shadows of a dimension-free causal law.

For every rectangular A x B GST world define

  L = D_1 + C_1,

the sum of one digit shift and one carry shift.

Every application raises total degree by exactly one.  Hence:
* L^k vanishes at every cell of degree < k;
* L^k transports a pure degree-r sector into degree r+k;
* for positive A,B, L^(A+B-1) = 0 globally.

The old twelve-cell L^6 theorem is recovered by A=4, B=3.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTUniversalLefschetzDynamics

open GSTWorldCosmology
open GSTGradedWorldAlgebra
open GSTWorldCrownBridge
open GSTLefschetzCrown
open GSTWaveCohomology

/-- Dimension-free polarization operator. -/
def worldLefschetz {A B : Nat}
    (g : WorldCoef A B) : WorldCoef A B :=
  fun c => digitShiftN 1 g c + carryShiftN 1 g c

@[simp]
theorem worldLefschetz_at
    {A B : Nat} (g : WorldCoef A B) (c : WorldCell A B) :
    worldLefschetz g c =
      digitShiftN 1 g c + carryShiftN 1 g c :=
  rfl

/-- One-step digit predecessor formula. -/
theorem digitShift_one_at
    {A B : Nat} (g : WorldCoef A B)
    (C d : Nat) (hC : C < A) (hd : d < B)
    (hpos : 0 < d) :
    digitShiftN 1 g (⟨C,hC⟩, ⟨d,hd⟩) =
      g (⟨C,hC⟩, ⟨d-1, by omega⟩) := by
  simp [digitShiftN, show 1 ≤ d by omega]

/-- Digit boundary truncation. -/
theorem digitShift_one_zero
    {A B : Nat} (g : WorldCoef A B)
    (C : Nat) (hC : C < A) (hB : 0 < B) :
    digitShiftN 1 g (⟨C,hC⟩, ⟨0,hB⟩) = 0 := by
  simp [digitShiftN]

/-- One-step carry predecessor formula. -/
theorem carryShift_one_at
    {A B : Nat} (g : WorldCoef A B)
    (C d : Nat) (hC : C < A) (hd : d < B)
    (hpos : 0 < C) :
    carryShiftN 1 g (⟨C,hC⟩, ⟨d,hd⟩) =
      g (⟨C-1, by omega⟩, ⟨d,hd⟩) := by
  simp [carryShiftN, show 1 ≤ C by omega]

/-- Carry boundary truncation. -/
theorem carryShift_one_zero
    {A B : Nat} (g : WorldCoef A B)
    (d : Nat) (hA : 0 < A) (hd : d < B) :
    carryShiftN 1 g (⟨0,hA⟩, ⟨d,hd⟩) = 0 := by
  simp [carryShiftN]

/-- The universal polarization raises a pure total-degree sector by one. -/
theorem worldLefschetz_respects_degree
    {A B : Nat} (k : Nat) (g : WorldCoef A B) :
    worldLefschetz (worldSectorProj k g) =
      worldSectorProj (k+1) (worldLefschetz g) := by
  unfold worldLefschetz
  rw [digitShiftN_respects_degree 1 k g,
      carryShiftN_respects_degree 1 k g]
  exact (worldSectorProj_add (k+1)
    (digitShiftN 1 g) (carryShiftN 1 g)).symm

/-- k iterations transport degree r exactly into degree r+k. -/
theorem worldLefschetz_iterate_respects_degree
    {A B : Nat} (k r : Nat) (g : WorldCoef A B) :
    Nat.iterate worldLefschetz k (worldSectorProj r g) =
      worldSectorProj (r+k) (Nat.iterate worldLefschetz k g) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      rw [ih, worldLefschetz_respects_degree]
      congr 1

/-- **DIMENSION-FREE DEGREE DESCENT.**

After k polarizations, every cell below degree k is zero.  No fixed world
size appears in the statement. -/
theorem worldLefschetz_iterate_zero
    {A B : Nat} (k : Nat) (g : WorldCoef A B) :
    ∀ (C d : Nat) (hC : C < A) (hd : d < B),
      C + d < k →
        (Nat.iterate worldLefschetz k g)
          (⟨C,hC⟩, ⟨d,hd⟩) = 0 := by
  induction k with
  | zero =>
      intro C d hC hd h
      omega
  | succ k ih =>
      intro C d hC hd hlt
      rw [Function.iterate_succ', Function.comp_apply]
      rw [worldLefschetz_at]
      by_cases hd0 : d = 0
      · subst d
        rw [digitShift_one_zero
          (Nat.iterate worldLefschetz k g) C hC hd]
        by_cases hC0 : C = 0
        · subst C
          rw [carryShift_one_zero
            (Nat.iterate worldLefschetz k g) 0 hC hd]
          ring
        · rw [carryShift_one_at
            (Nat.iterate worldLefschetz k g) C 0 hC hd
            (by omega)]
          rw [ih (C-1) 0 (by omega) hd (by omega)]
          ring
      · rw [digitShift_one_at
          (Nat.iterate worldLefschetz k g) C d hC hd
          (by omega)]
        rw [ih C (d-1) hC (by omega) (by omega)]
        by_cases hC0 : C = 0
        · subst C
          rw [carryShift_one_zero
            (Nat.iterate worldLefschetz k g) d hC hd]
          ring
        · rw [carryShift_one_at
            (Nat.iterate worldLefschetz k g) C d hC hd
            (by omega)]
          rw [ih (C-1) d (by omega) hd (by omega)]
          ring

/-- In a positive A x B world, top total degree is strictly below A+B-1. -/
theorem worldDegree_lt_sharp
    {A B : Nat} (hA : 0 < A) (hB : 0 < B)
    (c : WorldCell A B) :
    worldDegree c < A+B-1 := by
  rcases c with ⟨⟨C,hC⟩,⟨d,hd⟩⟩
  unfold worldDegree
  omega

/-- **UNIVERSAL LEFSCHETZ NILPOTENCE CEILING.**

Every positive A x B GST world satisfies L^(A+B-1)=0.
The exponent is derived from world dimensions rather than hard-coded. -/
theorem worldLefschetz_nilpotent
    {A B : Nat} (hA : 0 < A) (hB : 0 < B)
    (g : WorldCoef A B) :
    Nat.iterate worldLefschetz (A+B-1) g = fun _ => 0 := by
  funext c
  rcases c with ⟨⟨C,hC⟩,⟨d,hd⟩⟩
  exact worldLefschetz_iterate_zero (A+B-1) g
    C d hC hd (by omega)

/-- The twelve-cell polarization is exactly the 4 x 3 specialization of
the dimension-free world polarization under the chart equivalence. -/
theorem liftWave_lefschetzOp (g : WaveCoef) :
    liftWave (lefschetzOp g) =
      worldLefschetz (liftWave g) := by
  funext c
  have hd := congrFun (liftWave_cupDigit g) c
  have hc := congrFun (liftWave_cupCarry g) c
  change
    liftWave (cupDigit g) c + liftWave (cupCarry g) c =
      digitShiftN 1 (liftWave g) c +
        carryShiftN 1 (liftWave g) c
  rw [hd, hc]

/-- Every iterate of the old crown is the chart restriction of the universal
world Lefschetz iterate. -/
theorem liftWave_lefschetz_iterate
    (k : Nat) (g : WaveCoef) :
    liftWave (Nat.iterate lefschetzOp k g) =
      Nat.iterate worldLefschetz k (liftWave g) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [Function.iterate_succ', Function.iterate_succ',
        Function.comp_apply, Function.comp_apply,
        liftWave_lefschetzOp, ih]

/-- The old L^6=0 theorem is absorbed as A=4, B=3. -/
theorem lefschetz_sixth_power_from_universal
    (g : WaveCoef) :
    Nat.iterate lefschetzOp 6 g = fun _ => 0 := by
  apply liftWave_injective
  rw [liftWave_lefschetz_iterate]
  have h :=
    worldLefschetz_nilpotent
      (A:=4) (B:=3) (by decide) (by decide) (liftWave g)
  rw [h]
  rfl

/-- Capstone for dimension-free Lefschetz dynamics. -/
theorem universal_lefschetz_crown :
    (∀ A B k (g : WorldCoef A B) C d
        (hC : C < A) (hd : d < B),
      C+d < k →
        (Nat.iterate worldLefschetz k g)
          (⟨C,hC⟩,⟨d,hd⟩) = 0)
    ∧ (∀ A B, 0 < A → 0 < B → ∀ g : WorldCoef A B,
      Nat.iterate worldLefschetz (A+B-1) g = fun _ => 0)
    ∧ (∀ A B k r (g : WorldCoef A B),
      Nat.iterate worldLefschetz k (worldSectorProj r g) =
        worldSectorProj (r+k)
          (Nat.iterate worldLefschetz k g)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B k g C d hC hd hlt
    exact worldLefschetz_iterate_zero k g C d hC hd hlt
  · intro A B hA hB g
    exact worldLefschetz_nilpotent hA hB g
  · intro A B k r g
    exact worldLefschetz_iterate_respects_degree k r g

#check worldLefschetz
#check worldLefschetz_respects_degree
#check worldLefschetz_iterate_respects_degree
#check worldLefschetz_iterate_zero
#check worldDegree_lt_sharp
#check worldLefschetz_nilpotent
#check liftWave_lefschetzOp
#check liftWave_lefschetz_iterate
#check lefschetz_sixth_power_from_universal
#check universal_lefschetz_crown

#print axioms worldLefschetz_iterate_zero
#print axioms worldLefschetz_nilpotent
#print axioms liftWave_lefschetz_iterate
#print axioms lefschetz_sixth_power_from_universal
#print axioms universal_lefschetz_crown

end GSTUniversalLefschetzDynamics
