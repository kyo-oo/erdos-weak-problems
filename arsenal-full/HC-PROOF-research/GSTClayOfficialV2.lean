import Mathlib
import GSTClayOfficial
import GSTHodgeAssaultV2

/-!
# RATIONAL HODGE LAYER V2 — ALL-WEIGHT FINITE GST CLASSIFICATION

This layer strengthens the rationalized internal GST statement.
It classifies every natural weight of the finite lattice and records
uniqueness on the three live diagonal weights.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTClayOfficialV2

open GSTWaveCohomology
open GSTLefschetzCrown
open GSTHodgeAssault
open GSTHodgeAssaultV2
open GSTClayOfficial

/-- Above weight two the rational cycle class is identically zero. -/
theorem ratCycleClass_zero_of_three_le (p : Nat) (hp : 3 ≤ p) :
    ratCycleClass p = fun _ => 0 := by
  funext c
  unfold ratCycleClass
  rw [cycleClass_zero_of_three_le p hp]
  norm_num

/-- **ALL-WEIGHT RATIONAL CLASSIFICATION.**  Every integral GST Hodge class,
after rationalization, is a rational multiple of its weight cycle class for
every p : Nat.  Above weight two this is the zero-sector statement. -/
theorem rational_hodge_all_weights
    (p : Nat) (f : WaveCoef) (hf : isHodgeClass p f) :
    ∃ q : ℚ, ∀ c : WaveCell,
      rat f c = q * ratCycleClass p c := by
  obtain ⟨z,hz⟩ := (hodge_class_all_weights p f).mp hf
  refine ⟨(z:ℚ), ?_⟩
  intro c
  unfold rat ratCycleClass
  exact_mod_cast hz c

/-- On live weights the rational coefficient is exactly the diagonal
coordinate, without existential ambiguity. -/
theorem rational_hodge_coefficient_exact
    (p : Nat) (hp : p < 3) (f : WaveCoef)
    (hf : isHodgeClass p f) :
    ∀ c : WaveCell,
      rat f c =
        ((gev f (4*p) : ℤ) : ℚ) * ratCycleClass p c := by
  obtain ⟨z,hz⟩ := hodge_conjecture p hp f hf
  have hzc := hodge_coefficient_eq_coordinate p hp f hf z hz
  intro c
  unfold rat ratCycleClass
  rw [← hzc]
  exact_mod_cast hz c

/-- The live rational coefficient is unique. -/
theorem rational_hodge_coefficient_unique
    (p : Nat) (hp : p < 3) (f : WaveCoef)
    (q r : ℚ)
    (hq : ∀ c : WaveCell, rat f c = q * ratCycleClass p c)
    (hr : ∀ c : WaveCell, rat f c = r * ratCycleClass p c) :
    q = r := by
  have hp4 : p < 4 := by omega
  let c : WaveCell := ⟨p,p,hp4,hp⟩
  have hc : ratCycleClass p c = 1 := by
    unfold ratCycleClass c
    rw [cycle_at_diagonal p p p hp4 hp rfl rfl]
    norm_num
  have h1 := hq c
  have h2 := hr c
  rw [hc, mul_one] at h1 h2
  linarith

/-- Above weight two every rationalized Hodge class is zero. -/
theorem rational_hodge_zero_of_three_le
    (p : Nat) (hp : 3 ≤ p) (f : WaveCoef)
    (hf : isHodgeClass p f) :
    rat f = fun _ => 0 := by
  have hz := hodge_class_zero_of_three_le p hp f hf
  funext c
  unfold rat
  rw [hz]
  norm_num


/-!
## Direct rational Clay theorem — no integral representative required

The original rationalization theorem above starts with an integral
\`WaveCoef\`.  A rational Hodge cochain can have nonintegral diagonal
coefficients, so this section proves the exact statement on *every*
rational-valued GST cochain.  It is an internal GST result and makes no
identification with the Betti cohomology of an arbitrary projective scheme.
-/

/-- Rational Hodge type is defined directly on the rational coefficient
space, rather than inherited by scalar extension from integral cochains. -/
def IsRationalHodgeClass (p : Nat) (f : RatCoef) : Prop :=
  ∀ c : WaveCell, c.carry ≠ p ∨ c.digit ≠ p → f c = 0

/-- A rational cycle monomial is zero away from its own diagonal, even
at weights beyond the finite GST world's three live diagonals. -/
theorem ratCycleClass_offDiagonal
    (p : Nat) (c : WaveCell)
    (hc : c.carry ≠ p ∨ c.digit ≠ p) :
    ratCycleClass p c = 0 := by
  by_cases hp : p < 3
  · rcases c with ⟨C, d, hC, hd⟩
    have hzero := cycle_at_offdiagonal p hp C d hC hd (by
      intro h
      rcases hc with hCne | hdne
      · exact hCne h.1
      · exact hdne h.2)
    simpa only [ratCycleClass, hzero, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ℚ)) hzero
  · have hthree : 3 ≤ p := by omega
    exact congrFun (ratCycleClass_zero_of_three_le p hthree) c

/-- **UNCONDITIONAL ALL-WEIGHT RATIONAL GST CLAY CLASSIFICATION.**
Every rational-valued pure Hodge cochain, not merely a rationalization
of an integer-valued cochain, is an *exact rational multiple* of the
corresponding explicit GST cycle monomial at every weight. -/
theorem rational_hodge_class_all_rational_weights
    (p : Nat) (f : RatCoef) :
    IsRationalHodgeClass p f ↔
      ∃ q : ℚ, ∀ c : WaveCell, f c = q * ratCycleClass p c := by
  constructor
  · intro hf
    by_cases hp : p < 3
    · have hp4 : p < 4 := by omega
      refine ⟨f ⟨p, p, hp4, hp⟩, ?_⟩
      intro c
      rcases c with ⟨C, d, hC, hd⟩
      by_cases hdiag : C = p ∧ d = p
      · rcases hdiag with ⟨hCp, hdp⟩
        have hcycle :
            ratCycleClass p (⟨C, d, hC, hd⟩ : WaveCell) = 1 := by
          unfold ratCycleClass
          rw [cycle_at_diagonal p C d hC hd hCp hdp]
          norm_num
        have hcell : (⟨C, d, hC, hd⟩ : WaveCell) =
            ⟨p, p, hp4, hp⟩ := by
          cases hCp
          cases hdp
          rfl
        rw [hcycle, mul_one, hcell]
      · have hzero : f (⟨C, d, hC, hd⟩ : WaveCell) = 0 := by
          apply hf
          by_contra h
          push_neg at h
          exact hdiag h
        have hcycle :
            ratCycleClass p (⟨C, d, hC, hd⟩ : WaveCell) = 0 := by
          unfold ratCycleClass
          rw [cycle_at_offdiagonal p hp C d hC hd hdiag]
          norm_num
        rw [hzero, hcycle, mul_zero]
    · have hthree : 3 ≤ p := by omega
      refine ⟨0, ?_⟩
      intro c
      have hzero : f c = 0 :=
        hf c (Or.inr (by have hd := c.hdigit; omega))
      rw [hzero, ratCycleClass_zero_of_three_le p hthree]
      simp
  · rintro ⟨q, hq⟩ c hc
    rw [hq c, ratCycleClass_offDiagonal p c hc, mul_zero]

/-- On each live diagonal, the coefficient of a rational GST Hodge class
is its own exact diagonal value, without an integral-lift assumption. -/
theorem rational_hodge_coefficient_direct
    (p : Nat) (hp : p < 3)
    (f : RatCoef) (hf : IsRationalHodgeClass p f) :
    ∀ c : WaveCell, f c =
      f ⟨p, p, (by omega), hp⟩ * ratCycleClass p c := by
  obtain ⟨q, hq⟩ := (rational_hodge_class_all_rational_weights p f).mp hf
  have hp4 : p < 4 := by omega
  have hc : ratCycleClass p ⟨p, p, hp4, hp⟩ = 1 := by
    unfold ratCycleClass
    rw [cycle_at_diagonal p p p hp4 hp rfl rfl]
    norm_num
  have hcoef : q = f ⟨p, p, hp4, hp⟩ := by
    have hval := hq ⟨p, p, hp4, hp⟩
    rw [hc, mul_one] at hval
    exact hval.symm
  intro c
  rw [hq c, hcoef]

/-- For a live weight, the direct rational cycle coefficient is unique. -/
theorem rational_hodge_coefficient_direct_unique
    (p : Nat) (hp : p < 3) (f : RatCoef)
    (q r : ℚ)
    (hq : ∀ c : WaveCell, f c = q * ratCycleClass p c)
    (hr : ∀ c : WaveCell, f c = r * ratCycleClass p c) :
    q = r := by
  have hp4 : p < 4 := by omega
  have hc : ratCycleClass p ⟨p, p, hp4, hp⟩ = 1 := by
    unfold ratCycleClass
    rw [cycle_at_diagonal p p p hp4 hp rfl rfl]
    norm_num
  have heq := (hq ⟨p, p, hp4, hp⟩).symm.trans
    (hr ⟨p, p, hp4, hp⟩)
  simpa only [hc, mul_one] using heq

/-- Every direct rational Hodge class at a live weight has a unique
rational cycle coordinate, with no assumption of integral origin. -/
theorem rational_hodge_unique_direct
    (p : Nat) (hp : p < 3) (f : RatCoef)
    (hf : IsRationalHodgeClass p f) :
    ∃! q : ℚ, ∀ c : WaveCell, f c = q * ratCycleClass p c := by
  obtain ⟨q, hq⟩ := (rational_hodge_class_all_rational_weights p f).mp hf
  refine ⟨q, hq, ?_⟩
  intro r hr
  exact rational_hodge_coefficient_direct_unique p hp f r q hr hq

#check IsRationalHodgeClass
#check ratCycleClass_offDiagonal
#check rational_hodge_class_all_rational_weights
#check rational_hodge_coefficient_direct
#check rational_hodge_coefficient_direct_unique
#check rational_hodge_unique_direct
#print axioms rational_hodge_class_all_rational_weights
#print axioms rational_hodge_coefficient_direct
#print axioms rational_hodge_unique_direct

theorem rational_v2_crown :
    (∀ p f, isHodgeClass p f →
      ∃ q : ℚ, ∀ c : WaveCell,
        rat f c = q * ratCycleClass p c)
    ∧ (∀ p, p < 3 → ∀ f, isHodgeClass p f →
      ∀ c : WaveCell,
        rat f c =
          ((gev f (4*p) : ℤ) : ℚ) * ratCycleClass p c)
    ∧ (∀ p, 3 ≤ p → ∀ f, isHodgeClass p f →
      rat f = fun _ => 0) := by
  exact ⟨rational_hodge_all_weights,
    rational_hodge_coefficient_exact,
    rational_hodge_zero_of_three_le⟩

#check ratCycleClass_zero_of_three_le
#check rational_hodge_all_weights
#check rational_hodge_coefficient_exact
#check rational_hodge_coefficient_unique
#check rational_hodge_zero_of_three_le
#check rational_v2_crown

#print axioms rational_hodge_all_weights
#print axioms rational_hodge_coefficient_exact
#print axioms rational_hodge_coefficient_unique
#print axioms rational_v2_crown

end GSTClayOfficialV2
