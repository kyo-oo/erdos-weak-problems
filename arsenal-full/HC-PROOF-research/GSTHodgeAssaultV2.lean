import Mathlib
import GSTHodgeAssault

/-!
# HODGE ASSAULT V2 — ALL-WEIGHT INTERNAL CLASSIFICATION

This layer strengthens the finite GST diagonal algebra itself.
Weights 0,1,2 are the live rank-one diagonal sectors.  Every weight p >= 3
has no diagonal cell and therefore contains only the zero cochain.
No claim about arbitrary external varieties is made here.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTHodgeAssaultV2

open GSTWaveCohomology
open GSTCanonicalSevenAxisBridge
open GSTLefschetzCrown
open GSTHodgeAssault

/-- Above the three live diagonal weights, the cycle class vanishes. -/
theorem cycleClass_zero_of_three_le (p : Nat) (hp : 3 ≤ p) :
    cycleClass p = fun _ => 0 := by
  funext c
  rcases c with ⟨C,d,hC,hd⟩
  show cellClass (4*p) ⟨C,d,hC,hd⟩ = 0
  rw [cellClass_at]
  rw [if_neg]
  omega

/-- Above weight two every Hodge-class condition forces the zero cochain. -/
theorem hodge_class_zero_of_three_le
    (p : Nat) (hp : 3 ≤ p) (f : WaveCoef)
    (hf : isHodgeClass p f) :
    f = fun _ => 0 := by
  funext c
  have hd : c.digit < 3 := c.hdigit
  exact hf c (Or.inr (by omega))

/-- Zero is a Hodge class at every weight. -/
theorem zero_isHodgeClass (p : Nat) :
    isHodgeClass p (fun _ => 0) := by
  intro c hc
  rfl

/-- **ALL-WEIGHT CLASSIFICATION.**  Every finite-GST Hodge class is a
multiple of its cycle class, for every natural weight.  Above weight two
both sides reduce to zero. -/
theorem hodge_class_all_weights (p : Nat) (f : WaveCoef) :
    isHodgeClass p f ↔
      ∃ z : ℤ, ∀ c : WaveCell, f c = z * cycleClass p c := by
  by_cases hp : p < 3
  · exact hodge_class_rank_one p hp f
  · have hp3 : 3 ≤ p := by omega
    constructor
    · intro hf
      have hz := hodge_class_zero_of_three_le p hp3 f hf
      refine ⟨0, ?_⟩
      intro c
      rw [show f c = 0 by simpa [hz]]
      simp
    · rintro ⟨z,hz⟩
      have hc0 := cycleClass_zero_of_three_le p hp3
      have hf0 : f = fun _ => 0 := by
        funext c
        rw [hz c, hc0]
        simp
      rw [hf0]
      exact zero_isHodgeClass p

/-- For live weights the coefficient is unique. -/
theorem hodge_class_unique_coefficient
    (p : Nat) (hp : p < 3) (f : WaveCoef)
    (hf : isHodgeClass p f) :
    ∃! z : ℤ, ∀ c : WaveCell, f c = z * cycleClass p c := by
  obtain ⟨z,hz⟩ := hodge_conjecture p hp f hf
  refine ⟨z,hz,?_⟩
  intro w hw
  have hzero : ∀ c : WaveCell,
      (z-w) * cycleClass p c = 0 := by
    intro c
    calc
      (z-w) * cycleClass p c
          = z * cycleClass p c - w * cycleClass p c := by ring
      _ = f c - f c := by rw [← hz c, ← hw c]
      _ = 0 := sub_self _
  have hzw := hodge_class_torsion_free p hp (z-w) hzero
  omega

/-- The unique live-weight coefficient is exactly the diagonal coordinate. -/
theorem hodge_coefficient_eq_coordinate
    (p : Nat) (hp : p < 3) (f : WaveCoef)
    (hf : isHodgeClass p f)
    (z : ℤ) (hz : ∀ c : WaveCell, f c = z * cycleClass p c) :
    z = gev f (4*p) := by
  have hp4 : p < 4 := by omega
  have hcell := hz ⟨p,p,hp4,hp⟩
  have hcyc : cycleClass p ⟨p,p,hp4,hp⟩ = 1 :=
    cycle_at_diagonal p p p hp4 hp rfl rfl
  have hcoord := wave_coordinate_at f p p hp4 hp
  have hidx : 3*p+p = 4*p := by ring
  rw [hcyc, mul_one, hcoord, hidx] at hcell
  exact hcell.symm

/-- A compact coefficient type for the pure diagonal sector. -/
abbrev PureCoeffs := ℤ × ℤ × ℤ

def pureExpand (a : PureCoeffs) : WaveCoef :=
  fun cell =>
    a.1 * cycleClass 0 cell +
    a.2.1 * cycleClass 1 cell +
    a.2.2 * cycleClass 2 cell

/-- Pure classes have an exact canonical expansion. -/
theorem pure_hodge_expansion (f : WaveCoef) (hf : isPureHodge f) :
    f = pureExpand (gev f 0, gev f 4, gev f 8) := by
  obtain ⟨a,b,c,h⟩ := pure_hodge_generation f hf
  funext cell
  have hcell := h cell
  unfold pureExpand
  have h0 := h ⟨0,0,by decide,by decide⟩
  have h1 := h ⟨1,1,by decide,by decide⟩
  have h2 := h ⟨2,2,by decide,by decide⟩
  have c00 : cycleClass 0 ⟨0,0,by decide,by decide⟩ = 1 :=
    cycle_at_diagonal 0 0 0 (by decide) (by decide) rfl rfl
  have c01 : cycleClass 1 ⟨0,0,by decide,by decide⟩ = 0 :=
    cycle_at_offdiagonal 1 (by decide) 0 0 (by decide) (by decide) (by omega)
  have c02 : cycleClass 2 ⟨0,0,by decide,by decide⟩ = 0 :=
    cycle_at_offdiagonal 2 (by decide) 0 0 (by decide) (by decide) (by omega)
  have c10 : cycleClass 0 ⟨1,1,by decide,by decide⟩ = 0 :=
    cycle_at_offdiagonal 0 (by decide) 1 1 (by decide) (by decide) (by omega)
  have c11 : cycleClass 1 ⟨1,1,by decide,by decide⟩ = 1 :=
    cycle_at_diagonal 1 1 1 (by decide) (by decide) rfl rfl
  have c12 : cycleClass 2 ⟨1,1,by decide,by decide⟩ = 0 :=
    cycle_at_offdiagonal 2 (by decide) 1 1 (by decide) (by decide) (by omega)
  have c20 : cycleClass 0 ⟨2,2,by decide,by decide⟩ = 0 :=
    cycle_at_offdiagonal 0 (by decide) 2 2 (by decide) (by decide) (by omega)
  have c21 : cycleClass 1 ⟨2,2,by decide,by decide⟩ = 0 :=
    cycle_at_offdiagonal 1 (by decide) 2 2 (by decide) (by decide) (by omega)
  have c22 : cycleClass 2 ⟨2,2,by decide,by decide⟩ = 1 :=
    cycle_at_diagonal 2 2 2 (by decide) (by decide) rfl rfl
  rw [c00,c01,c02] at h0
  rw [c10,c11,c12] at h1
  rw [c20,c21,c22] at h2
  simp at h0 h1 h2
  have g0 : gev f 0 = a := by
    rw [← wave_coordinate_at f 0 0 (by decide) (by decide)]
    simpa using h0
  have g1 : gev f 4 = b := by
    rw [← wave_coordinate_at f 1 1 (by decide) (by decide)]
    simpa using h1
  have g2 : gev f 8 = c := by
    rw [← wave_coordinate_at f 2 2 (by decide) (by decide)]
    simpa using h2
  rw [g0,g1,g2]
  exact hcell

/-- Pure-sector coefficients are unique. -/
theorem pure_hodge_coefficients_unique
    (a b : PureCoeffs)
    (h : pureExpand a = pureExpand b) :
    a = b := by
  rcases a with ⟨a0,a1,a2⟩
  rcases b with ⟨b0,b1,b2⟩
  have h0 := congrArg (fun f : WaveCoef => f ⟨0,0,by decide,by decide⟩) h
  have h1 := congrArg (fun f : WaveCoef => f ⟨1,1,by decide,by decide⟩) h
  have h2 := congrArg (fun f : WaveCoef => f ⟨2,2,by decide,by decide⟩) h
  norm_num [pureExpand, cycleClass, cellClass, S12] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

theorem hodge_v2_crown :
    (∀ p f, isHodgeClass p f ↔
      ∃ z : ℤ, ∀ c : WaveCell, f c = z * cycleClass p c)
    ∧ (∀ p f, 3 ≤ p → isHodgeClass p f → f = fun _ => 0)
    ∧ (∀ p, p < 3 → ∀ f, isHodgeClass p f →
      ∃! z : ℤ, ∀ c : WaveCell, f c = z * cycleClass p c) := by
  refine ⟨hodge_class_all_weights, ?_, ?_⟩
  · intro p f hp hf
    exact hodge_class_zero_of_three_le p hp f hf
  · intro p hp f hf
    exact hodge_class_unique_coefficient p hp f hf

#check cycleClass_zero_of_three_le
#check hodge_class_zero_of_three_le
#check hodge_class_all_weights
#check hodge_class_unique_coefficient
#check hodge_coefficient_eq_coordinate
#check pure_hodge_expansion
#check pure_hodge_coefficients_unique
#check hodge_v2_crown

#print axioms hodge_class_all_weights
#print axioms hodge_class_unique_coefficient
#print axioms hodge_coefficient_eq_coordinate
#print axioms hodge_v2_crown

end GSTHodgeAssaultV2
