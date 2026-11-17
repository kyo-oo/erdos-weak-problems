import GSTFiniteSourceCorrection
import GSTClassicalHodgeCrossCarrierGeometricTransfer

/-!
# Multiple-source correction on the ORIGINAL smooth projective target

Proof draft; not compiled in this session.

OpenAI/math family 032 supplies a mathematical source theorem on CM
abelian varieties. It is not imported as an axiom here. `SourceAlgebraicity`
must be supplied for the chosen sources, with canonical comparisons proved
when connecting external geometry to the Stage-2G semantic carrier.

Compared with `NativeHodgeRetract` and `GeometricMultiSourceChowBirth`,
there is no exact one-step retract/hodgeSpan field. A finite or polynomial
residual certificate is used at the PRESCRIBED alpha. Sources may have
different codimensions, and the individual return operators may not commute.
Existence of suitable correspondences/certificates for arbitrary X is not
asserted. The construction creates actual native cycles from genuine source
cycles; it does not create new classes beyond their canonical image.
-/

open scoped BigOperators
noncomputable section
open GSTProjectiveOverC GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeCrossCarrierGeometricTransfer

namespace GSTClassicalHodgeFiniteSourceCorrection

structure SourceSystem (X : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData X) (p : ℕ) (ι : Type*) [Fintype ι] where
  source : ι → SmoothProjectiveComplexScheme
  data : (i : ι) → HodgeBigradedBettiData (source i)
  codim : ι → ℕ
  transfer : (i : ι) → CrossCarrierTransfer (source i) X (data i) H (codim i) p
  read : (i : ι) → ClassicalHodgeFiber X H p →ₗ[ℚ]
    ClassicalHodgeFiber (source i) (data i) (codim i)
  write : (i : ι) → ClassicalHodgeFiber (source i) (data i) (codim i) →ₗ[ℚ]
    ClassicalHodgeFiber X H p
  write_betti : ∀ i v, (write i v).1 = (transfer i).betti v.1

variable {X : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData X}
variable {p : ℕ} {ι : Type*} [Fintype ι]

namespace SourceSystem

/-- This is a SOURCE theorem, separate from all correspondence/correction data.
For CM sources its geometric proof comes from the external CM theorem;
the present module does not reprove that manuscript. -/
def SourceAlgebraicity (S : SourceSystem X H p ι) : Prop :=
  ∀ i (v : ClassicalHodgeFiber (S.source i) (S.data i) (S.codim i)),
    ∃ Z : codimensionCycles (S.source i).X (S.codim i),
      (S.data i).cycleClass (S.codim i) Z = v.1

def frame (S : SourceSystem X H p ι) :
    Module.End ℚ (ClassicalHodgeFiber X H p) where
  toFun v := ∑ i, S.write i (S.read i v)
  map_add' u v := by simp [map_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [map_smul, Finset.smul_sum]

def error (S : SourceSystem X H p ι) :
    Module.End ℚ (ClassicalHodgeFiber X H p) := 1 - S.frame

def sourceCycle (S : SourceSystem X H p ι) (h : S.SourceAlgebraicity)
    (i : ι) (v : ClassicalHodgeFiber X H p) :
    codimensionCycles (S.source i).X (S.codim i) :=
  Classical.choose (h i (S.read i v))

theorem sourceCycle_spec (S : SourceSystem X H p ι)
    (h : S.SourceAlgebraicity) (i : ι) (v : ClassicalHodgeFiber X H p) :
    (S.data i).cycleClass (S.codim i) (S.sourceCycle h i v) = (S.read i v).1 :=
  Classical.choose_spec (h i (S.read i v))

/-- A finite rational cycle on ORIGINAL X, selected using the target v. -/
def oneCorrection (S : SourceSystem X H p ι) (h : S.SourceAlgebraicity)
    (v : ClassicalHodgeFiber X H p) : codimensionCycles X.X p :=
  ∑ i, (S.transfer i).native (S.sourceCycle h i v)

theorem oneCorrection_class (S : SourceSystem X H p ι)
    (h : S.SourceAlgebraicity) (v : ClassicalHodgeFiber X H p) :
    H.cycleClass p (S.oneCorrection h v) = (v - S.error v).1 := by
  classical
  have hframe : H.cycleClass p (S.oneCorrection h v) = (S.frame v).1 := by
    calc
      H.cycleClass p (S.oneCorrection h v) =
          ∑ i, H.cycleClass p ((S.transfer i).native (S.sourceCycle h i v)) := by
            simp only [oneCorrection, map_sum]
      _ = ∑ i, (S.transfer i).betti (S.read i v).1 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [(S.transfer i).naturality, S.sourceCycle_spec h]
      _ = ∑ i, (S.write i (S.read i v)).1 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (S.write_betti i (S.read i v)).symm
      _ = (S.frame v).1 := by
            rw [show (S.frame v).1 = (∑ i, S.write i (S.read i v)).1 from rfl,
              Submodule.coe_sum]
  have hsub : v - S.error v = S.frame v := by
    change v - (v - S.frame v) = S.frame v
    abel
  rw [hsub]
  exact hframe

def correctedCycle (S : SourceSystem X H p ι) (h : S.SourceAlgebraicity)
    (n : ℕ) (alpha : ClassicalHodgeFiber X H p) : codimensionCycles X.X p :=
  GSTFiniteSourceCorrection.partialCycle S.error (S.oneCorrection h) n alpha

/-- Exact class equation for the supplied cycle-class map. Canonical
identification is an additional requirement of a geometric instantiation. -/
theorem correctedCycle_class (S : SourceSystem X H p ι)
    (h : S.SourceAlgebraicity) (n : ℕ) (alpha : ClassicalHodgeFiber X H p) :
    H.cycleClass p (S.correctedCycle h n alpha) =
      alpha.1 - ((S.error^n) alpha).1 := by
  exact GSTFiniteSourceCorrection.partialCycle_class
    (H.cycleClass p) (rationalHodgeSubspace (H.hodgeBigrading p)).subtype
    S.error (S.oneCorrection h) (S.oneCorrection_class h) n alpha

/-- Local finite extinction produces a native cycle on the original X. -/
theorem exact_originalX_cycle_of_target_nilpotent (S : SourceSystem X H p ι)
    (h : S.SourceAlgebraicity) (n : ℕ) (alpha : ClassicalHodgeFiber X H p)
    (hn : (S.error^n) alpha = 0) :
    H.cycleClass p (S.correctedCycle h n alpha) = alpha.1 := by
  rw [S.correctedCycle_class h, hn]
  simp

/-- Polynomial finite correction can succeed even for a nonnilpotent error. -/
theorem exact_originalX_cycle_of_polynomial (S : SourceSystem X H p ι)
    (h : S.SourceAlgebraicity) (r : ℕ) (c : ℕ → ℚ)
    (alpha : ClassicalHodgeFiber X H p)
    (hpoly : (∑ k ∈ Finset.range r, c k • (S.error^k) alpha) = 0)
    (hvalue : (∑ k ∈ Finset.range r, c k) ≠ 0) :
    ∃ Z : codimensionCycles X.X p, H.cycleClass p Z = alpha.1 := by
  refine ⟨(∑ k ∈ Finset.range r, c k)⁻¹ •
    GSTFiniteSourceCorrection.weightedCycle S.error (S.oneCorrection h) r c alpha, ?_⟩
  exact GSTFiniteSourceCorrection.exact_of_polynomial_annihilator
    (H.cycleClass p) (rationalHodgeSubspace (H.hodgeBigrading p)).subtype
    S.error (S.oneCorrection h) (S.oneCorrection_class h) r c alpha hpoly hvalue

/-- Global nilpotence is sufficient, but it is an additional geometric input. -/
theorem hodge_at_weight_of_nilpotent_error (S : SourceSystem X H p ι)
    (h : S.SourceAlgebraicity) (n : ℕ) (hn : S.error^n = 0) :
    ∀ alpha : ClassicalHodgeFiber X H p,
      ∃ Z : codimensionCycles X.X p, H.cycleClass p Z = alpha.1 := by
  intro alpha
  refine ⟨S.correctedCycle h n alpha, S.exact_originalX_cycle_of_target_nilpotent h n alpha ?_⟩
  rw [hn]
  rfl

/-- An invisible direction is fixed by the error. This guards against
calling repeated applications of the same source image a new source birth. -/
theorem error_fixes_blind_target (S : SourceSystem X H p ι)
    (alpha : ClassicalHodgeFiber X H p) (ha : S.frame alpha = 0) :
    S.error alpha = alpha := by
  change alpha - S.frame alpha = alpha
  rw [ha, sub_zero]

theorem blind_target_forbids_polynomial_certificate (S : SourceSystem X H p ι)
    (alpha : ClassicalHodgeFiber X H p) (ha : S.frame alpha = 0)
    (r : ℕ) (c : ℕ → ℚ)
    (hpoly : (∑ k ∈ Finset.range r, c k • (S.error^k) alpha) = 0)
    (hvalue : (∑ k ∈ Finset.range r, c k) ≠ 0) : alpha = 0 := by
  exact GSTFiniteSourceCorrection.polynomial_certificate_forbids_fixed_mode
    S.error alpha (S.error_fixes_blind_target alpha ha) r c hpoly hvalue

end SourceSystem

#print axioms SourceSystem.correctedCycle_class
#print axioms SourceSystem.exact_originalX_cycle_of_polynomial
#print axioms SourceSystem.blind_target_forbids_polynomial_certificate

end GSTClassicalHodgeFiniteSourceCorrection
