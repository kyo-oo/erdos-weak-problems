import GSTClassicalHodgeIntegralLiveSupport
import GSTClassicalHodgeRecoordinationArsenalCrown
import GSTWorldRecoordinationGroupoid
import GSTClassicalHodgeFullArsenalIrreducibility

/-!
# GST CLASSICAL HODGE — INTEGRAL WORLD EMBEDDING

The rational Hodge coefficients have now been cleared to integers.  This
module places those integer live coordinates into an actual finite GST world,
so the original integer-valued projector/recoordination machinery acts on the
state itself rather than on an auxiliary rational model.

The canonical live world has one row and `N` columns, where `N` is the finite
support cardinality.  Its state code is exactly the live slot number.  The
integer coefficient field is obtained by integralizing the finite rational
live vector.  Exact code projectors isolate the integral live coordinates,
and recoordination carries them functorially to every equal-cardinality world.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteSupportArsenalConjugation
open GSTClassicalHodgeIntegralLiveSupport
open GSTClassicalHodgeRecoordinationArsenalCrown
open GSTWorldRecoordinationGroupoid

namespace GSTClassicalHodgeIntegralWorldEmbedding

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Finite rational live vector as a `Finsupp`, using finiteness of `Fin N`. -/
noncomputable def liveRationalFinsupp
    (alpha : ClassicalHodgeFiber V H p) :
    Fin (liveRank alpha) →₀ ℚ :=
  Finsupp.equivFunOnFinite.symm (liveCoordinateVector alpha)

@[simp]
theorem liveRationalFinsupp_apply
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    liveRationalFinsupp alpha r = liveCoordinateVector alpha r := by
  simp [liveRationalFinsupp]

/-- Integralized live slot vector. -/
noncomputable def integralLiveFinsupp
    (alpha : ClassicalHodgeFiber V H p) :
    Fin (liveRank alpha) →₀ ℤ :=
  integralize (liveRationalFinsupp alpha)

/-- Integer coefficient field on the canonical live GST world. -/
noncomputable def integralLiveWorld
    (alpha : ClassicalHodgeFiber V H p) :
    ShapeCoef (liveLinearShape alpha) :=
  fun x => integralLiveFinsupp alpha x.2

/-- Exact denominator used by the finite live vector. -/
def liveDenominator
    (alpha : ClassicalHodgeFiber V H p) : Nat :=
  commonDenominator (liveRationalFinsupp alpha)

/-- Every live rational coordinate is recovered exactly from the integer GST
world coefficient. -/
theorem integralLiveWorld_recovers
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    liveCoordinateVector alpha r =
      (liveDenominator alpha : ℚ)⁻¹ *
        (integralLiveWorld alpha (liveShapeState alpha r) : ℚ) := by
  unfold integralLiveWorld integralLiveFinsupp liveDenominator
  rw [← liveRationalFinsupp_apply alpha r]
  simpa [liveShapeState] using
    recover_from_integralize (liveRationalFinsupp alpha) r

/-- Every live slot remains nonzero after denominator clearing. -/
theorem integralLiveWorld_live_ne_zero
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    integralLiveWorld alpha (liveShapeState alpha r) ≠ 0 := by
  intro hz
  have hrec := integralLiveWorld_recovers alpha r
  have hden := commonDenominator_cast_ne_zero (liveRationalFinsupp alpha)
  rw [hz] at hrec
  simp at hrec
  exact liveCoordinateVector_ne_zero_at alpha r hrec

/-- Exact integer code projector isolates one live slot. -/
theorem integer_projector_live_self
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    codeSectorProj (liveLinearShape alpha) r.1 (integralLiveWorld alpha)
        (liveShapeState alpha r) =
      integralLiveWorld alpha (liveShapeState alpha r) := by
  simp only [codeSectorProj]
  rw [if_pos (liveShapeState_code alpha r)]

/-- Exact integer code projector kills every other live slot. -/
theorem integer_projector_live_other
    (alpha : ClassicalHodgeFiber V H p)
    (r s : Fin (liveRank alpha))
    (hsr : s ≠ r) :
    codeSectorProj (liveLinearShape alpha) r.1 (integralLiveWorld alpha)
        (liveShapeState alpha s) = 0 := by
  have hcode : s.1 ≠ r.1 := by
    intro h
    apply hsr
    exact Fin.ext h
  have hcode' : ¬ worldCode (liveLinearShape alpha) (liveShapeState alpha s) = r.1 := by
    rw [liveShapeState_code alpha s]
    exact hcode
  simp only [codeSectorProj]
  rw [if_neg hcode']

/-- Integer live projectors commute with arbitrary equal-cardinality GST world
recoordination by the original groupoid theorem. -/
theorem integer_projector_recoordination_natural
    (alpha : ClassicalHodgeFiber V H p)
    (T : GSTWorldShape (liveRank alpha))
    (r : Fin (liveRank alpha)) :
    transportCoef (liveLinearShape alpha) T
        (codeSectorProj (liveLinearShape alpha) r.1 (integralLiveWorld alpha)) =
      codeSectorProj T r.1
        (transportCoef (liveLinearShape alpha) T (integralLiveWorld alpha)) :=
  transportCoef_codeSectorProj (liveLinearShape alpha) T r.1
    (integralLiveWorld alpha)

/-- Every integral live sheet has an explicit spectral polynomial projector
with nonzero integer scale. -/
theorem integral_live_projector_polynomial
    (alpha : ClassicalHodgeFiber V H p)
    (r : Fin (liveRank alpha)) :
    ∃ (P : Polynomial ℤ) (c : ℤ), c ≠ 0 ∧
      ∀ x : ShapeState (liveLinearShape alpha),
        codePolyOp (liveLinearShape alpha) P (integralLiveWorld alpha) x =
          c * codeSectorProj (liveLinearShape alpha) r.1
            (integralLiveWorld alpha) x := by
  obtain ⟨P, c, hc, hP⟩ := codeSector_projector_polynomial
    (liveLinearShape alpha) r.1 r.2
  exact ⟨P, c, hc, fun x => hP (integralLiveWorld alpha) x⟩

/-- **INTEGRAL WORLD CROWN.** Every nonzero genuine rational Hodge class has
an actual finite integer GST world observation in which every live coordinate
is nonzero, exactly recoverable over `Q`, spectrally projectable, and natural
under arbitrary world recoordination. -/
theorem integral_world_embedding_crown
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    (∀ r : Fin (liveRank alpha),
      integralLiveWorld alpha (liveShapeState alpha r) ≠ 0)
    ∧ (∀ r : Fin (liveRank alpha),
      liveCoordinateVector alpha r =
        (liveDenominator alpha : ℚ)⁻¹ *
          (integralLiveWorld alpha (liveShapeState alpha r) : ℚ))
    ∧ (∀ r : Fin (liveRank alpha),
      ∃ (P : Polynomial ℤ) (c : ℤ), c ≠ 0 ∧
        ∀ x : ShapeState (liveLinearShape alpha),
          codePolyOp (liveLinearShape alpha) P (integralLiveWorld alpha) x =
            c * codeSectorProj (liveLinearShape alpha) r.1
              (integralLiveWorld alpha) x) := by
  exact ⟨integralLiveWorld_live_ne_zero alpha,
    integralLiveWorld_recovers alpha,
    integral_live_projector_polynomial alpha⟩

#check liveRationalFinsupp
#check integralLiveFinsupp
#check integralLiveWorld
#check liveDenominator
#check integralLiveWorld_recovers
#check integralLiveWorld_live_ne_zero
#check integer_projector_live_self
#check integer_projector_live_other
#check integer_projector_recoordination_natural
#check integral_live_projector_polynomial
#check integral_world_embedding_crown

#print axioms integralLiveWorld_recovers
#print axioms integralLiveWorld_live_ne_zero
#print axioms integer_projector_recoordination_natural
#print axioms integral_live_projector_polynomial
#print axioms integral_world_embedding_crown

end GSTClassicalHodgeIntegralWorldEmbedding
