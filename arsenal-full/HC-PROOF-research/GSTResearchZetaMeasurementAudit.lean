import GSTMathboxCorrectedZetaActualHodge
import GSTClassicalHodgeRankFreeArsenalIrreducibility

/-!
# Mathbox adversarial audit: does a freely chosen zeta coefficient add geometry?

A decisive structural check of the author's corrected Equation (3).
For x=y=2 the independently verified infinite series equals -1.

If the real amplitude called "zetaAtS" is freely chosen (NOT proven to
be an actual zeta value at a fixed spectral parameter), then the
existence of a nonzero corrected-series measurement is EQUIVALENT
to existence of any nonzero native rational algebraic cycle class.

Forward direction: a nonzero scalar measurement forces the native
class nonzero. Backward direction: on every nonzero Hodge vector,
an actual rational basis coordinate is nonzero, and the freely
adjustable real coefficient may be chosen to match it because tsum=-1.

Thus a free zeta scalar is NOT itself an independent geometric
existence theorem. The genuinely NEW input has to be:
(1) a FIXED analytic zeta value, associated with a well-defined
parameter s, (2) an independently defined canonical geometric
readout/period, (3) the proved equality between this period and the
corrected series, and (4) enough actual realized correspondences.

This proof guards the original Hodge conjecture from an accidental
circularity or an analytically manufactured geometric certificate.
-/

set_option maxHeartbeats 20000000
noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeGeometricCycleClassSpine
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTMathboxCorrectedZetaGeometry
open GSTMathboxCorrectedZetaInfinite
open GSTMathboxCorrectedZetaActualHodge

namespace GSTResearchZetaMeasurementAudit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A genuinely nonzero native rational algebraic-cycle Hodge class. -/
def HasNonzeroNativeClass (G : GeometricCycleClassSpine V H) : Prop :=
  ∃ Z : codimensionCycles V.X p, geometricHodgeClass G Z ≠ 0

/-- The earlier corrected-series certificate with a freely adjustable
real scalar. Do not mistake this `zetaAtS` variable for the value of a
fixed Riemann zeta function: there is NO spectral parameter in the type. -/
def HasFreelyAdjustedZetaCertificate
    (G : GeometricCycleClassSpine V H) : Prop :=
  ∃ (Z : codimensionCycles V.X p)
    (read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (zetaAtS : ℝ),
      zetaAtS ≠ 0 ∧
      ((read (geometricHodgeClass G Z) : ℚ) : ℝ) =
        zetaAtS * (∑' m : ℕ, indexedKernel 2 2 m)

/-- Exact if-and-only-if: with a FREE real zeta multiplier, corrected
series certification is equivalent to an already nonzero genuine
native cycle class. This marks the next non-circular geometric input. -/
theorem freely_adjusted_zeta_certificate_iff_nonzero_native_class
    (G : GeometricCycleClassSpine V H) :
    HasFreelyAdjustedZetaCertificate (p := p) G ↔
      HasNonzeroNativeClass (p := p) G := by
  constructor
  · rintro ⟨Z, read, zetaAtS, hzeta, hmeas⟩
    exact ⟨Z, corrected_zeta_infinite_forces_nonzero_native_class
      G Z read zetaAtS hzeta hmeas⟩
  · rintro ⟨Z, hZ⟩
    obtain ⟨i, hi⟩ :=
      exists_nonzero_hodgeCoordinate (V := V) (H := H)
        (p := p) hZ
    let read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
      hodgeCoordinate i
    let amplitude : ℝ :=
      -((read (geometricHodgeClass G Z) : ℚ) : ℝ)
    refine ⟨Z, read, amplitude, ?_, ?_⟩
    · have hread :
        ((read (geometricHodgeClass G Z) : ℚ) : ℝ) ≠ 0 := by
        exact_mod_cast hi
      exact neg_ne_zero.mpr hread
    · rw [corrected_series_two_tsum]
      dsimp [amplitude]
      ring

#check HasNonzeroNativeClass
#check HasFreelyAdjustedZetaCertificate
#check freely_adjusted_zeta_certificate_iff_nonzero_native_class

#print axioms freely_adjusted_zeta_certificate_iff_nonzero_native_class

end GSTResearchZetaMeasurementAudit
