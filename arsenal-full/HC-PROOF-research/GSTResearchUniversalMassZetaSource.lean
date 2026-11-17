import GSTResearchFixedZetaGeometricSource
import GSTClassicalHodgeLimitlessSpinePropagation

/-!
# Research GST: fixed corrected zeta source at EVERY weight from native mass

The first source construction proved a fixed corrected zeta(s=0)
measurement in codimension zero from a normalized fundamental cycle.

The EXISTING GST native-mass bridge is more powerful. Its kernel-mass
descent, nonzero base mass, and successor point-mass laws manufacture
a conserved rational cohomological charge in EVERY codimension and
a nonzero actual native projective spine there.

This theorem constructs, rather than freely assumes, a rational
Hodge coordinate functional normalized to 1/2 on that genuine
native spine. The author's CORRECTED index-dependent infinite
series has value -1 at x=y=2, so the FIXED analytic special scalar
-1/2 yields exactly +1/2 at EVERY weight.

All constructed objects are native algebraic cycles and Q-linear
cohomological readouts. Neither zeta scalar nor readout is chosen
after a prescribed Hodge target class.

CAUTION: NativeMassCycleClassBridge is a STRUCTURE WITH THREE
substantive geometric premises; its universal inhabitance has
not been proved in HC-PROOF. This theorem is valid for any such
certified bridge but is NOT an unconditional proof of the Hodge
conjecture or the bridge's existence.
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
open GSTClassicalHodgeLimitlessSpinePropagation
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTMathboxCorrectedZetaGeometry
open GSTMathboxCorrectedZetaInfinite
open GSTResearchFixedZetaGeometricSource

namespace GSTResearchUniversalMassZetaSource

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- Uniform source measurement constructed from the native mass
bridge's ACTUAL cohomology readout at every weight.
The native source is spineNativeTower G p (not an arbitrary
target-Hodge-class preimage), and the fixed -1/2 comes from
the user's corrected indexed infinite series at x=y=2. -/
theorem fixed_corrected_zeta_source_every_weight
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (p : Nat) :
    ∃ read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ,
      ((read (spineHodgeSeed G p) : ℚ) : ℝ) =
        (-1/2 : ℝ) * (∑' m : ℕ, indexedKernel 2 2 m) ∧
      spineHodgeSeed G p ≠ 0 := by
  let D : SpineTowerConservedCharge G := M.toConservedCharge G
  let mass0 : ℚ :=
    D.nativeRead 0 (codimensionZeroFundamentalCycle V)
  have hmass0 : mass0 ≠ 0 := D.base_ne_zero
  let baseRead : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
    (D.cohomologyRead p).comp
      (rationalHodgeSubspace (H.hodgeBigrading p)).subtype
  let read : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
    ((1/2 : ℚ) / mass0) • baseRead
  have hbase :
      baseRead (spineHodgeSeed G p) = mass0 := by
    change D.cohomologyRead p
      (spineHodgeSeed G p).1 =
        D.nativeRead 0 (codimensionZeroFundamentalCycle V)
    rw [← spineNativeTower_cycleClass G p]
    rw [D.cycleClass_read p (spineNativeTower G p)]
    exact D.nativeRead_spineNativeTower p
  have hhalf :
      read (spineHodgeSeed G p) = 1/2 := by
    dsimp [read]
    simp [hbase, div_mul_cancel₀ _ hmass0]
  refine ⟨read, ?_, D.spineHodgeSeed_ne_zero p⟩
  rw [fixed_zetazero_corrected_scalar]
  simpa using congrArg (fun q : ℚ => (q : ℝ)) hhalf

#check fixed_corrected_zeta_source_every_weight
#print axioms fixed_corrected_zeta_source_every_weight

end GSTResearchUniversalMassZetaSource
