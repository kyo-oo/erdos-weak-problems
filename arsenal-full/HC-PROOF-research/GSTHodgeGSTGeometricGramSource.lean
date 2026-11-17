import GSTHodgeWaveAllNGeometricLanding
import Mathlib

/-!
# GST geometric source detector extraction from intersection Gram data

The previous GST all-N Wave I/II/CM native landing required independently
provided native AND Betti dual readouts.  Here the duals are constructed
from ONE fixed rational geometric pairing and an inverse matrix of
intersection numbers of actual native original-X algebraic cycles.

An invertible Gram certificate is stronger and more falsifiable than
declaring a detector that reads any unknown Hodge class at will:
the entries are the actual rational pairings of known algebraic cycles.

For primitive projective classes, the signed Hodge-Riemann pairing provides
a natural pairing candidate, subject to correct projective realization.
No universal source cycles are invented by this linear algebra.
-/

noncomputable section

namespace GSTHodgeGSTGeometricGramSource

open GSTHodgeWaveAllNGeometricLanding
open GSTNCohomology

variable {A : Type*} [AddCommGroup A] [Module ℚ A]
variable {B : Type*} [AddCommGroup B] [Module ℚ B]
variable {s : NShape} {cl : A →ₗ[ℚ] B}

/-- Native source cycles with one actual rational intersection/polarization
pairing, and a verified inverse of their finite geometric Gram matrix. -/
structure GeometricGramSource (s : NShape) (cl : A →ₗ[ℚ] B) where
  atom : Fin s.holes → A
  pairing : B →ₗ[ℚ] B →ₗ[ℚ] ℚ
  gramInverse : Matrix (Fin s.holes) (Fin s.holes) ℚ
  gram_inverse_identity :
    ∀ i j : Fin s.holes,
       ∑ k : Fin s.holes,
         gramInverse i k * (pairing (cl (atom k))) (cl (atom j)) =
         if i = j then 1 else 0

namespace GeometricGramSource

/-- The geometric readout is CALCULATED from the inverse Gram matrix. -/
def bettiDual (F : GeometricGramSource s cl)
    (i : Fin s.holes) : B →ₗ[ℚ] ℚ :=
  ∑ k : Fin s.holes,
    (F.gramInverse i k) • (F.pairing (cl (F.atom k)))

/-- The native readout is not an independent arbitrary field: it is
the Betti intersection functional evaluated on the actual cycle class. -/
def nativeDual (F : GeometricGramSource s cl)
    (i : Fin s.holes) : A →ₗ[ℚ] ℚ :=
  (F.bettiDual i).comp cl

/-- The finite Gram inverse forces all Kronecker duality relations. -/
theorem bettiDual_atom (F : GeometricGramSource s cl)
    (i j : Fin s.holes) :
    F.bettiDual i (cl (F.atom j)) =
      if i = j then 1 else 0 := by
  simp only [bettiDual, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  exact F.gram_inverse_identity i j

/-- Upgrade geometric Gram data into the FULL GST wave-native frame.
This removes a separate assumption of arbitrary native/Betti detectors. -/
def toGeometricWaveFrame (F : GeometricGramSource s cl) :
    GeometricWaveFrame s cl where
  atom := F.atom
  nativeDual := F.nativeDual
  bettiDual := F.bettiDual
  dual_atom := by
    intro i j
    exact F.bettiDual_atom i j
  dual_class := by
    intro i z
    rfl

/-- An actually supplied geometric Gram packet PROVES the exact
all-N wave source intertwining with its derived original-X fold. -/
theorem native_wave_intertwining
    (F : GeometricGramSource s cl)
    (u : GSTGraphV2CMWaveFusion.HoleWaveSignals s) :
    F.toGeometricWaveFrame.nativeWaveSource
        (GSTGraphV2WaveNShapeCompiler.shiftedNShapeFold s u) =
      F.toGeometricWaveFrame.nativeFold
        (F.toGeometricWaveFrame.nativeWaveSource u) :=
  F.toGeometricWaveFrame.nativeWaveSource_intertwines u

/-- If the geometric source count reaches the whole Betti fiber rank,
the ORIGINAL wave produces an actual native representative for EVERY
rational class via explicit inverse Gram readouts. -/
theorem full_rank_wave_native_class
    (F : GeometricGramSource s cl)
    [FiniteDimensional ℚ B]
    (hRank : Module.finrank ℚ B = s.holes)
    (alpha : B) :
    cl (F.toGeometricWaveFrame.nativeWaveSource
      (GSTHodgeWaveAllNHoleReadout.holeReadoutLift s
       (F.toGeometricWaveFrame.bettiCoordinates alpha))) = alpha := by
  -- A full-rank frame is a rational coordinate isomorphism.
  let W := F.toGeometricWaveFrame
  have hCoord : Function.Surjective W.bettiCoordinates := by
    intro v
    exact ⟨W.bettiCombination v, by
      have h := W.nativeCoordinates_nativeCombination v
      rw [← W.cl_nativeCombination] 
      simpa [W.bettiCoordinates_cl] using h⟩
  have hdim : Module.finrank ℚ B =
      Module.finrank ℚ (Fin s.holes → ℚ) := by
    simpa using hRank
  have hinj : Function.Injective W.bettiCoordinates :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hCoord
  have hright (b : B) :
      W.bettiCombination (W.bettiCoordinates b) = b := by
    apply hinj
    have hh : W.bettiCoordinates (W.bettiCombination (W.bettiCoordinates b))
       = W.bettiCoordinates b := by
      rw [← W.cl_nativeCombination, W.bettiCoordinates_cl,
        W.nativeCoordinates_nativeCombination]
    exact hh
  change cl (W.nativeCombination
      (GSTHodgeWaveAllNHoleReadout.holeReadout s
        (GSTHodgeWaveAllNHoleReadout.holeReadoutLift s
          (W.bettiCoordinates alpha)))) = alpha
  rw [GSTHodgeWaveAllNHoleReadout.holeReadout_lift,
    W.cl_nativeCombination]
  exact hright alpha

#check bettiDual_atom
#check toGeometricWaveFrame
#check full_rank_wave_native_class
#print axioms bettiDual_atom
#print axioms full_rank_wave_native_class

end GeometricGramSource
end GSTHodgeGSTGeometricGramSource
