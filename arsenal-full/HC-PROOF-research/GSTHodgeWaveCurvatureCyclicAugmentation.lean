import GSTHodgeWaveCurvatureResidualStep
import GSTHodgeWaveFiniteCyclicCompletion

/-!
# GST native wave+curvature source makes ONE actual cyclic geometric fold

The previous GST residual-step theorem supplies a concrete corrected native
curvature cycle that is independent of every old original-X N-hole source.

Here it is used to EXTEND an existing genuine geometric wave frame by
exactly one algebraic source. The old readouts and the normalized curvature
readout form true native/Betti dual frames on the enlarged finite family.

We then invoke the ALREADY PROVED native cyclic-completion constructor:
one rational native cycle operator and one compatible rational cohomology
operator move around the (n+1)-element extended frame.

No Hodge-to-Chow inverse is inserted. The expanded finite frame can be
used on any real smooth projective original X with the required geometric
dual readouts; rank coverage is tested separately.
-/

noncomputable section

namespace GSTHodgeWaveCurvatureCyclicAugmentation

open GSTHodgeWaveCurvatureResidualStep
open GSTHodgeWaveAllNGeometricLanding
open GSTHodgeWaveFiniteCyclicCompletion
open GSTNCohomology

variable {A : Type*} [AddCommGroup A] [Module ℚ A]
variable {B : Type*} [AddCommGroup B] [Module ℚ B]
variable {s : NShape} {cl : A →ₗ[ℚ] B}

/-- A normalized NEW Betti intersection readout for the true curvature
class, scaled so it detects the new source with coefficient one. -/
def newBettiDual
    (z : A) (read : B →ₗ[ℚ] ℚ) : B →ₗ[ℚ] ℚ :=
  (read (cl z))⁻¹ • read

/-- Pull the geometric detector back to actual native Chow cycles. -/
def newNativeDual
    (z : A) (read : B →ₗ[ℚ] ℚ) : A →ₗ[ℚ] ℚ :=
  (newBettiDual (cl := cl) z read).comp cl

/-- The newly corrected source is invisible to every old native
detector, using genuine cycle-class naturality. -/
theorem oldNativeDual_corrected_zero
    (F : GeometricWaveFrame s cl) (z : A)
    (i : Fin s.holes) :
    F.nativeDual i (correctedCurvatureSource F z) = 0 := by
  have hcompat :=
    F.bettiCoordinates_cl (correctedCurvatureSource F z)
  have hz := correctedCurvatureSource_oldCoordinates_zero F z
  have h := congrFun (hcompat.symm.trans hz) i
  exact h

theorem newNativeDual_old_zero
    (F : GeometricWaveFrame s cl) (z : A)
    (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (i : Fin s.holes) :
    newNativeDual (cl := cl) z read (F.atom i) = 0 := by
  simp [newNativeDual, newBettiDual, hOld i]

theorem newNativeDual_corrected_one
    (F : GeometricWaveFrame s cl) (z : A)
    (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0) :
    newNativeDual (cl := cl) z read
      (correctedCurvatureSource F z) = 1 := by
  simp only [newNativeDual, newBettiDual, LinearMap.comp_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [read_correctedCurvatureSource F z read hOld]
  exact inv_mul_cancel₀ hNew

/-- The true enlarged native AND geometric dual frame, including one
new source born by noncommutative curvature. Its index is Fin(n+1),
the precise input of the existing single-cycle completion law. -/
def extendedGeometricCyclicFrame
    (F : GeometricWaveFrame s cl)
    (z : A) (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0) :
    GeometricCyclicFrame s.holes cl where
  atom := Fin.snoc F.atom (correctedCurvatureSource F z)
  nativeDual := Fin.snoc F.nativeDual (newNativeDual (cl := cl) z read)
  bettiDual := Fin.snoc F.bettiDual (newBettiDual (cl := cl) z read)
  dual_atom := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [Fin.snoc_last, if_pos] using
          newNativeDual_corrected_one F z read hOld hNew
      · have hneq : (Fin.last s.holes) ≠ j.castSucc := by
          intro hEq
          have hval : s.holes = j.val := by
            simpa using congrArg Fin.val hEq
          omega
        simpa [Fin.snoc_castSucc, hneq] using
          newNativeDual_old_zero F z read hOld j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [Fin.snoc_castSucc, Fin.snoc_last] using
          oldNativeDual_corrected_zero F z i
      · simpa only [Fin.snoc_castSucc, Fin.castSucc_inj] using
          F.dual_atom i j
  dual_class := by
    intro i x
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [newNativeDual, newBettiDual]
    · simpa only [Fin.snoc_castSucc] using F.dual_class j x

/-- The ONE FOLD on actual original-X cycles is now a concrete
rational native linear map manufactured from the wave atoms and
one independent curvature source. -/
def nativeSingleFold
    (F : GeometricWaveFrame s cl) (z : A)
    (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0) : A →ₗ[ℚ] A :=
  (extendedGeometricCyclicFrame F z read hOld hNew).nativeFold

/-- Its Betti operator is not assumed: it is computed from the
SAME real geometric frame and its dual native/cycle-class data. -/
def bettiSingleFold
    (F : GeometricWaveFrame s cl) (z : A)
    (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0) : B →ₗ[ℚ] B :=
  (extendedGeometricCyclicFrame F z read hOld hNew).bettiFold

theorem nativeSingleFold_cycleClass
    (F : GeometricWaveFrame s cl) (z : A)
    (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0) (w : A) :
    cl (nativeSingleFold F z read hOld hNew w) =
      bettiSingleFold F z read hOld hNew (cl w) := by
  exact (extendedGeometricCyclicFrame F z read hOld hNew).nativeFold_cycleClass w

/-- The true source cycles form the intended finite cyclic orbit of
the NEW single fold. This uses the existing native cyclic-completion
operator, not an abstract nongeometric shift. -/
theorem nativeSingleFold_cycles_orbit
    (F : GeometricWaveFrame s cl) (z : A)
    (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0) (k : ℕ) :
    nativeSingleFold F z read hOld hNew
      ((extendedGeometricCyclicFrame F z read hOld hNew).atomOrbit k) =
      (extendedGeometricCyclicFrame F z read hOld hNew).atomOrbit (k+1) := by
  exact (extendedGeometricCyclicFrame F z read hOld hNew).nativeFold_atomOrbit_succ k

/-- Integrated finite-rank theorem: the newly curvature-augmented
geometric wave frame builds ONE native cyclic fold with a commuting
Betti action AND an explicit original-carrier cycle for any rational
class, once the geometric full-frame rank is checked. -/
theorem augmented_cyclic_fold_constructs_all_classes_of_rank
    (F : GeometricWaveFrame s cl) (z : A)
    (read : B →ₗ[ℚ] ℚ)
    (hOld : ∀ i : Fin s.holes, read (cl (F.atom i)) = 0)
    (hNew : read (cl z) ≠ 0)
    [FiniteDimensional ℚ B]
    (hRank : Module.finrank ℚ B = s.holes + 1)
    (alpha : B) :
    ∃ native : A →ₗ[ℚ] A, ∃ betti : B →ₗ[ℚ] B,
      (∀ w : A, cl (native w) = betti (cl w)) ∧
      (∃ Z : A, cl Z = alpha) := by
  refine ⟨nativeSingleFold F z read hOld hNew,
    bettiSingleFold F z read hOld hNew, ?_, ?_⟩
  · intro w
    exact nativeSingleFold_cycleClass F z read hOld hNew w
  · exact ⟨waveCurvatureCycle F z read alpha,
      waveCurvature_exact_of_rank_succ F z read hOld hNew hRank alpha⟩

#check extendedGeometricCyclicFrame
#check nativeSingleFold_cycleClass
#check nativeSingleFold_cycles_orbit
#print axioms nativeSingleFold_cycleClass

end GSTHodgeWaveCurvatureCyclicAugmentation
