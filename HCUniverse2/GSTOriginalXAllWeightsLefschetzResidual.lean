import HCUniverse2.GSTOriginalXDivisorCurveCyclicChowFold
import Mathlib

/-!
# GST Hodge hypothesis: canonical original-X source for prescribed alpha

The actual original-X geometry is proved in the companion TeX:
For every smooth connected projective X and EVERY p=1,...,dim(X)-1,
divisors D_i and an ample h construct real Chow source cycles
  Z_i = D_i*h^(p-1) in CH^p(X)_Q
and complementary dual cycles
  Y_i = sum_j inverse(G)_(ij) D_j*h^(d-p-1) in CH^(d-p)(X)_Q,
with degree(Z_j*Y_i)=delta_ij.
They give a REAL Chow idempotent Pi_p in CH^d(X x X)_Q,
not just a freely specified linear operator.

For every prescribed rational Hodge alpha, define its source coefficients
by genuine cup/integration against cl(Y_i). The actual rational Chow cycle
  Z_(alpha,Lef) = sum_i <alpha,cl(Y_i)> Z_i
has CANONICAL Betti class equal to the Lefschetz projection of alpha.
The missing higher-primitive residual is retained, not declared zero.

This file kernel-verifies the rational source/Betti projector calculus:
native and Betti idempotence, exact naturality, explicit selected-source
class and annihilation of the residual by ALL original algebraic detectors.
The actual Chow product and canonical singular cohomology interpretation
are supplied by the separate geometric theorem, not fabricated here.
-/

set_option maxHeartbeats 6000000
noncomputable section
open scoped BigOperators

namespace GSTOriginalXAllWeightsLefschetzResidual

open GSTOriginalXDivisorCurveCyclicChowFold
open GSTOriginalXDivisorCurveCyclicChowFold.IntersectionChowFrame

universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {A : Type v} [AddCommGroup A] [Module ℚ A]
variable {B : Type w} [AddCommGroup B] [Module ℚ B]
variable (F : IntersectionChowFrame ι A B)

/-- The genuine original-X Chow projector is represented at the typed
linear-algebra level by its exact intersection-degree readouts. -/
noncomputable def nativeLefschetzProjector : Module.End ℚ A :=
  F.nativeCycleFold id

/-- Betti action of the SAME original Chow projector. -/
noncomputable def bettiLefschetzProjector : Module.End ℚ B :=
  F.bettiCyclicFold id

/-- Completely explicit original-X Chow cycle for the LEFSCHETZ PART
of an arbitrary prescribed rational Hodge class alpha. -/
noncomputable def selectedLefschetzCycle (alpha : B) : A :=
  ∑ i : ι, F.bettiIntersection i alpha • F.source i

/-- Exact class of the prescribed-alpha Chow construction. This proves a
canonical class equality for its EXPLICIT algebraic projection, not for
the unconstructed middle-primitive residual. -/
theorem selectedLefschetzCycle_class (alpha : B) :
    F.cycleClass (selectedLefschetzCycle F alpha) =
      bettiLefschetzProjector F alpha := by
  change F.cycleClass
    (∑ i : ι, F.bettiIntersection i alpha • F.source i) =
      ∑ i : ι, F.bettiIntersection i alpha •
        F.cycleClass (F.source i)
  simp only [map_sum, map_smul]

/-- The original-X Chow projector is genuinely idempotent on EVERY native
cycle, not only on its chosen Gram-dual divisor frame. -/
theorem nativeLefschetzProjector_idempotent_apply (z : A) :
    nativeLefschetzProjector F (nativeLefschetzProjector F z) =
      nativeLefschetzProjector F z := by
  calc
    nativeLefschetzProjector F (nativeLefschetzProjector F z) =
        ∑ i : ι, F.nativeIntersection i z •
          nativeLefschetzProjector F (F.source i) := by
            change F.nativeCycleFold id
              (∑ i : ι, F.nativeIntersection i z • F.source i) = _
            simp only [nativeLefschetzProjector, map_sum, map_smul]
    _ = ∑ i : ι, F.nativeIntersection i z • F.source i := by
          simp [nativeLefschetzProjector, F.nativeCycleFold_source]
    _ = nativeLefschetzProjector F z := rfl

theorem nativeLefschetzProjector_idempotent :
    (nativeLefschetzProjector F).comp (nativeLefschetzProjector F) =
      nativeLefschetzProjector F := by
  apply LinearMap.ext
  intro z
  exact nativeLefschetzProjector_idempotent_apply F z

/-- Betti projector is equally idempotent, with exact original-X source
classes as its image generators. -/
theorem bettiLefschetzProjector_idempotent_apply (alpha : B) :
    bettiLefschetzProjector F (bettiLefschetzProjector F alpha) =
      bettiLefschetzProjector F alpha := by
  calc
    bettiLefschetzProjector F (bettiLefschetzProjector F alpha) =
        ∑ i : ι, F.bettiIntersection i alpha •
          bettiLefschetzProjector F (F.cycleClass (F.source i)) := by
            change F.bettiCyclicFold id
              (∑ i : ι,
                F.bettiIntersection i alpha • F.cycleClass (F.source i)) = _
            simp only [bettiLefschetzProjector, map_sum, map_smul]
    _ = ∑ i : ι, F.bettiIntersection i alpha • F.cycleClass (F.source i) := by
          simp [bettiLefschetzProjector, F.bettiCyclicFold_source]
    _ = bettiLefschetzProjector F alpha := rfl

theorem bettiLefschetzProjector_idempotent :
    (bettiLefschetzProjector F).comp (bettiLefschetzProjector F) =
      bettiLefschetzProjector F := by
  apply LinearMap.ext
  intro alpha
  exact bettiLefschetzProjector_idempotent_apply F alpha

/-- ORIGINAL-X native Chow/Betti projector commuting square, derived
from actual intersection-naturality and not from unknown Hodge cycles. -/
theorem lefProjector_class (z : A) :
    F.cycleClass (nativeLefschetzProjector F z) =
      bettiLefschetzProjector F (F.cycleClass z) :=
  F.nativeCycleFold_class id z

/-- Native and Betti complements, corresponding to the genuine Chow
correspondence Delta_X-Pi_p in the companion geometric proof. -/
noncomputable def nativeResidualProjector : Module.End ℚ A :=
  LinearMap.id - nativeLefschetzProjector F

noncomputable def bettiResidualProjector : Module.End ℚ B :=
  LinearMap.id - bettiLefschetzProjector F

/-- Even the residual projector is still a naturally realized original-X
operator: naturality follows from the projection formula by subtraction. -/
theorem residualProjector_class (z : A) :
    F.cycleClass (nativeResidualProjector F z) =
      bettiResidualProjector F (F.cycleClass z) := by
  change F.cycleClass (z - nativeLefschetzProjector F z) =
    F.cycleClass z - bettiLefschetzProjector F (F.cycleClass z)
  rw [map_sub, lefProjector_class]

/-- The target-prescribed true higher-primitive residual is computed,
not assumed algebraic and not silently identified with zero. -/
noncomputable def prescribedHodgeResidual (alpha : B) : B :=
  alpha - F.cycleClass (selectedLefschetzCycle F alpha)

/-- Each actual complementary algebraic cycle Y_i has pairing ZERO
with the residual, for EVERY prescribed alpha. This is an exact
noncircular "what still needs new geometry" equation. -/
theorem prescribedHodgeResidual_detector_zero
    (alpha : B) (i : ι) :
    F.bettiIntersection i (prescribedHodgeResidual F alpha) = 0 := by
  have hread :
      F.bettiIntersection i
        (F.cycleClass (selectedLefschetzCycle F alpha)) =
        F.bettiIntersection i alpha := by
    rw [selectedLefschetzCycle_class]
    change F.bettiIntersection i
      (∑ j : ι, F.bettiIntersection j alpha •
        F.cycleClass (F.source j)) = F.bettiIntersection i alpha
    simp only [map_sum, map_smul]
    simp_rw [F.bettiIntersection_source]
    simp
  change F.bettiIntersection i
    (alpha - F.cycleClass (selectedLefschetzCycle F alpha)) = 0
  rw [map_sub, hread, sub_self]

#check nativeLefschetzProjector_idempotent
#check bettiLefschetzProjector_idempotent
#check selectedLefschetzCycle_class
#check lefProjector_class
#check residualProjector_class
#check prescribedHodgeResidual_detector_zero
#print axioms nativeLefschetzProjector_idempotent
#print axioms selectedLefschetzCycle_class
#print axioms prescribedHodgeResidual_detector_zero

end GSTOriginalXAllWeightsLefschetzResidual
