import GSTClassicalHodgeArsenalOrbitSaturation
import GSTClassicalHodgeAtomicAnnihilator
import GSTClassicalHodgeAtomicDefectDuality
import GSTClassicalHodgeRankFreeArsenalIrreducibility

/-!
# GST CLASSICAL HODGE — DUAL ARSENAL EXTINCTION

The primal limitless theorem says every nonzero Hodge state is cyclic for the
full GST matrix-unit arsenal.  Dually, a rational detector which vanishes on
the complete one-step arsenal orbit of one nonzero state must vanish on the
entire genuine Hodge fiber.

This is the natural contradiction engine for an atomic separator.  A separator
already vanishes on every genuinely algebraic point-cycle class.  Therefore,
if the arsenal orbit of one nonzero algebraic seed stays algebraic, the
separator vanishes on a spanning set of the Hodge fiber and hence cannot
detect any Hodge direction.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeAtomicAnnihilator
open GSTClassicalHodgeArsenalOrbitSaturation
open GSTClassicalHodgeRankFreeArsenalIrreducibility

namespace GSTClassicalHodgeDualArsenalExtinction

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- Restrict an ambient cohomology functional to the genuine Hodge fiber. -/
noncomputable def restrictToHodge
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
  ell.comp (rationalHodgeSubspace (H.hodgeBigrading p)).subtype

/-- A Hodge functional that kills the one-step arsenal orbit of one nonzero
state kills the whole Hodge fiber. -/
theorem hodgeFunctional_eq_zero_of_orbit
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (horbit : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ell (hodgeMatrixUnit i j alpha) = 0) :
    ell = 0 := by
  have hspan : arsenalOrbitSpan alpha ≤ LinearMap.ker ell := by
    apply Submodule.span_le.mpr
    rintro x ⟨ij, rfl⟩
    exact horbit ij.1 ij.2
  have htop := arsenalOrbitSpan_eq_top alpha halpha
  apply LinearMap.ext
  intro beta
  have hbeta : beta ∈ arsenalOrbitSpan alpha := by
    rw [htop]
    trivial
  exact hspan hbeta

/-- Elementwise form of dual extinction. -/
theorem hodgeFunctional_vanishes_of_orbit
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0)
    (ell : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (horbit : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ell (hodgeMatrixUnit i j alpha) = 0) :
    ∀ beta : ClassicalHodgeFiber V H p, ell beta = 0 := by
  have hz := hodgeFunctional_eq_zero_of_orbit alpha halpha ell horbit
  intro beta
  rw [hz]
  rfl

/-- An ambient atomic separator is extinguished on the whole Hodge fiber as
soon as the orbit of one nonzero algebraic seed remains in the atomic span. -/
theorem atomicSeparator_vanishes_of_algebraic_orbit
    (seed : ClassicalHodgeFiber V H p)
    (hseed0 : seed ≠ 0)
    (horbit : ∀ i j : ClassicalHodgeBasisIndex V H p,
      (hodgeMatrixUnit i j seed).1 ∈
        pointCycleClassSpan p (H.cycleClass p))
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (hell : AnnihilatesPointCycleClasses p (H.cycleClass p) ell) :
    ∀ beta : ClassicalHodgeFiber V H p, ell beta.1 = 0 := by
  have hspanKer : pointCycleClassSpan p (H.cycleClass p) ≤ LinearMap.ker ell :=
    (annihilatesPointCycles_iff_atomicSpan_le_ker
      p (H.cycleClass p) ell).mp hell
  let ellH := restrictToHodge (V := V) (H := H) (p := p) ell
  have horbitZero : ∀ i j : ClassicalHodgeBasisIndex V H p,
      ellH (hodgeMatrixUnit i j seed) = 0 := by
    intro i j
    exact hspanKer (horbit i j)
  have hz := hodgeFunctional_eq_zero_of_orbit seed hseed0 ellH horbitZero
  intro beta
  have hbeta := LinearMap.congr_fun hz beta
  exact hbeta

/-- **DUAL ONE-SEED HODGE CROWN.**  If every nonzero Hodge weight contains one
seed whose full GST orbit is algebraic, then no atomic separator exists and
the exact Stage-2G statement follows. -/
theorem bigradedBettiHodge_of_dualArsenalExtinction
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hseed : ∀ p : Nat,
      ∀ alpha : ClassicalHodgeFiber V H p, alpha ≠ 0 →
        ∃ seed : ClassicalHodgeFiber V H p,
          seed ≠ 0 ∧
          ∀ i j : ClassicalHodgeBasisIndex V H p,
            (hodgeMatrixUnit i j seed).1 ∈
              pointCycleClassSpan p (H.cycleClass p)) :
    BigradedBettiHodgeStatement V H := by
  apply (bigradedBettiHodgeStatement_iff_no_atomic_separator V H).mpr
  intro p ell hell alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  by_cases hzero : alphaH = 0
  · have ha0 : alpha = 0 := congrArg Subtype.val hzero
    subst ha0
    exact map_zero ell
  · obtain ⟨seed, hseed0, horbit⟩ := hseed p alphaH hzero
    exact atomicSeparator_vanishes_of_algebraic_orbit
      seed hseed0 horbit ell hell alphaH

#check restrictToHodge
#check hodgeFunctional_eq_zero_of_orbit
#check hodgeFunctional_vanishes_of_orbit
#check atomicSeparator_vanishes_of_algebraic_orbit
#check bigradedBettiHodge_of_dualArsenalExtinction

#print axioms hodgeFunctional_eq_zero_of_orbit
#print axioms atomicSeparator_vanishes_of_algebraic_orbit
#print axioms bigradedBettiHodge_of_dualArsenalExtinction

end GSTClassicalHodgeDualArsenalExtinction
