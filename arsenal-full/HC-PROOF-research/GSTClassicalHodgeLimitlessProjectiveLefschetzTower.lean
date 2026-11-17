import GSTClassicalHodgePrincipalCutSuccessorOperator
import GSTClassicalHodgeCodimensionZeroFundamentalCycle
import GSTClassicalHodgeLimitlessCosmicLefschetzPropagation
import GSTClassicalHodgeSchemeCodimensionStalk
import GSTClassicalHodgeCrossWeightNativePropagation

/-!
# GST CLASSICAL HODGE — LIMITLESS PROJECTIVE LEFSCHETZ TOWER

The projective and cosmic sides now carry the same unbounded weight index.

On the geometric side, start with the canonical codimension-zero fundamental
cycle and repeatedly apply the source-dependent principal-cut successor
operator.  This produces a genuine native codimension-p cycle for every `p`
without inserting Hodge data into the construction.

On the GST side, start with the genuine cosmic Hodge generator at weight zero
and evolve under the global Lefschetz operator.  At weight `p`, time `2p`
produces the exact nonzero central-binomial coefficient at `(p,p)`.

This file packages the two towers in parallel.  The later cycle-class
comparison only has to identify one geometric principal-cut step with the
corresponding cosmic Lefschetz step; all higher steps are already generated
recursively on both sides.
-/

set_option maxHeartbeats 60000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeLimitlessProjectiveLefschetzTower

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTClassicalHodgePrincipalCutSuccessorOperator
open GSTClassicalHodgeCodimensionZeroFundamentalCycle
open GSTClassicalHodgeLimitlessCosmicLefschetzPropagation
open GSTClassicalHodgeCrossWeightNativePropagation
open GSTWorldCosmology
open GSTUniversalLefschetzCosmology
open GSTDimensionFreeHodgeDiagonal

/-- Iterated native principal-cut transport from codimension `p` through `d`
steps. -/
noncomputable def nativeCutIterate
    (V : SmoothProjectiveComplexScheme) :
    (p d : Nat) →
      codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X (p + d)
  | p, 0 => by simpa using
      (LinearMap.id : codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p)
  | p, d + 1 => by
      have hprev := nativeCutIterate V p d
      have hnext := successorNativeOperator V (p + d)
      have hcomp := hnext.comp hprev
      rw [show p + d + 1 = p + (d + 1) from Nat.add_assoc p d 1] at hcomp
      exact hcomp

@[simp]
theorem nativeCutIterate_zero
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    nativeCutIterate V p 0 = LinearMap.id := by
  rfl

/-- Successor recursion law. -/
theorem nativeCutIterate_succ
    (V : SmoothProjectiveComplexScheme)
    (p d : Nat) :
    nativeCutIterate V p (d+1) =
      (successorNativeOperator V (p+d)).comp
        (nativeCutIterate V p d) := by
  simp [nativeCutIterate, Nat.add_assoc]

/-- Canonical projective native tower: the p-th state is obtained from the
component fundamental cycle by p recursive principal cuts. -/
noncomputable def projectiveCutTower
    (V : SmoothProjectiveComplexScheme) :
    (p : Nat) → codimensionCycles V.X p
  | 0 => codimensionZeroFundamentalCycle V
  | p+1 => successorNativeOperator V p (projectiveCutTower V p)

@[simp]
theorem projectiveCutTower_zero
    (V : SmoothProjectiveComplexScheme) :
    projectiveCutTower V 0 = codimensionZeroFundamentalCycle V := rfl

/-- Exact recursive projective tower law. -/
theorem projectiveCutTower_succ
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    projectiveCutTower V (p+1) =
      successorNativeOperator V p (projectiveCutTower V p) := rfl

/-- Every level of the projective tower is an actual native codimension-p
algebraic cycle. -/
theorem projectiveCutTower_native
    (V : SmoothProjectiveComplexScheme)
    (p : Nat) :
    (projectiveCutTower V p : AlgebraicCycle V.X ℚ) ∈
      codimensionCycles V.X p :=
  (projectiveCutTower V p).2

/-- The corresponding completed-cosmos Lefschetz tower from the weight-zero
Hodge generator. -/
def cosmicLefschetzTower (p : Nat) : CompletedCosmos :=
  (cosmicLefschetz^(2*p)) (cosmicDiagonalClass 0)

/-- Exact diagonal coefficient of the cosmic tower. -/
theorem cosmicLefschetzTower_diagonal
    (p : Nat) :
    cosmicLefschetzTower p (p,p) = ((2*p).choose p : ℤ) := by
  simpa [cosmicLefschetzTower] using
    cosmicLefschetz_diagonal_coefficient 0 p

/-- The diagonal coefficient never vanishes. -/
theorem cosmicLefschetzTower_diagonal_ne_zero
    (p : Nat) :
    cosmicLefschetzTower p (p,p) ≠ 0 := by
  simpa [cosmicLefschetzTower] using
    cosmicLefschetz_target_coefficient_ne_zero 0 p (Nat.zero_le p)

/-- Project the completed cosmic tower to its pure target weight. -/
def cosmicPureTowerTarget (p : Nat) : CompletedCosmos :=
  completedDiagonalProjector p (cosmicLefschetzTower p)

/-- The projected cosmic tower is exactly the central-binomial multiple of the
canonical Hodge generator at weight `p`. -/
theorem cosmicPureTowerTarget_exact
    (p : Nat) :
    cosmicPureTowerTarget p =
      ((2*p).choose p : ℤ) • (fun c => cosmicDiagonalClass p c) := by
  simpa [cosmicPureTowerTarget, cosmicLefschetzTower] using
    completedProjector_cosmicLefschetz_generator 0 p (Nat.zero_le p)

/-- Rational cross-weight coefficient seen by the classical propagation layer
is exactly the coefficient of this true limitless tower. -/
theorem classical_limitlessScalar_is_tower_coefficient
    (p : Nat) :
    limitlessLefschetzScalar 0 p = (cosmicLefschetzTower p (p,p) : ℚ) := by
  simpa [cosmicLefschetzTower] using
    limitlessLefschetzScalar_eq_cosmic_coefficient 0 p (Nat.zero_le p)

/-- A single-step comparison law at every weight is sufficient to identify the
cycle class of every recursively generated projective tower level. -/
theorem cycleClass_projectiveCutTower_of_step
    {Coh : Nat → Type*}
    [∀ p, AddCommGroup (Coh p)] [∀ p, Module ℚ (Coh p)]
    (V : SmoothProjectiveComplexScheme)
    (cl : ∀ p, codimensionCycles V.X p →ₗ[ℚ] Coh p)
    (L : ∀ p, Coh p →ₗ[ℚ] Coh (p+1))
    (hstep : ∀ p Z,
      cl (p+1) (successorNativeOperator V p Z) = L p (cl p Z)) :
    ∀ p,
      cl p (projectiveCutTower V p) =
        (Nat.rec (cl 0 (codimensionZeroFundamentalCycle V))
          (fun n x => L n x) p) := by
  intro p
  induction p with
  | zero => simp [projectiveCutTower]
  | succ p ih =>
      rw [projectiveCutTower_succ]
      rw [hstep]
      simpa using congrArg (fun x => L p x) ih

/-- Limitless projective/cosmic tower crown. -/
theorem limitless_projective_lefschetz_tower_crown
    (V : SmoothProjectiveComplexScheme) :
    (∀ p, (projectiveCutTower V p : AlgebraicCycle V.X ℚ) ∈
      codimensionCycles V.X p)
    ∧ (∀ p, cosmicLefschetzTower p (p,p) = ((2*p).choose p : ℤ))
    ∧ (∀ p, cosmicLefschetzTower p (p,p) ≠ 0)
    ∧ (∀ p, limitlessLefschetzScalar 0 p =
      (cosmicLefschetzTower p (p,p) : ℚ)) := by
  exact ⟨projectiveCutTower_native V,
    cosmicLefschetzTower_diagonal,
    cosmicLefschetzTower_diagonal_ne_zero,
    classical_limitlessScalar_is_tower_coefficient⟩

#check nativeCutIterate
#check projectiveCutTower
#check projectiveCutTower_succ
#check cosmicLefschetzTower
#check cosmicLefschetzTower_diagonal
#check cosmicPureTowerTarget
#check cycleClass_projectiveCutTower_of_step
#check limitless_projective_lefschetz_tower_crown

#print axioms projectiveCutTower_succ
#print axioms cosmicLefschetzTower_diagonal
#print axioms cosmicPureTowerTarget_exact
#print axioms cycleClass_projectiveCutTower_of_step
#print axioms limitless_projective_lefschetz_tower_crown

end GSTClassicalHodgeLimitlessProjectiveLefschetzTower
