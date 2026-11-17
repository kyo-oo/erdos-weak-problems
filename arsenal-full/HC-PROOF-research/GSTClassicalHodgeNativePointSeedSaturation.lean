import GSTClassicalHodgeGeometryFirstTwoGenerator
import GSTClassicalHodgeAtomicSpan
import GSTClassicalHodgeRankFreeArsenalIrreducibility
import GSTNativeCodimensionCyclePresentation

/-!
# GST CLASSICAL HODGE — NATIVE POINT-SEED SATURATION

The rank-free limitless arsenal does not need an abstract seed object.  One
actual codimension-p generic point of the smooth projective scheme is enough,
provided its genuine cycle class is a nonzero rational (p,p) class.

This file turns that concrete native point cycle into the nonzero algebraic
Hodge seed required by the unrestricted irreducibility theorem.  Combined with
the geometry-first two-generator theorem, the whole genuine Hodge fiber is
then forced into the actual cycle-class range.

The purpose of this layer is to keep the remaining geometric construction
literal: produce one actual point cycle and prove its standard cycle-class
properties.  No basis representative, address chart, or Hodge-surjectivity
hypothesis occurs here.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan
open GSTClassicalHodgeRankFreeArsenalIrreducibility
open GSTClassicalHodgeGeometryFirstTwoGenerator
open GSTNativeCodimensionCyclePresentation

namespace GSTClassicalHodgeNativePointSeedSaturation

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- A concrete geometric seed is one genuine codimension-p point whose native
cycle class is a nonzero rational Hodge class. -/
structure NativePointHodgeSeed
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  point : CodimensionPoint V.X p
  class_is_hodge :
    H.cycleClass p (codimensionPointCycle V.X p point) ∈
      rationalHodgeSubspace (H.hodgeBigrading p)
  class_ne_zero :
    H.cycleClass p (codimensionPointCycle V.X p point) ≠ 0

namespace NativePointHodgeSeed

/-- The genuine Hodge vector carried by the point seed. -/
noncomputable def hodgeClass
    (S : NativePointHodgeSeed V H p) : ClassicalHodgeFiber V H p :=
  ⟨H.cycleClass p (codimensionPointCycle V.X p S.point), S.class_is_hodge⟩

/-- The Hodge seed is nonzero. -/
theorem hodgeClass_ne_zero
    (S : NativePointHodgeSeed V H p) : S.hodgeClass ≠ 0 := by
  intro h
  have hval := congrArg Subtype.val h
  exact S.class_ne_zero (by simpa [hodgeClass] using hval)

/-- The seed is algebraic by construction: it is literally the class of one
native point cycle. -/
theorem hodgeClass_mem_algebraicHodgeSubspace
    (S : NativePointHodgeSeed V H p) :
    S.hodgeClass ∈ AlgebraicHodgeSubspace V H p := by
  rw [mem_AlgebraicHodgeSubspace_iff]
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p]
  exact ⟨codimensionPointCycle V.X p S.point, rfl⟩

/-- One concrete native point seed makes the algebraic Hodge subspace
nontrivial. -/
theorem algebraicHodgeSubspace_ne_bot
    (S : NativePointHodgeSeed V H p) :
    AlgebraicHodgeSubspace V H p ≠ ⊥ := by
  intro hbot
  have hmem := S.hodgeClass_mem_algebraicHodgeSubspace
  rw [hbot] at hmem
  have hz : S.hodgeClass = 0 := by simpa using hmem
  exact S.hodgeClass_ne_zero hz

/-- Geometry-first realization of the two primitive GST operators for every
ordered basis pair, together with one genuine point seed, saturates the whole
rational Hodge fiber. -/
theorem algebraicHodgeSubspace_eq_top
    (S : NativePointHodgeSeed V H p)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    AlgebraicHodgeSubspace V H p = ⊤ := by
  exact algebraicHodgeSubspace_eq_top_of_geometryFirstTwoGenerators
    R S.algebraicHodgeSubspace_ne_bot

/-- Every genuine rational (p,p) class has an actual native codimension-p
cycle once the one-point seed and geometry-first primitive operators are
constructed. -/
theorem every_hodge_class_has_native_cycle
    (S : NativePointHodgeSeed V H p)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  have htop := S.algebraicHodgeSubspace_eq_top R
  have halg : alpha ∈ AlgebraicHodgeSubspace V H p := by
    rw [htop]
    trivial
  have hatomic : alpha.1 ∈ pointCycleClassSpan p (H.cycleClass p) := halg
  rw [← smoothProjective_cycleClass_range_eq_atomic_span V H p] at hatomic
  exact hatomic

/-- Weight-p form of the exact Stage-2G target. -/
theorem hodge_weight_le_cycleClass_range
    (S : NativePointHodgeSeed V H p)
    (R : ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha halpha
  let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
  exact S.every_hodge_class_has_native_cycle R alphaH

end NativePointHodgeSeed

/-- **ACTIVE-FIBER GEOMETRY-FIRST POINT SATURATION.**
A geometric native point is needed only at a weight with a nonzero rational
Hodge fiber.  For a zero fiber, the zero native cycle realizes every member,
without supplying a fictitious codimension point or nonzero seed.

The live-weight witnesses remain literal native codimension points and genuine
geometry-first operators; no algebraicity or surjectivity conclusion is placed
in the hypotheses. -/
theorem bigradedBettiHodge_of_active_nativePointSeeds
    (seeds :
      ∀ (p : Nat),
        (∃ alpha : ClassicalHodgeFiber V H p, alpha ≠ 0) →
          NativePointHodgeSeed V H p)
    (R :
      ∀ (p : Nat)
        (hp : ∃ alpha : ClassicalHodgeFiber V H p, alpha ≠ 0),
      ∀ i j : ClassicalHodgeBasisIndex V H p,
        GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    BigradedBettiHodgeStatement V H := by
  classical
  intro p alpha halpha
  by_cases hp : ∃ beta : ClassicalHodgeFiber V H p, beta ≠ 0
  · exact (seeds p hp).hodge_weight_le_cycleClass_range (R p hp) halpha
  · have halpha_zero : alpha = 0 := by
      by_contra hne
      apply hp
      refine ⟨⟨alpha, halpha⟩, ?_⟩
      intro h
      exact hne (by simpa using congrArg Subtype.val h)
    exact ⟨0, by simp [halpha_zero]⟩

/-- A concrete native point seed and geometry-first two-generator realization
in every weight close the exact Stage-2G Hodge statement. -/
theorem bigradedBettiHodge_of_nativePointSeeds
    (seeds : ∀ p : Nat, NativePointHodgeSeed V H p)
    (R : ∀ p : Nat, ∀ i j : ClassicalHodgeBasisIndex V H p,
      GeometryFirstTwoGenerator (V := V) (H := H) i j) :
    BigradedBettiHodgeStatement V H := by
  exact bigradedBettiHodge_of_active_nativePointSeeds
    (fun p _ => seeds p) (fun p _ => R p)

#check NativePointHodgeSeed
#check NativePointHodgeSeed.hodgeClass
#check NativePointHodgeSeed.hodgeClass_mem_algebraicHodgeSubspace
#check NativePointHodgeSeed.algebraicHodgeSubspace_ne_bot
#check NativePointHodgeSeed.algebraicHodgeSubspace_eq_top
#check NativePointHodgeSeed.every_hodge_class_has_native_cycle
#check NativePointHodgeSeed.hodge_weight_le_cycleClass_range
#check bigradedBettiHodge_of_active_nativePointSeeds
#check bigradedBettiHodge_of_nativePointSeeds

#print axioms NativePointHodgeSeed.hodgeClass_mem_algebraicHodgeSubspace
#print axioms NativePointHodgeSeed.algebraicHodgeSubspace_eq_top
#print axioms NativePointHodgeSeed.every_hodge_class_has_native_cycle
#print axioms bigradedBettiHodge_of_active_nativePointSeeds
#print axioms bigradedBettiHodge_of_nativePointSeeds

end GSTClassicalHodgeNativePointSeedSaturation
