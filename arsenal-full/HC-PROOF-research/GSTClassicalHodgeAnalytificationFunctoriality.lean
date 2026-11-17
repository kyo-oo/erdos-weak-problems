import GSTGeometricRealizationStage2F
import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# GST CLASSICAL HODGE — ANALYTIFICATION FUNCTORIALITY

Stage 2F fixes the rational singular-cohomology carrier but stores only the
analytification space and its identification with C-valued scheme points.
For the projective correspondence attack we also need the morphism-level
transport that is standard for a genuine analytification.

This module first constructs the underlying action of a C-scheme endomorphism
on actual complex points with no topological assumption.  It then transports
that action through the Stage-2F point equivalence and packages the precise
continuity law needed to obtain a TopCat endomorphism.  Identity and
composition are proved at the underlying-point level.

No algebraic-cycle or Hodge conclusion occurs here.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F

namespace GSTClassicalHodgeAnalytificationFunctoriality

variable {V : SmoothProjectiveComplexScheme}

/-- Endomorphisms of the projective scheme over the fixed complex base. -/
structure ComplexSchemeEndomorphism
    (V : SmoothProjectiveComplexScheme) where
  hom : V.X ⟶ V.X
  over_base : hom ≫ V.structureMap = V.structureMap

namespace ComplexSchemeEndomorphism

instance : Coe (ComplexSchemeEndomorphism V) (V.X ⟶ V.X) :=
  ⟨fun f => f.hom⟩

/-- Identity C-scheme endomorphism. -/
def id (V : SmoothProjectiveComplexScheme) : ComplexSchemeEndomorphism V where
  hom := 𝟙 V.X
  over_base := by simp

/-- Composition of C-scheme endomorphisms. -/
def comp (f g : ComplexSchemeEndomorphism V) : ComplexSchemeEndomorphism V where
  hom := f.hom ≫ g.hom
  over_base := by
    rw [Category.assoc, g.over_base, f.over_base]

/-- Actual action on C-valued points by postcomposition. -/
def complexPointMap
    (f : ComplexSchemeEndomorphism V) : ComplexPoint V → ComplexPoint V :=
  fun x => ⟨x.1 ≫ f.hom, by
    rw [Category.assoc, f.over_base]
    exact x.2⟩

@[simp]
theorem complexPointMap_id (x : ComplexPoint V) :
    complexPointMap (id V) x = x := by
  apply Subtype.ext
  simp [complexPointMap, id]

@[simp]
theorem complexPointMap_comp
    (f g : ComplexSchemeEndomorphism V)
    (x : ComplexPoint V) :
    complexPointMap (comp f g) x =
      complexPointMap g (complexPointMap f x) := by
  apply Subtype.ext
  simp [complexPointMap, comp, Category.assoc]

end ComplexSchemeEndomorphism

variable (A : AnalytificationData V)

/-- Underlying self-map of the supplied analytification point set obtained by
transporting the genuine C-point action through `pointsEquiv`. -/
def transportedPointMap
    (f : ComplexSchemeEndomorphism V) : A.space → A.space :=
  fun x => A.pointsEquiv
    (ComplexSchemeEndomorphism.complexPointMap f (A.pointsEquiv.symm x))

@[simp]
theorem transportedPointMap_id (x : A.space) :
    transportedPointMap A (ComplexSchemeEndomorphism.id V) x = x := by
  simp [transportedPointMap]

@[simp]
theorem transportedPointMap_comp
    (f g : ComplexSchemeEndomorphism V)
    (x : A.space) :
    transportedPointMap A (ComplexSchemeEndomorphism.comp f g) x =
      transportedPointMap A g (transportedPointMap A f x) := by
  simp [transportedPointMap,
    ComplexSchemeEndomorphism.complexPointMap_comp]

/-- A scheme endomorphism whose transported action is continuous for the
supplied analytification topology.  This is the exact morphism-level property
that a genuine analytification functor supplies. -/
structure AnalyticEndomorphism where
  algebraic : ComplexSchemeEndomorphism V
  continuous_toFun : Continuous (transportedPointMap A algebraic)

namespace AnalyticEndomorphism

/-- The corresponding actual morphism in `TopCat`. -/
noncomputable def toTopCatHom
    (f : AnalyticEndomorphism A) : A.space ⟶ A.space :=
  ConcreteCategory.ofHom (C := TopCat)
    (ContinuousMap.mk (transportedPointMap A f.algebraic) f.continuous_toFun)

/-- Identity analytification endomorphism. -/
noncomputable def id : AnalyticEndomorphism A where
  algebraic := ComplexSchemeEndomorphism.id V
  continuous_toFun := by
    have hmap : transportedPointMap A (ComplexSchemeEndomorphism.id V) = _root_.id := by
      funext x
      simp
    rw [hmap]
    exact continuous_id

/-- Analytic endomorphisms compose. -/
noncomputable def comp
    (f g : AnalyticEndomorphism A) : AnalyticEndomorphism A where
  algebraic := ComplexSchemeEndomorphism.comp f.algebraic g.algebraic
  continuous_toFun := by
    have hmap : transportedPointMap A
        (ComplexSchemeEndomorphism.comp f.algebraic g.algebraic)
        = transportedPointMap A g.algebraic ∘ transportedPointMap A f.algebraic := by
      funext x
      exact transportedPointMap_comp A f.algebraic g.algebraic x
    rw [hmap]
    exact g.continuous_toFun.comp f.continuous_toFun

@[simp]
theorem toTopCatHom_id :
    (id (A := A)).toTopCatHom = 𝟙 A.space :=
  TopCat.ext (fun x => transportedPointMap_id A x)

@[simp]
theorem toTopCatHom_comp
    (f g : AnalyticEndomorphism A) :
    (comp (A := A) f g).toTopCatHom = f.toTopCatHom ≫ g.toTopCatHom :=
  TopCat.ext (fun x => transportedPointMap_comp A f.algebraic g.algebraic x)

end AnalyticEndomorphism

/-- Morphism-level analytification package for all C-scheme endomorphisms of
one smooth projective carrier.  This records continuity, not any Hodge or
cycle-class conclusion. -/
structure EndomorphismAnalytification where
  lift : ComplexSchemeEndomorphism V → AnalyticEndomorphism A
  lift_algebraic : ∀ f, (lift f).algebraic = f
  lift_id : lift (ComplexSchemeEndomorphism.id V) =
    AnalyticEndomorphism.id (A := A)
  lift_comp : ∀ f g,
    lift (ComplexSchemeEndomorphism.comp f g) =
      AnalyticEndomorphism.comp (A := A) (lift f) (lift g)

#check ComplexSchemeEndomorphism
#check ComplexSchemeEndomorphism.complexPointMap
#check transportedPointMap
#check AnalyticEndomorphism
#check AnalyticEndomorphism.toTopCatHom
#check EndomorphismAnalytification

#print axioms ComplexSchemeEndomorphism.complexPointMap_id
#print axioms ComplexSchemeEndomorphism.complexPointMap_comp
#print axioms transportedPointMap_id
#print axioms transportedPointMap_comp
#print axioms AnalyticEndomorphism.toTopCatHom_comp

end GSTClassicalHodgeAnalytificationFunctoriality
