import GSTClassicalHodgeAnalytificationFunctoriality
import GSTProjectiveOverC
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# GST CLASSICAL HODGE — GENUINE PROJECTIVE SELF-CORRESPONDENCES

The multiplicity operators used by the internal GST universe must eventually
be realized by genuine algebraic geometry, not by arbitrary basis read/write
maps.  The correct geometric carrier is the self-product

  X ×_{Spec C} X.

Every smooth projective complex carrier in this repository already comes with
a closed immersion into an actual Mathlib `Proj`.  Hence it is separated over
`Spec C`.  Its diagonal and the graph of every C-scheme endomorphism are
therefore genuine closed immersions into the self-product.

This module constructs those objects and proves their projection identities.
No Hodge class, cycle-class surjectivity, or coordinate-basis assumption occurs
here.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeAnalytificationFunctoriality

namespace GSTClassicalHodgeProjectiveSelfCorrespondences

attribute [local instance] MvPolynomial.gradedAlgebra

variable (V : SmoothProjectiveComplexScheme)

/-- Actual algebraic self-product over the complex base. -/
abbrev selfProduct : Scheme :=
  pullback V.structureMap V.structureMap

/-- First projection of the self-product. -/
abbrev fst : selfProduct V ⟶ V.X :=
  pullback.fst V.structureMap V.structureMap

/-- Second projection of the self-product. -/
abbrev snd : selfProduct V ⟶ V.X :=
  pullback.snd V.structureMap V.structureMap

/-- The two projections agree after composition to `Spec C`. -/
theorem fst_toBase_eq_snd_toBase :
    fst V ≫ V.structureMap = snd V ≫ V.structureMap :=
  pullback.condition

/-- Algebraic diagonal of the projective carrier. -/
noncomputable def diagonal : V.X ⟶ selfProduct V :=
  pullback.lift (𝟙 V.X) (𝟙 V.X) (by simp)

@[simp, reassoc]
theorem diagonal_fst :
    diagonal V ≫ fst V = 𝟙 V.X :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
theorem diagonal_snd :
    diagonal V ≫ snd V = 𝟙 V.X :=
  pullback.lift_snd _ _ _

/-- Graph of a genuine C-scheme endomorphism inside the self-product. -/
noncomputable def graph
    (f : ComplexSchemeEndomorphism V) :
    V.X ⟶ selfProduct V :=
  pullback.lift (𝟙 V.X) f.hom (by
    rw [Category.id_comp, f.over_base])

@[simp, reassoc]
theorem graph_fst
    (f : ComplexSchemeEndomorphism V) :
    graph V f ≫ fst V = 𝟙 V.X :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
theorem graph_snd
    (f : ComplexSchemeEndomorphism V) :
    graph V f ≫ snd V = f.hom :=
  pullback.lift_snd _ _ _

/-- The diagonal is the graph of the identity endomorphism. -/
theorem graph_id :
    graph V (ComplexSchemeEndomorphism.id V) = diagonal V := by
  apply pullback.hom_ext
  · simp only [graph, diagonal, fst, pullback.lift_fst,
      ComplexSchemeEndomorphism.id]
  · simp only [graph, diagonal, snd, pullback.lift_snd,
      ComplexSchemeEndomorphism.id]

/-- Projective space over C is separated. -/
local instance projectiveSpace_separated (n : Nat) :
    IsSeparated (projectiveSpaceToBase n) := by
  unfold projectiveSpaceToBase
  haveI hF : IsSeparated (Proj.toSpecZero (ProjectiveGrading n)) := inferInstance
  haveI hG : IsSeparated (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (ProjectiveGrading n 0)))) := inferInstance
  exact IsSeparated.stableUnderComposition.comp_mem _ _ hF hG

/-- Every smooth projective complex carrier in the repository is separated
over the complex base, derived from its closed projective embedding. -/
instance smoothProjective_isSeparated : IsSeparated V.structureMap := by
  rw [← V.projective.over_base]
  haveI : IsClosedImmersion (V.projective.immersion) := V.projective.closedImmersion
  haveI : IsSeparated (projectiveSpaceToBase V.projective.n) := inferInstance
  infer_instance

/-- The algebraic diagonal is a genuine closed immersion. -/
instance diagonal_isClosedImmersion : IsClosedImmersion (diagonal V) := by
  show IsClosedImmersion (pullback.diagonal V.structureMap)
  infer_instance

/-- The `(a, b) ↦ (f a, b)`-twist of the self-product. -/
noncomputable def twist (f : ComplexSchemeEndomorphism V) :
    selfProduct V ⟶ selfProduct V :=
  pullback.lift (fst V ≫ f.hom) (snd V) (by
    rw [Category.assoc, f.over_base, pullback.condition])

/-- The graph is the base change of the separated diagonal along the twist. -/
private theorem graph_isPullback (f : ComplexSchemeEndomorphism V) :
    IsPullback f.hom (graph V f)
      (pullback.diagonal V.structureMap) (twist V f) := by
  have hcond1 : pullback.fst (pullback.diagonal V.structureMap) (twist V f) =
      pullback.snd (pullback.diagonal V.structureMap) (twist V f) ≫ (fst V ≫ f.hom) := by
    have h := congrArg (fun g => g ≫ fst V)
      (pullback.condition (f := pullback.diagonal V.structureMap) (g := twist V f))
    simp only [twist] at h
    rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id,
      pullback.lift_fst] at h
    exact h
  have hcond2 : pullback.fst (pullback.diagonal V.structureMap) (twist V f) =
      pullback.snd (pullback.diagonal V.structureMap) (twist V f) ≫ snd V := by
    have h := congrArg (fun g => g ≫ snd V)
      (pullback.condition (f := pullback.diagonal V.structureMap) (g := twist V f))
    simp only [twist] at h
    rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_snd] at h
    exact h
  have hw : f.hom ≫ pullback.diagonal V.structureMap = graph V f ≫ twist V f := by
    apply pullback.hom_ext
    · simp only [twist]
      rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc,
        pullback.lift_fst, ← Category.assoc, graph_fst, Category.id_comp]
    · simp only [twist]
      rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc,
        pullback.lift_snd, graph_snd]
  refine IsPullback.of_iso_pullback ⟨hw⟩
    ⟨pullback.lift f.hom (graph V f) hw,
      pullback.snd (pullback.diagonal V.structureMap) (twist V f) ≫ fst V, ?_, ?_⟩
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  · rw [← Category.assoc, pullback.lift_snd, graph_fst]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.id_comp, hcond1]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, graph_fst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, graph_snd, ← hcond1, hcond2]

/-- Every algebraic graph over C is a genuine closed immersion into the
projective self-product. -/
instance graph_isClosedImmersion
    (f : ComplexSchemeEndomorphism V) :
    IsClosedImmersion (graph V f) :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback (graph_isPullback V f)
    (inferInstanceAs (IsClosedImmersion (pullback.diagonal V.structureMap)))

/-- Universal characterization of the graph by its two projections. -/
theorem graph_unique
    (f : ComplexSchemeEndomorphism V)
    (g : V.X ⟶ selfProduct V)
    (hfst : g ≫ fst V = 𝟙 V.X)
    (hsnd : g ≫ snd V = f.hom) :
    g = graph V f := by
  apply pullback.hom_ext
  · simpa [hfst] using hfst
  · simpa [hsnd] using hsnd

/-- Self-correspondence geometry crown. -/
theorem projective_self_correspondence_crown :
    IsClosedImmersion (diagonal V)
    ∧ (∀ f : ComplexSchemeEndomorphism V,
      IsClosedImmersion (graph V f))
    ∧ (∀ f : ComplexSchemeEndomorphism V,
      graph V f ≫ fst V = 𝟙 V.X
      ∧ graph V f ≫ snd V = f.hom) := by
  refine ⟨inferInstance, fun f => inferInstance, ?_⟩
  intro f
  exact ⟨graph_fst V f, graph_snd V f⟩

#check selfProduct
#check fst
#check snd
#check diagonal
#check graph
#check graph_fst
#check graph_snd
#check graph_id
#check graph_isClosedImmersion
#check projective_self_correspondence_crown

#print axioms graph_fst
#print axioms graph_snd
#print axioms graph_id
#print axioms projective_self_correspondence_crown

end GSTClassicalHodgeProjectiveSelfCorrespondences
