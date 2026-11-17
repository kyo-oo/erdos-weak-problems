import GSTGeneralSpaceManifoldTangentFamily
import GSTGeneralSpaceMorphisms
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# GENERAL SPACE THEORY — TANGENT-FAMILY MORPHISMS

Smooth maps move manifold points covariantly and their derivatives move tangent
vectors covariantly between the corresponding local fibers.  This is the
differential-geometric counterpart to the contravariant stalk maps of schemes.
-/

universe u u' v w w' h h'

namespace GSTGeneralSpace

open scoped Manifold
open GSTGeneralSpace.GeneralSpace

/-- A covariant map of local families above a map of base General Spaces. -/
structure LocalMorphism
    {G : GeneralSpace} {H : GeneralSpace}
    (f : GeneralSpace.Hom G H)
    (F : LocalFamily G) (K : LocalFamily H) where
  map : ∀ x : G.Point, F.Fiber x → K.Fiber (f.mapPoint x)

/-- The differential of a C¹ manifold map as a covariant GST local-family
morphism between the genuine tangent families. -/
noncomputable def tangentLocalMorphism
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type w'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H : Type h} [TopologicalSpace H]
    {H' : Type h'} [TopologicalSpace H']
    {I : ModelWithCorners 𝕜 E H}
    {I' : ModelWithCorners 𝕜 E' H'}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type u'} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold I 1 M] [IsManifold I' 1 N]
    (f : M → N)
    (hf : ContMDiff I I' 1 f) :
    LocalMorphism (contMDiffHom f hf)
      (manifoldTangentFamily I M) (manifoldTangentFamily I' N) where
  map x := mfderiv I I' f x

/-- Evaluation of the GST tangent morphism is literally Mathlib's manifold
derivative at the point. -/
@[simp]
theorem tangentLocalMorphism_apply
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type w'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H : Type h} [TopologicalSpace H]
    {H' : Type h'} [TopologicalSpace H']
    {I : ModelWithCorners 𝕜 E H}
    {I' : ModelWithCorners 𝕜 E' H'}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type u'} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold I 1 M] [IsManifold I' 1 N]
    (f : M → N) (hf : ContMDiff I I' 1 f)
    (x : M) (v : TangentSpace I x) :
    (tangentLocalMorphism f hf).map x v = mfderiv I I' f x v := rfl

/-- The native tangent-bundle map and the GST local-family morphism have the
same base motion and fiber motion. -/
theorem tangentMap_eq_generalSpace_local_morphism
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type w'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H : Type h} [TopologicalSpace H]
    {H' : Type h'} [TopologicalSpace H']
    {I : ModelWithCorners 𝕜 E H}
    {I' : ModelWithCorners 𝕜 E' H'}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type u'} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold I 1 M] [IsManifold I' 1 N]
    (f : M → N) (hf : ContMDiff I I' 1 f)
    (x : M) (v : TangentSpace I x) :
    tangentMap I I' f ⟨x, v⟩ =
      ⟨(contMDiffHom f hf).mapPoint x,
        (tangentLocalMorphism f hf).map x v⟩ := by
  rfl

#check LocalMorphism
#check tangentLocalMorphism
#check tangentLocalMorphism_apply
#check tangentMap_eq_generalSpace_local_morphism

end GSTGeneralSpace
