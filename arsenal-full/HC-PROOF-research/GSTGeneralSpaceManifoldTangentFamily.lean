import GSTGeneralSpaceManifold
import GSTGeneralSpaceFiberedCosmology
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# GENERAL SPACE THEORY — MANIFOLD TANGENT FAMILY

Every smooth manifold enters GST through its underlying topological General
Space.  Its tangent spaces are not one fixed global state space: they vary with
the base point.  This file records the genuine Mathlib tangent bundle as a GST
local family.

No canonical path transport is asserted.  Such transport requires additional
geometric structure (for example a connection), and GST keeps that distinction
explicit.
-/

universe u v w u'

namespace GSTGeneralSpace

open scoped Manifold ContDiff

/-- The genuine pointwise tangent-space family of an arbitrary charted
manifold. -/
instance {M : Type u} [TopologicalSpace M] :
    TopologicalSpace (manifoldGeneralSpace M).Point :=
  inferInstanceAs (TopologicalSpace M)

instance {M : Type u} [TopologicalSpace M] {H : Type u'} [TopologicalSpace H]
    [ChartedSpace H M] :
    ChartedSpace H (manifoldGeneralSpace M).Point :=
  inferInstanceAs (ChartedSpace H M)

def manifoldTangentFamily
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type u'} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M] :
    LocalFamily (manifoldGeneralSpace M) where
  Fiber x := TangentSpace I x

/-- Fiber identification is literal: the GST local fiber at x is the actual
Mathlib tangent space T_x M. -/
@[simp]
theorem manifoldTangentFamily_fiber
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type u'} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (x : M) :
    (manifoldTangentFamily I M).Fiber x = TangentSpace I x := rfl

/-- Tangent families therefore survive a change in the *ontology layer*
without replacing the native differential-geometric object. -/
theorem every_manifold_has_native_tangent_family
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type u'} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ∞ω) [IsManifold I n M] :
    Nonempty (@LocalFamily.{u, 0, w} (manifoldGeneralSpace M)) :=
  ⟨manifoldTangentFamily I M⟩

#check manifoldTangentFamily
#check manifoldTangentFamily_fiber
#check every_manifold_has_native_tangent_family

end GSTGeneralSpace
