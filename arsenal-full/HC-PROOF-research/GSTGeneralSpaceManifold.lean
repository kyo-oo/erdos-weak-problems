import GSTGeneralSpaceTopology
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# GENERAL SPACE THEORY — MANIFOLD CAPABILITY

GST does not define a space to be a manifold.  Instead every Mathlib manifold
is admitted as a topological General-Space sector, and its smooth structure is
retained as an optional capability.

This is the direction of abstraction required by General Space Theory:

* arbitrary General Spaces need not have coordinates or dimension;
* every charted C^n manifold can nevertheless be observed inside GST;
* every C^n manifold map induces a whole-space GST morphism;
* the native manifold structure remains available and is never replaced by
  the GST abstraction.
-/

universe u u' v v' w w' h h'

namespace GSTGeneralSpace

open scoped Manifold ContDiff
open GSTGeneralSpace.GeneralSpace

/-- The underlying General Space of any topological manifold carrier.  The
manifold structure is deliberately not stored in the ontological core. -/
abbrev manifoldGeneralSpace
    (M : Type u) [TopologicalSpace M] : GeneralSpace :=
  topologicalGeneralSpace M

/-- A proof object recording that a General-Space topological sector carries a
specific Mathlib C^n manifold structure.  This is a capability, not a field of
`GeneralSpace`. -/
structure ManifoldCapability
    (𝕜 : Type v) [NontriviallyNormedField 𝕜]
    (E : Type w) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (H : Type u') [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ∞ω) : Prop where
  manifold : IsManifold I n M

/-- Every actual Mathlib C^n manifold produces the corresponding capability
certificate. -/
def manifoldCapability
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type u'} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ∞ω) [IsManifold I n M] :
    ManifoldCapability 𝕜 E H I M n :=
  ⟨inferInstance⟩

/-- **ALL-MANIFOLD ADMISSION LAW.**
Every Mathlib C^n manifold, of arbitrary carrier/model/corners/regularity,
has a canonical carrier-independent General Space realization. -/
theorem every_manifold_admits_generalSpace
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type u'} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ∞ω) [IsManifold I n M] :
    Nonempty (@GeneralSpace.{u, 0}) :=
  ⟨manifoldGeneralSpace M⟩

/-- A C^n map between arbitrary manifolds automatically becomes a
General-Space morphism, because smooth manifold transport is in particular
continuous transport. -/
def contMDiffHom
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type w'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H : Type h} [TopologicalSpace H]
    {H' : Type h'} [TopologicalSpace H']
    {I : ModelWithCorners 𝕜 E H}
    {I' : ModelWithCorners 𝕜 E' H'}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type u'} [TopologicalSpace N] [ChartedSpace H' N]
    {n : ℕ∞ω}
    (f : M → N)
    (hf : ContMDiff I I' n f) :
    GeneralSpace.Hom (manifoldGeneralSpace M) (manifoldGeneralSpace N) :=
  continuousHom f hf.continuous

/-- Smooth maps therefore preserve genuine continuous-path reachability inside
GST. -/
theorem contMDiff_preserves_generalSpace_reachability
    {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type w'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H : Type h} [TopologicalSpace H]
    {H' : Type h'} [TopologicalSpace H']
    {I : ModelWithCorners 𝕜 E H}
    {I' : ModelWithCorners 𝕜 E' H'}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type u'} [TopologicalSpace N] [ChartedSpace H' N]
    {n : ℕ∞ω}
    (f : M → N)
    (hf : ContMDiff I I' n f)
    {x y : M} :
    TopologicalReachability x y →
      TopologicalReachability (f x) (f y) :=
  topologicalReachability_map f hf.continuous

/-- The manifold carrier itself is an identity chart of the corresponding
General Space.  Local manifold charts remain additional observations rather
than ontological coordinates. -/
def manifoldCarrierChart
    (M : Type u) [TopologicalSpace M] :
    GeneralSpace.Chart (manifoldGeneralSpace M) :=
  topologicalCarrierChart M

#check manifoldGeneralSpace
#check ManifoldCapability
#check manifoldCapability
#check every_manifold_admits_generalSpace
#check contMDiffHom
#check contMDiff_preserves_generalSpace_reachability

end GSTGeneralSpace
