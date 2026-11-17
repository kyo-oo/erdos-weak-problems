import GSTSmoothProjectiveNoetherian
import GSTClassicalHodgeProjectivePrincipalSection

/-!
# GST CLASSICAL HODGE — NOETHERIAN PRINCIPAL-SECTION CUTTING ENGINE

The projective-principal-section layer produces, for every source point of a
smooth projective complex scheme, a positive-degree homogeneous equation whose
pulled-back zero locus avoids that point.  This module upgrades that local
construction to the finiteness package required for recursive algebraic-cycle
construction.

The key facts are purely geometric:

* every generator-specific principal section is a closed subscheme of the
  smooth projective carrier;
* hence it is compact;
* closed immersions into a locally Noetherian scheme are locally of finite
  type, so the section is locally Noetherian;
* compact + locally Noetherian gives Noetherian;
* therefore the section has only finitely many irreducible components;
* the relevance-selected equation avoids its source point, so its support is
  a genuinely proper closed subset of the carrier.

No Hodge data, cycle-class map, or algebraicity conclusion occurs here.  This
is the recursive geometric cutting engine that later feeds native codimension
cycles.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open GSTProjectiveOverC
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgeProjectivePrincipalSection
open GSTSmoothProjectiveNoetherian

namespace GSTClassicalHodgePrincipalSectionNoetherian

/-- Every generator-specific principal section is locally Noetherian. -/
noncomputable def principalSectionAtIsLocallyNoetherian
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IsLocallyNoetherian (principalSectionAt V x) := by
  letI : IsLocallyNoetherian V.X := smoothProjectiveIsLocallyNoetherian V
  letI : IsClosedImmersion (principalSectionAtι V x) :=
    principalSectionAt_isClosedImmersion V x
  letI : LocallyOfFiniteType (principalSectionAtι V x) := by infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (principalSectionAtι V x)

/-- Every generator-specific principal section is compact. -/
noncomputable def principalSectionAtCompactSpace
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    CompactSpace (principalSectionAt V x) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  letI : IsClosedImmersion (principalSectionAtι V x) :=
    principalSectionAt_isClosedImmersion V x
  refine ⟨?_⟩
  have hpre :=
    QuasiCompact.isCompact_preimage
      (f := principalSectionAtι V x)
      Set.univ isOpen_univ (isCompact_univ : IsCompact (Set.univ : Set V.X))
  simpa using hpre

/-- Generator-specific principal sections are Noetherian schemes. -/
noncomputable def principalSectionAtIsNoetherian
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IsNoetherian (principalSectionAt V x) := by
  letI : IsLocallyNoetherian (principalSectionAt V x) :=
    principalSectionAtIsLocallyNoetherian V x
  letI : CompactSpace (principalSectionAt V x) :=
    principalSectionAtCompactSpace V x
  exact { }

/-- Their underlying Zariski spaces are Noetherian. -/
noncomputable def principalSectionAtNoetherianSpace
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    NoetherianSpace (principalSectionAt V x) := by
  letI : IsNoetherian (principalSectionAt V x) :=
    principalSectionAtIsNoetherian V x
  infer_instance

/-- Every generator-specific principal section has finitely many irreducible
components. -/
theorem finite_principalSectionAt_irreducibleComponents
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    (irreducibleComponents (principalSectionAt V x)).Finite := by
  letI : IsNoetherian (principalSectionAt V x) :=
    principalSectionAtIsNoetherian V x
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- The support of the generator-specific section is not all of `V`: the
source point is explicitly excluded by the relevance-selected homogeneous
separator. -/
theorem principalSectionAt_support_ne_univ
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    (principalSectionIdeal V
      (positiveHomogeneousSeparator V.projective.n
        (V.projective.immersion x)).equation).support ≠ ⊤ := by
  intro h
  have hx : x ∈
      (principalSectionIdeal V
        (positiveHomogeneousSeparator V.projective.n
          (V.projective.immersion x)).equation).support := by
    rw [h]
    trivial
  exact source_not_mem_principalSection V x hx

/-- Pointed strict-cut crown: the canonical positive-degree principal section
at a point is simultaneously Noetherian, finite-component, and genuinely
proper in the carrier. -/
theorem principalSectionAt_strict_cut_crown
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    (irreducibleComponents (principalSectionAt V x)).Finite
      ∧ (principalSectionIdeal V
          (positiveHomogeneousSeparator V.projective.n
            (V.projective.immersion x)).equation).support ≠ ⊤ := by
  exact ⟨finite_principalSectionAt_irreducibleComponents V x,
    principalSectionAt_support_ne_univ V x⟩

#check principalSectionAtIsLocallyNoetherian
#check principalSectionAtCompactSpace
#check principalSectionAtIsNoetherian
#check principalSectionAtNoetherianSpace
#check finite_principalSectionAt_irreducibleComponents
#check principalSectionAt_support_ne_univ
#check principalSectionAt_strict_cut_crown

#print axioms principalSectionAtIsLocallyNoetherian
#print axioms principalSectionAtCompactSpace
#print axioms principalSectionAtIsNoetherian
#print axioms finite_principalSectionAt_irreducibleComponents
#print axioms principalSectionAt_support_ne_univ
#print axioms principalSectionAt_strict_cut_crown

end GSTClassicalHodgePrincipalSectionNoetherian
