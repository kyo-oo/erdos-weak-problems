import Mathlib.AlgebraicGeometry.Noetherian
import GSTCompactNativeCyclePresentation
import GSTClassicalHodgeProjectiveHyperplaneSection

/-!
# GST SMOOTH PROJECTIVE — NOETHERIAN FINITENESS FRONT

Smooth projective complex schemes are Noetherian for two independent geometric
reasons already present in the formalization:

* smoothness over `Spec C` gives a locally-finite-type morphism over a
  Noetherian base, hence local Noetherianity;
* projectivity gives compactness of the underlying Zariski space through the
  actual closed immersion into projective space.

The same argument applies to every closed hyperplane section.  This file turns
those facts into reusable instances so that irreducible-component and generic-
point constructions are finite downstream.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgeProjectiveHyperplaneSection

namespace GSTSmoothProjectiveNoetherian

/-- The complex base `Spec C` is locally Noetherian. -/
noncomputable def complexBaseIsLocallyNoetherian :
    IsLocallyNoetherian complexBase := by
  dsimp [complexBase]
  infer_instance

/-- Smoothness over the Noetherian complex base makes every smooth projective
carrier locally Noetherian. -/
noncomputable def smoothProjectiveIsLocallyNoetherian
    (V : SmoothProjectiveComplexScheme) :
    IsLocallyNoetherian V.X := by
  letI : IsLocallyNoetherian complexBase := complexBaseIsLocallyNoetherian
  letI : LocallyOfFiniteType V.structureMap := by infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian V.structureMap

/-- **SMOOTH-PROJECTIVE NOETHERIANITY.** -/
noncomputable def smoothProjectiveIsNoetherian
    (V : SmoothProjectiveComplexScheme) :
    IsNoetherian V.X := by
  letI : IsLocallyNoetherian V.X := smoothProjectiveIsLocallyNoetherian V
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  exact { }

/-- The underlying Zariski space of a smooth projective complex scheme is a
Noetherian topological space. -/
noncomputable def smoothProjectiveNoetherianSpace
    (V : SmoothProjectiveComplexScheme) :
    TopologicalSpace.NoetherianSpace V.X := by
  letI : IsNoetherian V.X := smoothProjectiveIsNoetherian V
  infer_instance

/-- A hyperplane section is locally Noetherian because its inclusion into the
smooth projective carrier is a closed immersion, hence locally of finite type. -/
noncomputable def hyperplaneSectionIsLocallyNoetherian
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    IsLocallyNoetherian (hyperplaneSection V i) := by
  letI : IsLocallyNoetherian V.X := smoothProjectiveIsLocallyNoetherian V
  letI : IsClosedImmersion (hyperplaneSectionι V i) :=
    hyperplaneSection_isClosedImmersion V i
  letI : LocallyOfFiniteType (hyperplaneSectionι V i) := by infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (hyperplaneSectionι V i)

/-- A hyperplane section is compact because it is a closed immersion into a
compact projective carrier. -/
noncomputable def hyperplaneSectionCompactSpace
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    CompactSpace (hyperplaneSection V i) := by
  letI : CompactSpace V.X := smoothProjectiveCompactSpace V
  letI : IsClosedImmersion (hyperplaneSectionι V i) :=
    hyperplaneSection_isClosedImmersion V i
  refine ⟨?_⟩
  have hpre :=
    QuasiCompact.isCompact_preimage
      (f := hyperplaneSectionι V i)
      Set.univ isOpen_univ (isCompact_univ : IsCompact (Set.univ : Set V.X))
  simpa using hpre

/-- Every genuine projective hyperplane section is Noetherian. -/
noncomputable def hyperplaneSectionIsNoetherian
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    IsNoetherian (hyperplaneSection V i) := by
  letI : IsLocallyNoetherian (hyperplaneSection V i) :=
    hyperplaneSectionIsLocallyNoetherian V i
  letI : CompactSpace (hyperplaneSection V i) :=
    hyperplaneSectionCompactSpace V i
  exact { }

/-- Finiteness of irreducible components of the smooth projective carrier. -/
theorem finite_irreducibleComponents
    (V : SmoothProjectiveComplexScheme) :
    (irreducibleComponents V.X).Finite := by
  letI : IsNoetherian V.X := smoothProjectiveIsNoetherian V
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- Finiteness of irreducible components of every coordinate hyperplane
section. -/
theorem finite_hyperplaneSection_irreducibleComponents
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    (irreducibleComponents (hyperplaneSection V i)).Finite := by
  letI : IsNoetherian (hyperplaneSection V i) :=
    hyperplaneSectionIsNoetherian V i
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

#check complexBaseIsLocallyNoetherian
#check smoothProjectiveIsLocallyNoetherian
#check smoothProjectiveIsNoetherian
#check smoothProjectiveNoetherianSpace
#check hyperplaneSectionIsLocallyNoetherian
#check hyperplaneSectionCompactSpace
#check hyperplaneSectionIsNoetherian
#check finite_irreducibleComponents
#check finite_hyperplaneSection_irreducibleComponents

#print axioms smoothProjectiveIsLocallyNoetherian
#print axioms smoothProjectiveIsNoetherian
#print axioms hyperplaneSectionIsNoetherian
#print axioms finite_irreducibleComponents
#print axioms finite_hyperplaneSection_irreducibleComponents

end GSTSmoothProjectiveNoetherian
