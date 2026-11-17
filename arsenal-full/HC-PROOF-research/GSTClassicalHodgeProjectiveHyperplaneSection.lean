import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import GSTProjectiveOverC

/-!
# GST CLASSICAL HODGE — GENUINE PROJECTIVE HYPERPLANE SECTIONS

This module constructs an actual coordinate hyperplane in the standard
projective space used by `ProjectiveOverC`, upgrades its closed zero locus to
the reduced induced closed subscheme, and pulls that subscheme back along the
actual projective embedding of a smooth projective complex scheme.

Nothing in this file mentions the Hodge conjecture, a cycle-class map, or a
basis of cohomology.  It is pure projective scheme geometry.  The resulting
closed subscheme is the geometric source from which the later native
codimension-raising cycle operator is to be extracted.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open TopologicalSpace
open GSTProjectiveOverC

namespace GSTClassicalHodgeProjectiveHyperplaneSection

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous coordinate defining the i-th coordinate hyperplane in
standard projective n-space. -/
def hyperplaneCoordinate (n : Nat) (i : Fin (n + 1)) :
    ProjectiveCoordinateRing n :=
  MvPolynomial.X i

/-- The underlying projective zero locus of one coordinate hyperplane. -/
def projectiveHyperplaneSet (n : Nat) (i : Fin (n + 1)) :
    Set (projectiveSpace n) :=
  ProjectiveSpectrum.zeroLocus (ProjectiveGrading n)
    ({hyperplaneCoordinate n i} : Set (ProjectiveCoordinateRing n))

/-- The coordinate hyperplane zero locus is Zariski closed. -/
theorem projectiveHyperplaneSet_isClosed
    (n : Nat) (i : Fin (n + 1)) :
    IsClosed (projectiveHyperplaneSet n i) := by
  exact ProjectiveSpectrum.isClosed_zeroLocus
    (ProjectiveGrading n)
    ({hyperplaneCoordinate n i} : Set (ProjectiveCoordinateRing n))

/-- Bundled closed subset underlying the coordinate hyperplane. -/
noncomputable def projectiveHyperplaneClosed
    (n : Nat) (i : Fin (n + 1)) :
    Closeds (projectiveSpace n) :=
  ⟨projectiveHyperplaneSet n i,
    projectiveHyperplaneSet_isClosed n i⟩

/-- Vanishing ideal sheaf of the coordinate hyperplane.  Mathlib's
`IdealSheafData.vanishingIdeal` gives the reduced induced closed-subscheme
structure on this closed locus. -/
noncomputable def projectiveHyperplaneIdeal
    (n : Nat) (i : Fin (n + 1)) :
    (projectiveSpace n).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (projectiveHyperplaneClosed n i)

/-- The genuine coordinate hyperplane as a scheme. -/
noncomputable def projectiveHyperplane
    (n : Nat) (i : Fin (n + 1)) : Scheme :=
  (projectiveHyperplaneIdeal n i).subscheme

/-- Closed immersion of the coordinate hyperplane into standard projective
space. -/
noncomputable def projectiveHyperplaneι
    (n : Nat) (i : Fin (n + 1)) :
    projectiveHyperplane n i ⟶ projectiveSpace n :=
  (projectiveHyperplaneIdeal n i).subschemeι

set_option trace.Meta.synthInstance true in
instance projectiveHyperplane_isClosedImmersion
    (n : Nat) (i : Fin (n + 1)) :
    IsClosedImmersion (projectiveHyperplaneι n i) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.subschemeι (projectiveHyperplaneIdeal n i)))

/-- The reduced coordinate-hyperplane subscheme has exactly the intended
projective zero locus as support. -/
theorem projectiveHyperplaneIdeal_support
    (n : Nat) (i : Fin (n + 1)) :
    (projectiveHyperplaneIdeal n i).support =
      projectiveHyperplaneClosed n i := by
  apply TopologicalSpace.Closeds.ext
  simp [projectiveHyperplaneIdeal, projectiveHyperplaneClosed]

/-- Pull the coordinate-hyperplane ideal sheaf back along the actual closed
projective embedding of V.  This is the scheme-theoretic hyperplane section
of V associated to the chosen projective coordinate. -/
noncomputable def hyperplaneSectionIdeal
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    V.X.IdealSheafData :=
  (projectiveHyperplaneIdeal V.projective.n i).comap
    V.projective.immersion

/-- Genuine projective hyperplane section of V. -/
noncomputable def hyperplaneSection
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) : Scheme :=
  (hyperplaneSectionIdeal V i).subscheme

/-- Closed immersion of the hyperplane section into V. -/
noncomputable def hyperplaneSectionι
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    hyperplaneSection V i ⟶ V.X :=
  (hyperplaneSectionIdeal V i).subschemeι

instance hyperplaneSection_isClosedImmersion
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    IsClosedImmersion (hyperplaneSectionι V i) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.subschemeι (hyperplaneSectionIdeal V i)))

/-- The hyperplane section is canonically isomorphic to the fibred product of
V with the coordinate hyperplane over projective space. -/
noncomputable def hyperplaneSectionIsoPullback
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    hyperplaneSection V i ≅
      pullback V.projective.immersion
        (projectiveHyperplaneι V.projective.n i) :=
  (projectiveHyperplaneIdeal V.projective.n i).comapIso
    V.projective.immersion

/-- Under the pullback identification, the closed immersion into V is the
first projection of the geometric fibre product. -/
theorem hyperplaneSectionIsoPullback_fst
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    (hyperplaneSectionIsoPullback V i).hom ≫
        pullback.fst V.projective.immersion
          (projectiveHyperplaneι V.projective.n i) =
      hyperplaneSectionι V i := by
  exact (projectiveHyperplaneIdeal V.projective.n i).comapIso_hom_fst
    V.projective.immersion

/-- Exact support formula: a point of V lies in the hyperplane section iff its
image under the projective embedding lies in the coordinate hyperplane. -/
theorem hyperplaneSectionIdeal_support
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1)) :
    (hyperplaneSectionIdeal V i).support =
      (projectiveHyperplaneIdeal V.projective.n i).support.preimage
        V.projective.immersion.continuous := by
  exact Scheme.IdealSheafData.support_comap
    (projectiveHyperplaneIdeal V.projective.n i)
    V.projective.immersion

/-- Pointwise form of the support equation. -/
theorem mem_hyperplaneSection_support_iff
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1))
    (x : V.X) :
    x ∈ (hyperplaneSectionIdeal V i).support ↔
      V.projective.immersion x ∈
        projectiveHyperplaneSet V.projective.n i := by
  rw [hyperplaneSectionIdeal_support, projectiveHyperplaneIdeal_support]
  rfl

/-- Algebraic characterization of section membership: the chosen homogeneous
coordinate belongs to the relevant homogeneous prime corresponding to the
projective image of x. -/
theorem mem_hyperplaneSection_support_iff_coordinate
    (V : SmoothProjectiveComplexScheme)
    (i : Fin (V.projective.n + 1))
    (x : V.X) :
    x ∈ (hyperplaneSectionIdeal V i).support ↔
      hyperplaneCoordinate V.projective.n i ∈
        (V.projective.immersion x).asHomogeneousIdeal := by
  rw [mem_hyperplaneSection_support_iff]
  exact (ProjectiveSpectrum.mem_zeroLocus (ProjectiveGrading V.projective.n)
      (V.projective.immersion x)
      ({hyperplaneCoordinate V.projective.n i} :
        Set (ProjectiveCoordinateRing V.projective.n))).trans
    Set.singleton_subset_iff

#check hyperplaneCoordinate
#check projectiveHyperplaneSet
#check projectiveHyperplaneClosed
#check projectiveHyperplaneIdeal
#check projectiveHyperplane
#check projectiveHyperplaneι
#check hyperplaneSectionIdeal
#check hyperplaneSection
#check hyperplaneSectionι
#check hyperplaneSectionIsoPullback
#check hyperplaneSectionIdeal_support
#check mem_hyperplaneSection_support_iff
#check mem_hyperplaneSection_support_iff_coordinate

#print axioms projectiveHyperplaneSet_isClosed
#print axioms projectiveHyperplaneIdeal_support
#print axioms hyperplaneSectionIsoPullback_fst
#print axioms hyperplaneSectionIdeal_support
#print axioms mem_hyperplaneSection_support_iff_coordinate

end GSTClassicalHodgeProjectiveHyperplaneSection
