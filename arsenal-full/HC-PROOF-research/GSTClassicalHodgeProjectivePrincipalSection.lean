import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import GSTClassicalHodgeProjectiveHyperplaneSection

/-!
# GST CLASSICAL HODGE — GENERATOR-SPECIFIC PROJECTIVE PRINCIPAL SECTIONS

A fixed coordinate hyperplane can contain an irreducible component of a
projective variety.  The correct generatorwise Lefschetz construction therefore
chooses the cutting equation from the generic point being cut.

A point of `Proj` is relevant by definition: its homogeneous prime does not
contain the irrelevant ideal.  Since the irrelevant ideal is the union/span of
the positive-degree homogeneous pieces, every projective point admits a
positive-degree homogeneous element outside its prime.

This file extracts that element unconditionally and uses it to build the
corresponding genuine reduced principal closed subscheme of projective space,
then pulls the subscheme back along the actual projective embedding of a smooth
projective complex scheme.

No Hodge data and no cycle-class map occur here.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open TopologicalSpace
open DirectSum SetLike
open GSTProjectiveOverC

namespace GSTClassicalHodgeProjectivePrincipalSection

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A positive-degree homogeneous projective equation which does not vanish at
one specified projective point. -/
structure PositiveHomogeneousSeparator
    (n : Nat) (x : projectiveSpace n) where
  degree : Nat
  degree_pos : 0 < degree
  equation : ProjectiveCoordinateRing n
  homogeneous : equation ∈ ProjectiveGrading n degree
  not_mem_prime : equation ∉ x.asHomogeneousIdeal

/-- **RELEVANCE SEPARATOR.**  Every point of projective space admits a
positive-degree homogeneous equation which is nonzero at that point. -/
noncomputable def positiveHomogeneousSeparator
    (n : Nat) (x : projectiveSpace n) :
    PositiveHomogeneousSeparator n x := by
  apply Classical.choice
  have hnot :
      ¬ HomogeneousIdeal.irrelevant (ProjectiveGrading n) ≤
        x.asHomogeneousIdeal :=
    x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le] at hnot
  push_neg at hnot
  obtain ⟨d, hd, hpiece⟩ := hnot
  have hsubset :
      ¬ AddSubmonoid.ofClass (ProjectiveGrading n d) ≤
        x.asHomogeneousIdeal.toAddSubmonoid :=
    hpiece
  rw [SetLike.not_le_iff_exists] at hsubset
  obtain ⟨f, hfdeg, hfnot⟩ := hsubset
  exact ⟨{
    degree := d
    degree_pos := hd
    equation := f
    homogeneous := hfdeg
    not_mem_prime := hfnot
  }⟩

@[simp]
theorem positiveHomogeneousSeparator_degree_pos
    (n : Nat) (x : projectiveSpace n) :
    0 < (positiveHomogeneousSeparator n x).degree :=
  (positiveHomogeneousSeparator n x).degree_pos

@[simp]
theorem positiveHomogeneousSeparator_homogeneous
    (n : Nat) (x : projectiveSpace n) :
    (positiveHomogeneousSeparator n x).equation ∈
      ProjectiveGrading n (positiveHomogeneousSeparator n x).degree :=
  (positiveHomogeneousSeparator n x).homogeneous

@[simp]
theorem positiveHomogeneousSeparator_not_mem
    (n : Nat) (x : projectiveSpace n) :
    (positiveHomogeneousSeparator n x).equation ∉ x.asHomogeneousIdeal :=
  (positiveHomogeneousSeparator n x).not_mem_prime

/-- Projective principal zero locus of a homogeneous equation. -/
def projectivePrincipalSet
    (n : Nat) (f : ProjectiveCoordinateRing n) :
    Set (projectiveSpace n) :=
  ProjectiveSpectrum.zeroLocus (ProjectiveGrading n)
    ({f} : Set (ProjectiveCoordinateRing n))

/-- Every projective principal zero locus is closed. -/
theorem projectivePrincipalSet_isClosed
    (n : Nat) (f : ProjectiveCoordinateRing n) :
    IsClosed (projectivePrincipalSet n f) := by
  exact ProjectiveSpectrum.isClosed_zeroLocus
    (ProjectiveGrading n) ({f} : Set (ProjectiveCoordinateRing n))

noncomputable def projectivePrincipalClosed
    (n : Nat) (f : ProjectiveCoordinateRing n) :
    Closeds (projectiveSpace n) :=
  ⟨projectivePrincipalSet n f, projectivePrincipalSet_isClosed n f⟩

/-- Reduced induced ideal sheaf of the principal projective zero locus. -/
noncomputable def projectivePrincipalIdeal
    (n : Nat) (f : ProjectiveCoordinateRing n) :
    (projectiveSpace n).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (projectivePrincipalClosed n f)

/-- Genuine reduced principal projective subscheme. -/
noncomputable def projectivePrincipalSection
    (n : Nat) (f : ProjectiveCoordinateRing n) : Scheme :=
  (projectivePrincipalIdeal n f).subscheme

noncomputable def projectivePrincipalSectionι
    (n : Nat) (f : ProjectiveCoordinateRing n) :
    projectivePrincipalSection n f ⟶ projectiveSpace n :=
  (projectivePrincipalIdeal n f).subschemeι

instance projectivePrincipalSection_isClosedImmersion
    (n : Nat) (f : ProjectiveCoordinateRing n) :
    IsClosedImmersion (projectivePrincipalSectionι n f) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.subschemeι (projectivePrincipalIdeal n f)))

/-- The reduced principal-section subscheme has exactly the intended
projective principal zero locus as support. -/
theorem projectivePrincipalIdeal_support
    (n : Nat) (f : ProjectiveCoordinateRing n) :
    (projectivePrincipalIdeal n f).support =
      projectivePrincipalClosed n f := by
  apply TopologicalSpace.Closeds.ext
  simp [projectivePrincipalIdeal, projectivePrincipalClosed]

/-- Pull a principal projective section back to an actual smooth projective
scheme through its given closed projective embedding. -/
noncomputable def principalSectionIdeal
    (V : SmoothProjectiveComplexScheme)
    (f : ProjectiveCoordinateRing V.projective.n) :
    V.X.IdealSheafData :=
  (projectivePrincipalIdeal V.projective.n f).comap
    V.projective.immersion

noncomputable def principalSection
    (V : SmoothProjectiveComplexScheme)
    (f : ProjectiveCoordinateRing V.projective.n) : Scheme :=
  (principalSectionIdeal V f).subscheme

noncomputable def principalSectionι
    (V : SmoothProjectiveComplexScheme)
    (f : ProjectiveCoordinateRing V.projective.n) :
    principalSection V f ⟶ V.X :=
  (principalSectionIdeal V f).subschemeι

instance principalSection_isClosedImmersion
    (V : SmoothProjectiveComplexScheme)
    (f : ProjectiveCoordinateRing V.projective.n) :
    IsClosedImmersion (principalSectionι V f) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.subschemeι (principalSectionIdeal V f)))

/-- The principal section is the actual scheme-theoretic pullback of the
projective principal subscheme. -/
noncomputable def principalSectionIsoPullback
    (V : SmoothProjectiveComplexScheme)
    (f : ProjectiveCoordinateRing V.projective.n) :
    principalSection V f ≅
      pullback V.projective.immersion
        (projectivePrincipalSectionι V.projective.n f) :=
  (projectivePrincipalIdeal V.projective.n f).comapIso
    V.projective.immersion

/-- Support formula for the pulled-back principal section. -/
theorem principalSectionIdeal_support
    (V : SmoothProjectiveComplexScheme)
    (f : ProjectiveCoordinateRing V.projective.n) :
    (principalSectionIdeal V f).support =
      (projectivePrincipalIdeal V.projective.n f).support.preimage
        V.projective.immersion.continuous := by
  exact Scheme.IdealSheafData.support_comap
    (projectivePrincipalIdeal V.projective.n f)
    V.projective.immersion

/-- Membership in the principal section is exactly vanishing of f at the
projective image. -/
theorem mem_principalSection_support_iff
    (V : SmoothProjectiveComplexScheme)
    (f : ProjectiveCoordinateRing V.projective.n)
    (x : V.X) :
    x ∈ (principalSectionIdeal V f).support ↔
      f ∈ (V.projective.immersion x).asHomogeneousIdeal := by
  rw [principalSectionIdeal_support, projectivePrincipalIdeal_support]
  exact (Set.mem_preimage).trans ((ProjectiveSpectrum.mem_zeroLocus
      (ProjectiveGrading V.projective.n) (V.projective.immersion x)
      ({f} : Set (ProjectiveCoordinateRing V.projective.n))).trans
    Set.singleton_subset_iff)

/-- The relevance-selected equation genuinely avoids its source point. -/
theorem source_not_mem_principalSection
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    x ∉ (principalSectionIdeal V
      (positiveHomogeneousSeparator V.projective.n
        (V.projective.immersion x)).equation).support := by
  rw [mem_principalSection_support_iff]
  exact positiveHomogeneousSeparator_not_mem _ _

/-- Bundled generator-specific principal section associated to one point of V. -/
noncomputable def principalSectionAt
    (V : SmoothProjectiveComplexScheme) (x : V.X) : Scheme :=
  principalSection V
    (positiveHomogeneousSeparator V.projective.n
      (V.projective.immersion x)).equation

/-- Its closed immersion into V. -/
noncomputable def principalSectionAtι
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    principalSectionAt V x ⟶ V.X :=
  principalSectionι V
    (positiveHomogeneousSeparator V.projective.n
      (V.projective.immersion x)).equation

instance principalSectionAt_isClosedImmersion
    (V : SmoothProjectiveComplexScheme) (x : V.X) :
    IsClosedImmersion (principalSectionAtι V x) := by
  dsimp [principalSectionAtι, principalSectionAt]
  infer_instance

#check PositiveHomogeneousSeparator
#check positiveHomogeneousSeparator
#check projectivePrincipalSet
#check projectivePrincipalSection
#check principalSectionIdeal
#check principalSection
#check principalSectionIsoPullback
#check mem_principalSection_support_iff
#check source_not_mem_principalSection
#check principalSectionAt
#check principalSectionAtι

#print axioms positiveHomogeneousSeparator
#print axioms projectivePrincipalSet_isClosed
#print axioms principalSectionIdeal_support
#print axioms mem_principalSection_support_iff
#print axioms source_not_mem_principalSection

end GSTClassicalHodgeProjectivePrincipalSection
