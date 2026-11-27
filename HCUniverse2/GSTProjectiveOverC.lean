import Mathlib
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# COMPLEX SMOOTH / PROJECTIVE GEOMETRY FRONT

This file supplies the geometric object that the Stage-2 audit demanded.

It contains no Hodge classes, no cycle-class surjectivity, and no form of
the Hodge conjecture.

* the base is the actual scheme Spec(C);
* projective n-space is the actual Proj of the standard graded ring
  C[x_0,...,x_n];
* projectivity is witnessed by an actual closed immersion into such a Proj,
  together with compatibility over Spec(C);
* smoothness is Mathlib's actual AlgebraicGeometry.Smooth predicate.

The pinned Mathlib revision does not bundle projective morphisms as a named
class, so ProjectiveOverC is the missing small interface built here.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped DirectSum

namespace GSTProjectiveOverC

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The complex base scheme. -/
abbrev complexBase : Scheme := Spec (.of ℂ)

/-- Standard homogeneous coordinate ring of projective n-space. -/
abbrev ProjectiveCoordinateRing (n : Nat) :=
  MvPolynomial (Fin (n + 1)) ℂ

/-- Standard total-degree grading on the homogeneous coordinate ring. -/
abbrev ProjectiveGrading (n : Nat) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ

/-- Actual projective n-space over the complex coefficient ring, represented
by Mathlib's projective spectrum of the standard graded polynomial ring. -/
noncomputable def projectiveSpace (n : Nat) : Scheme :=
  Proj (ProjectiveGrading n)

/-- The canonical structure morphism from standard projective n-space to
Spec(C).  Mathlib supplies Proj.toSpecZero to the degree-zero homogeneous
piece; composing with Spec.map of the scalar algebra map lands in Spec(C). -/
noncomputable def projectiveSpaceToBase (n : Nat) :
    projectiveSpace n ⟶ complexBase :=
  Proj.toSpecZero (ProjectiveGrading n) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (ProjectiveGrading n 0)))

/-- A fully geometric witness that a given complex-scheme structure map is
projective: the source embeds as a closed subscheme of an actual standard
projective space and the embedding commutes with the canonical projective
space structure morphism to Spec(C). -/
structure ProjectiveOverC
    (X : Scheme) (structureMap : X ⟶ complexBase) where
  n : Nat
  immersion : X ⟶ projectiveSpace n
  closedImmersion : IsClosedImmersion immersion
  over_base : immersion ≫ projectiveSpaceToBase n = structureMap

/-- The exact geometric carrier for the classical Hodge statement used by
Stage 2E: an actual complex scheme with actual smoothness and an actual
closed projective embedding witness. -/
structure SmoothProjectiveComplexScheme where
  X : Scheme
  structureMap : X ⟶ complexBase
  smooth : Smooth structureMap
  projective : ProjectiveOverC X structureMap

instance (V : SmoothProjectiveComplexScheme) : Smooth V.structureMap :=
  V.smooth

theorem projective_closed_immersion
    (V : SmoothProjectiveComplexScheme) :
    IsClosedImmersion V.projective.immersion :=
  V.projective.closedImmersion

theorem projective_embedding_over_base
    (V : SmoothProjectiveComplexScheme) :
    V.projective.immersion ≫
      projectiveSpaceToBase V.projective.n = V.structureMap :=
  V.projective.over_base

/-- Every smooth projective complex scheme exports its projective witness
as an ordinary existential factorization.  Downstream stages can consume the
geometry without destructing the bundled certificate manually. -/
theorem exists_closed_projective_embedding
    (V : SmoothProjectiveComplexScheme) :
    ∃ n : Nat, ∃ f : V.X ⟶ projectiveSpace n,
      IsClosedImmersion f ∧
        f ≫ projectiveSpaceToBase n = V.structureMap := by
  exact ⟨V.projective.n, V.projective.immersion,
    V.projective.closedImmersion, V.projective.over_base⟩

/-- **SMOOTH-PROJECTIVE GEOMETRY CROWN.**  The geometric carrier exposes
smoothness and an actual closed projective factorization over Spec(C) at the
same time. -/
theorem smooth_projective_geometry_crown
    (V : SmoothProjectiveComplexScheme) :
    Smooth V.structureMap ∧
      ∃ n : Nat, ∃ f : V.X ⟶ projectiveSpace n,
        IsClosedImmersion f ∧
          f ≫ projectiveSpaceToBase n = V.structureMap := by
  exact ⟨V.smooth, exists_closed_projective_embedding V⟩

#check complexBase
#check ProjectiveCoordinateRing
#check ProjectiveGrading
#check projectiveSpace
#check projectiveSpaceToBase
#check ProjectiveOverC
#check SmoothProjectiveComplexScheme
#check projective_closed_immersion
#check projective_embedding_over_base
#check exists_closed_projective_embedding
#check smooth_projective_geometry_crown

#print axioms projective_closed_immersion
#print axioms projective_embedding_over_base
#print axioms exists_closed_projective_embedding
#print axioms smooth_projective_geometry_crown

end GSTProjectiveOverC
