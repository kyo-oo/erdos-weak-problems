import GSTCardinalHilbertComponentSource
import Mathlib

/-!
# GST cardinal topology + N-cohomology: graded original-X incidence birth

The user's actual cardinal proposal uses the COHOMOLOGY of an indexed
source world, not just a list of fibers / component labels.

Geometry (outside Lean in companion derivation):
For smooth projective source Y, dim=m, smooth projective original X,
a TRUE algebraic incidence Gamma in CH^c(Y x X), and an actual native
source class z in CH^q(Y), Chow push-pull produces
  Gamma_*(z) in CH^(c+q-m)(X).
The canonical Betti action obeys the corresponding graded square.
Therefore the equation
  c + q = m + p
is the REQUIRED native codimension equation when target is CH^p(X).

The powerful no-go for a universal family of p-cycles (c=p) is:
to land in codim p, a source class must have TOP codim q=m.
But lower-degree source cohomology can land in LOWER codimension
on X: on the point Hilbert family of X the universal diagonal
acts on ALL degrees, despite every point fiber having one class.

This file formalizes the graded dependence, heterogeneous source
worlds and the noncircular source-span implication. Real algebraic
incidences and actual native sources are EXPLICIT inputs; no target
Hodge class is assumed to have a Chow inverse, and no full-rank
geometric incidence is falsely declared to exist for all original X.
-/

set_option maxHeartbeats 1500000
noncomputable section

namespace GSTCardinalGradedIncidenceBirth

universe u v w x y

variable {I : Type u} {A : Type v} {B : Type w}
variable [AddCommGroup A] [Module ℚ A]
variable [AddCommGroup B] [Module ℚ B]

/-- An arbitrary-cardinality set of TRUE heterogeneous geometric
source worlds, all landing on the SAME original-X Chow and Hodge
carriers. All cohomological gradings are explicitly checked. -/
structure GradedIncidenceAtlas (I : Type u)
    (A : Type v) (B : Type w)
    [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] where
  NativeSource : I → Type x
  HodgeSource : I → Type y
  sourceCycleClass : (i : I) → NativeSource i → HodgeSource i
  source : (i : I) → NativeSource i
  nativeLanding : (i : I) → NativeSource i → A
  bettiLanding : (i : I) → HodgeSource i → B
  targetCycleClass : A →ₗ[ℚ] B
  canonicalSquare :
    ∀ (i : I) (z : NativeSource i),
      targetCycleClass (nativeLanding i z) =
        bettiLanding i (sourceCycleClass i z)
  sourceDimension : I → ℕ
  sourceCodimension : I → ℕ
  correspondenceCodimension : I → ℕ
  targetCodimension : ℕ
  degreeLaw :
    ∀ i : I, correspondenceCodimension i + sourceCodimension i =
      sourceDimension i + targetCodimension

namespace GradedIncidenceAtlas

variable (F : GradedIncidenceAtlas I A B)

def landedNative (i : I) : A := F.nativeLanding i (F.source i)

def landedHodge (i : I) : B :=
  F.bettiLanding i (F.sourceCycleClass i (F.source i))

/-- Actual Betti class of every born source on the original X. -/
theorem landed_class (i : I) :
    F.targetCycleClass (F.landedNative i) = F.landedHodge i :=
  F.canonicalSquare i (F.source i)

/-- An exact cohomological GRADING firewall: a family of codimension-p
cycles on original X, with the incidence itself of codimension p,
can contribute to W_p(X) only from source-world TOP codimension.
Its lower-degree cohomology may still contribute to LOWER weights! -/
theorem top_degree_necessary_for_same_codimension
    (i : I)
    (hfamily : F.correspondenceCodimension i =
      F.targetCodimension) :
    F.sourceCodimension i = F.sourceDimension i := by
  have h := F.degreeLaw i
  omega

/-- A general incidence cannot output a higher Chow codimension than
its own incidence codimension when the source input q is within
the geometric range 0 <= q <= dim(source). -/
theorem output_codimension_bound
    (i : I) (hsource : F.sourceCodimension i ≤ F.sourceDimension i) :
    F.targetCodimension ≤ F.correspondenceCodimension i := by
  have h := F.degreeLaw i
  omega

/-- Canonical original-X native result from all cardinal worlds:
if the BETTI images of independently constructed native incidence
cycles span the entire TARGET Hodge space, then the actual canonical
target cycle-class map is surjective.

This is a conditional noncircular sufficient criterion. The key
unverified input is the FULL-RANK geometric atlas, not the theorem's
linear algebra or the existence of arbitrary cardinal indices. -/
theorem originalX_hodge_of_incidence_source_span
    (hcover : Submodule.span ℚ (Set.range F.landedHodge) = ⊤) :
    Function.Surjective F.targetCycleClass := by
  have hsub :
      Submodule.span ℚ (Set.range F.landedHodge) ≤
        LinearMap.range F.targetCycleClass := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact ⟨F.landedNative i, F.landed_class i⟩
  rw [hcover] at hsub
  intro beta
  have hbeta : beta ∈ LinearMap.range F.targetCycleClass :=
    hsub (Submodule.mem_top)
  exact hbeta

end GradedIncidenceAtlas

#check GradedIncidenceAtlas.top_degree_necessary_for_same_codimension
#check GradedIncidenceAtlas.output_codimension_bound
#check GradedIncidenceAtlas.landed_class
#check GradedIncidenceAtlas.originalX_hodge_of_incidence_source_span

#print axioms GradedIncidenceAtlas.top_degree_necessary_for_same_codimension
#print axioms GradedIncidenceAtlas.output_codimension_bound
#print axioms GradedIncidenceAtlas.originalX_hodge_of_incidence_source_span

end GSTCardinalGradedIncidenceBirth
