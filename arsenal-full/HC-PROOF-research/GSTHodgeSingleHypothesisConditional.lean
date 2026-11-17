import GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
import GSTClassicalHodgeGeometricKrylovMomentDeterminant
import GSTClassicalHodgeExactClayStatement

/-!
# GST Hodge: a single explicit geometric hypothesis

This module does NOT assert the existence of the required geometry.
It isolates one unified target instead of separately requiring F/G/D/R.

The rank-free target, `NativeGSTSingleFoldOrbitLaw`, asks for ONE
genuinely realized native/cohomological correspondence word and ONE genuine
algebraic native seed at every Hodge weight, with cyclic orbit.  The
corrected canonical geometry, if established, must instantiate `H`;
the abstract Stage-2G package still permits a noncanonical `cycleClass`.

The stronger, numerically falsifiable target,
`NativeGSTSingleFoldDeterminantLaw`, asks for a finite-dimensional
Hodge instance and the existing single-fold rational Hankel determinant
certificate.  Both conditional consequences reuse the repository's
already proved actual-native orbit and matrix inversion mathematics.

For the exact moment-only constructive expression (rather than the
basis-coordinate inverse used in the old Krylov proof), see
research/derivations/GST_single_hypothesis_fold_moment_conditional_2026_11_08.tex.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeGeometricKrylovMomentDeterminant
open GSTClassicalHodgeExactClayStatement

namespace GSTHodgeSingleHypothesisConditional

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}

/-- The ONE source-bearing GST geometric hypothesis: a realized native fold
correspondence with a cyclic algebraic orbit in every Hodge weight.

The realized correspondence certificate contains an actual native cycle
operator and an exact cycle-class commuting square, not a free linear
operator or a preselected Hodge-to-Chow inverse. -/
def NativeGSTSingleFoldOrbitLaw
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∀ p : Nat,
    ∃ C : RealizedCorrespondenceKrylovCertificate V H p,
      C.IsKrylovCyclic

/-- CONDITIONAL EXACT HODGE: one GST orbit law implies that each prescribed
rational (p,p) class is the class of an actual native codimension-p cycle.
No global native-mass law, per-weight arbitrary basis cycles, two-generator
self-map family, or separate geometric spine is assumed here. -/
theorem exactHodge_of_one_GST_fold_orbit
    (h : NativeGSTSingleFoldOrbitLaw V H) :
    EveryHodgeClassIsRationalAlgebraic H := by
  intro p alpha halpha
  obtain ⟨C, hcyc⟩ := h p
  exact C.exists_cycle hcyc alpha halpha

/-- The literal finite-rational-algebraic-cycle wording from the SAME
single hypothesis. -/
theorem finiteRationalCombination_of_one_GST_fold_orbit
    (h : NativeGSTSingleFoldOrbitLaw V H) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  exact (rationalAlgebraic_iff_finiteRationalCombination H).mp
    (exactHodge_of_one_GST_fold_orbit h)

/-- The ONE scalar-certificate version.  The finiteness data are deliberately
VISIBLE inside the named hypothesis: the abstract Stage-2G structure does not
itself construct analytically correct finite-dimensional Hodge theory.
For the genuine smooth-projective geometric instance, finiteness is standard;
a canonical-data instantiation is still an explicit formalization obligation.

The nonzero determinant is the genuine hard geometry; it is NOT proved here. -/
def NativeGSTSingleFoldDeterminantLaw
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) : Prop :=
  ∃ F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H,
    UniversalGSTKrylovHankelNondegeneracy F

/-- CONDITIONAL EXACT HODGE FROM THE ONE SCALAR LAW.  The target has the
same original-X rational native cycle semantics as the existing exact
Clay-style statement; it remains parameterized by the supplied Hodge data. -/
theorem exactHodge_of_one_GST_fold_determinant
    (h : NativeGSTSingleFoldDeterminantLaw V H) :
    EveryHodgeClassIsRationalAlgebraic H := by
  obtain ⟨F, hdet⟩ := h
  exact full_hodge_of_universal_Krylov_Hankel_geometry F hdet

/-- The finite-sum original-X cycle form of the scalar-law conditional
theorem, with no additional assumptions. -/
theorem finiteRationalCombination_of_one_GST_fold_determinant
    (h : NativeGSTSingleFoldDeterminantLaw V H) :
    EveryHodgeClassIsFiniteRationalCombination H := by
  exact (rationalAlgebraic_iff_finiteRationalCombination H).mp
    (exactHodge_of_one_GST_fold_determinant h)

#check NativeGSTSingleFoldOrbitLaw
#check exactHodge_of_one_GST_fold_orbit
#check finiteRationalCombination_of_one_GST_fold_orbit
#check NativeGSTSingleFoldDeterminantLaw
#check exactHodge_of_one_GST_fold_determinant
#check finiteRationalCombination_of_one_GST_fold_determinant
#print axioms exactHodge_of_one_GST_fold_orbit
#print axioms exactHodge_of_one_GST_fold_determinant

end GSTHodgeSingleHypothesisConditional
