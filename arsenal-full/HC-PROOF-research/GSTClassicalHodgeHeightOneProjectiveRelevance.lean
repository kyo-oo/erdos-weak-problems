import GSTClassicalHodgeProjectiveSeparatorHeightOne
import GSTClassicalHodgeHomogeneousMinimalPrime
import Mathlib.RingTheory.Ideal.Height

/-!
# GST CLASSICAL HODGE — HEIGHT-ONE PROJECTIVE RELEVANCE

A height-one minimal prime over the source-specific homogeneous separator gives
a genuine codimension-one component in the source-prime quotient.  To turn it
back into a point of `Proj`, it must remain relevant: it must not contain the
irrelevant ideal.

This file isolates the exact dimension argument.  Map the ambient irrelevant
ideal to the source-prime quotient.  If that image has height at least two,
then no height-one prime can contain it, by monotonicity of ideal height.
Hence every height-one separator component is automatically projectively
relevant.

The condition is precisely the positive-dimensional projective-source
condition in algebraic form.  It intentionally fails at a zero-dimensional
projective source, where a positive-degree section may have empty zero locus.
No Hodge data occurs.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectiveSeparatorKrull
open GSTClassicalHodgeProjectiveSeparatorHeightOne

namespace GSTClassicalHodgeHeightOneProjectiveRelevance

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Image of the projective irrelevant ideal in the homogeneous source-prime
quotient. -/
noncomputable def quotientIrrelevant
    (n : Nat) (x : projectiveSpace n) :
    Ideal (pointQuotient n x) :=
  Ideal.map (Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal)
    (HomogeneousIdeal.irrelevant (ProjectiveGrading n)).toIdeal

/-- Algebraic live-dimension condition for the projective source: its
irrelevant ideal still has height at least two after quotienting by the source
prime. -/
def ProjectivelyLiveSource
    (n : Nat) (x : projectiveSpace n) : Prop :=
  (2 : ℕ∞) ≤ (quotientIrrelevant n x).height

/-- A height-one prime cannot contain an ideal of height at least two. -/
theorem heightOnePrime_avoids_heightTwoIdeal
    {R : Type*} [CommRing R]
    {J Q : Ideal R}
    (hJ : (2 : ℕ∞) ≤ J.height)
    (hQ : Q.height = 1) :
    ¬ J ≤ Q := by
  intro hle
  have hmono : J.height ≤ Q.height := Ideal.height_mono hle
  rw [hQ] at hmono
  have : (2 : ℕ∞) ≤ 1 := hJ.trans hmono
  norm_num at this

/-- Therefore every height-one prime in a live source quotient avoids the
projective irrelevant image. -/
theorem heightOnePrime_avoids_quotientIrrelevant
    (n : Nat) (x : projectiveSpace n)
    (hlive : ProjectivelyLiveSource n x)
    {q : Ideal (pointQuotient n x)}
    (hq : q.height = 1) :
    ¬ quotientIrrelevant n x ≤ q := by
  exact heightOnePrime_avoids_heightTwoIdeal hlive hq

/-- If an ambient ideal contains the irrelevant ideal, then its quotient image
contains the quotient irrelevant ideal.  This is the map/comap adapter used to
turn the height argument into `Proj` relevance. -/
theorem quotientIrrelevant_le_of_irrelevant_le_comap
    (n : Nat) (x : projectiveSpace n)
    (q : Ideal (pointQuotient n x))
    (h :
      (HomogeneousIdeal.irrelevant (ProjectiveGrading n)).toIdeal ≤
        Ideal.comap (Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal) q) :
    quotientIrrelevant n x ≤ q := by
  exact (Ideal.map_le_iff_le_comap).2 h

/-- **HEIGHT-ONE RELEVANCE CROWN.**
At a projectively live source, the comap of every height-one quotient prime is
relevant in the underlying projective coordinate ring. -/
theorem heightOnePrime_comap_not_irrelevant
    (n : Nat) (x : projectiveSpace n)
    (hlive : ProjectivelyLiveSource n x)
    (q : Ideal (pointQuotient n x))
    (hq : q.height = 1) :
    ¬ (HomogeneousIdeal.irrelevant (ProjectiveGrading n)).toIdeal ≤
        Ideal.comap (Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal) q := by
  intro hbad
  exact heightOnePrime_avoids_quotientIrrelevant n x hlive hq
    (quotientIrrelevant_le_of_irrelevant_le_comap n x q hbad)

#check quotientIrrelevant
#check ProjectivelyLiveSource
#check heightOnePrime_avoids_heightTwoIdeal
#check heightOnePrime_avoids_quotientIrrelevant
#check heightOnePrime_comap_not_irrelevant

#print axioms heightOnePrime_avoids_heightTwoIdeal
#print axioms heightOnePrime_comap_not_irrelevant

end GSTClassicalHodgeHeightOneProjectiveRelevance
