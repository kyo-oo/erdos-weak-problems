import GSTClassicalHodgeProjectiveSeparatorHeightOne
import GSTClassicalHodgeHomogeneousMinimalPrime
import GSTClassicalHodgeHeightOneProjectiveRelevance
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# GST CLASSICAL HODGE — GENUINE PROJECTIVE SEPARATOR SUCCESSOR

The source-specific positive homogeneous separator survives as a nonzero
nonunit in the quotient by the source projective prime.  Krull's theorem gives
a height-one minimal prime over that principal ideal.  The previous two layers
show that:

* its pullback to the ambient projective coordinate ring is a homogeneous
  minimal prime over the source prime plus the separator equation;
* at a projectively live source it remains relevant, because a height-one
  prime cannot contain the quotient irrelevant ideal of height at least two.

Therefore the separator does not merely define an abstract height-one ideal:
it produces an actual new point of `Proj`, strictly specialized from the source
and lying on the chosen principal section.

No Hodge class, cycle-class map, or algebraicity conclusion is used.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgeProjectivePrincipalSection
open GSTClassicalHodgeProjectiveSeparatorKrull
open GSTClassicalHodgeProjectiveSeparatorHeightOne
open GSTClassicalHodgeHomogeneousMinimalPrime
open GSTClassicalHodgeHeightOneProjectiveRelevance

namespace GSTClassicalHodgeProjectiveSeparatorSuccessorPoint

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Principal separator ideal in the source-prime quotient. -/
noncomputable def separatorQuotientIdeal
    (n : Nat) (x : projectiveSpace n) : Ideal (pointQuotient n x) :=
  Ideal.span ({separatorClass n x} : Set (pointQuotient n x))

/-- The quotient separator ideal is proper because the separator class is a
nonunit. -/
theorem separatorQuotientIdeal_ne_top
    (n : Nat) (x : projectiveSpace n) :
    separatorQuotientIdeal n x ≠ ⊤ := by
  simpa [separatorQuotientIdeal] using
    (Ideal.span_singleton_ne_top (separatorClass_not_isUnit n x))

/-- Choose one minimal prime over the surviving separator. -/
noncomputable def separatorMinimalPrimeWitness
    (n : Nat) (x : projectiveSpace n) :
    {I : Ideal (pointQuotient n x) //
      I ∈ (separatorQuotientIdeal n x).minimalPrimes} :=
  Classical.choice
    (Nonempty.elim (Ideal.nonempty_minimalPrimes
      (separatorQuotientIdeal_ne_top n x))
      (fun p => ⟨⟨p.1, p.2⟩⟩))

noncomputable def separatorMinimalPrime
    (n : Nat) (x : projectiveSpace n) : Ideal (pointQuotient n x) :=
  (separatorMinimalPrimeWitness n x).1

/-- Receipt that the chosen quotient prime is genuinely minimal over the
separator ideal. -/
theorem separatorMinimalPrime_mem
    (n : Nat) (x : projectiveSpace n) :
    separatorMinimalPrime n x ∈ (separatorQuotientIdeal n x).minimalPrimes :=
  (separatorMinimalPrimeWitness n x).2

/-- The chosen quotient prime has exact height one. -/
theorem separatorMinimalPrime_height_one
    (n : Nat) (x : projectiveSpace n) :
    (separatorMinimalPrime n x).height = 1 := by
  exact separator_minimalPrime_prime_height_one n x
    (by simpa [separatorQuotientIdeal] using separatorMinimalPrime_mem n x)

/-- Pull the height-one separator component back to the ambient homogeneous
coordinate ring. -/
noncomputable def separatorAmbientPrime
    (n : Nat) (x : projectiveSpace n) : Ideal (ProjectiveCoordinateRing n) :=
  Ideal.comap (Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal)
    (separatorMinimalPrime n x)

/-- The source prime lies below the pulled-back successor prime. -/
theorem sourcePrime_le_separatorAmbientPrime
    (n : Nat) (x : projectiveSpace n) :
    x.asHomogeneousIdeal.toIdeal ≤ separatorAmbientPrime n x := by
  intro a ha
  change Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal a ∈
    separatorMinimalPrime n x
  have h0 : Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal a = 0 :=
    (Submodule.Quotient.mk_eq_zero x.asHomogeneousIdeal.toIdeal).mpr ha
  rw [h0]
  exact zero_mem _

/-- The pulled-back successor prime is prime. -/
theorem separatorAmbientPrime_isPrime
    (n : Nat) (x : projectiveSpace n) :
    (separatorAmbientPrime n x).IsPrime := by
  exact (separatorMinimalPrime_mem n x).isPrime.comap
    (Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal)

/-- The separator equation lies in the ambient successor prime. -/
theorem separator_mem_separatorAmbientPrime
    (n : Nat) (x : projectiveSpace n) :
    (positiveHomogeneousSeparator n x).equation ∈ separatorAmbientPrime n x := by
  change separatorClass n x ∈ separatorMinimalPrime n x
  exact (separatorMinimalPrime_mem n x).le (Ideal.subset_span (Set.mem_singleton _))

/-- The ambient successor is strictly above the source prime because the
separator was chosen outside the source prime but lies in the successor. -/
theorem sourcePrime_lt_separatorAmbientPrime
    (n : Nat) (x : projectiveSpace n) :
    x.asHomogeneousIdeal.toIdeal < separatorAmbientPrime n x := by
  refine lt_of_le_of_ne (sourcePrime_le_separatorAmbientPrime n x) ?_
  intro hEq
  have hmem :
      (positiveHomogeneousSeparator n x).equation ∈ x.asHomogeneousIdeal := by
    show (positiveHomogeneousSeparator n x).equation ∈
      x.asHomogeneousIdeal.toIdeal
    rw [hEq]
    exact separator_mem_separatorAmbientPrime n x
  exact (positiveHomogeneousSeparator n x).not_mem_prime hmem

/-- The pulled-back prime is minimal over the homogeneous ideal generated by
source prime plus separator equation. -/
theorem separatorAmbientPrime_mem_minimalPrimes
    (n : Nat) (x : projectiveSpace n) :
    separatorAmbientPrime n x ∈
      (x.asHomogeneousIdeal.toIdeal ⊔
        Ideal.span ({(positiveHomogeneousSeparator n x).equation} :
          Set (ProjectiveCoordinateRing n))).minimalPrimes := by
  let P := x.asHomogeneousIdeal.toIdeal
  let J : Ideal (ProjectiveCoordinateRing n) :=
    Ideal.span ({(positiveHomogeneousSeparator n x).equation} :
      Set (ProjectiveCoordinateRing n))
  let Q := separatorAmbientPrime n x
  haveI : Q.IsPrime := separatorAmbientPrime_isPrime n x
  have hP : P ≤ Q := sourcePrime_le_separatorAmbientPrime n x
  apply Ideal.mem_minimalPrimes_sup hP
  have hmapQ : Q.map (Ideal.Quotient.mk P) = separatorMinimalPrime n x := by
    unfold Q separatorAmbientPrime P
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  have hmapJ : J.map (Ideal.Quotient.mk P) = separatorQuotientIdeal n x := by
    rw [separatorQuotientIdeal, separatorClass]
    simp [J, Ideal.map_span, Set.image_singleton]
    rfl
  rw [hmapQ, hmapJ]
  exact separatorMinimalPrime_mem n x

/-- The source-plus-separator ideal is homogeneous. -/
theorem sourceSeparatorIdeal_isHomogeneous
    (n : Nat) (x : projectiveSpace n) :
    (x.asHomogeneousIdeal.toIdeal ⊔
      Ideal.span ({(positiveHomogeneousSeparator n x).equation} :
        Set (ProjectiveCoordinateRing n))).IsHomogeneous
      (ProjectiveGrading n) := by
  apply Ideal.IsHomogeneous.sup x.asHomogeneousIdeal.isHomogeneous
  apply Ideal.homogeneous_span
  intro f hf
  simp only [Set.mem_singleton_iff] at hf
  subst f
  exact ⟨(positiveHomogeneousSeparator n x).degree,
    (positiveHomogeneousSeparator n x).homogeneous⟩

/-- The ambient successor prime is therefore itself homogeneous. -/
theorem separatorAmbientPrime_isHomogeneous
    (n : Nat) (x : projectiveSpace n) :
    (separatorAmbientPrime n x).IsHomogeneous (ProjectiveGrading n) := by
  exact minimalPrime_isHomogeneous
    (sourceSeparatorIdeal_isHomogeneous n x)
    (separatorAmbientPrime_mem_minimalPrimes n x)

/-- Bundled homogeneous successor prime. -/
noncomputable def separatorAmbientHomogeneousPrime
    (n : Nat) (x : projectiveSpace n) :
    HomogeneousIdeal (ProjectiveGrading n) :=
  ⟨separatorAmbientPrime n x, separatorAmbientPrime_isHomogeneous n x⟩

/-- In the projectively live case, the homogeneous successor prime remains
relevant and therefore determines an actual point of Proj. -/
theorem separatorAmbientPrime_not_irrelevant
    (n : Nat) (x : projectiveSpace n)
    (hlive : ProjectivelyLiveSource n x) :
    ¬ HomogeneousIdeal.irrelevant (ProjectiveGrading n) ≤
        separatorAmbientHomogeneousPrime n x := by
  intro hbad
  have hbadIdeal :
      (HomogeneousIdeal.irrelevant (ProjectiveGrading n)).toIdeal ≤
        separatorAmbientPrime n x := hbad
  have hquot : quotientIrrelevant n x ≤ separatorMinimalPrime n x :=
    (Ideal.map_le_iff_le_comap).2 hbadIdeal
  exact heightOnePrime_avoids_quotientIrrelevant n x hlive
    (separatorMinimalPrime_height_one n x) hquot

/-- **GENUINE PROJECTIVE SUCCESSOR POINT.** -/
noncomputable def separatorSuccessorPoint
    (n : Nat) (x : projectiveSpace n)
    (hlive : ProjectivelyLiveSource n x) : projectiveSpace n where
  asHomogeneousIdeal := separatorAmbientHomogeneousPrime n x
  isPrime := separatorAmbientPrime_isPrime n x
  not_irrelevant_le := separatorAmbientPrime_not_irrelevant n x hlive

/-- The successor point contains the source homogeneous prime. -/
theorem source_le_separatorSuccessorPoint
    (n : Nat) (x : projectiveSpace n)
    (hlive : ProjectivelyLiveSource n x) :
    x.asHomogeneousIdeal.toIdeal ≤
      (separatorSuccessorPoint n x hlive).asHomogeneousIdeal.toIdeal :=
  sourcePrime_le_separatorAmbientPrime n x

/-- The successor is genuinely distinct from the source. -/
theorem separatorSuccessorPoint_ne_source
    (n : Nat) (x : projectiveSpace n)
    (hlive : ProjectivelyLiveSource n x) :
    separatorSuccessorPoint n x hlive ≠ x := by
  intro h
  have hIdeal := congrArg
    (fun z : projectiveSpace n => z.asHomogeneousIdeal.toIdeal) h
  exact ne_of_lt (sourcePrime_lt_separatorAmbientPrime n x) hIdeal.symm

/-- The separator vanishes at the successor point, so the successor lies on
its genuine projective principal zero locus. -/
theorem separatorSuccessorPoint_mem_principalSet
    (n : Nat) (x : projectiveSpace n)
    (hlive : ProjectivelyLiveSource n x) :
    separatorSuccessorPoint n x hlive ∈
      projectivePrincipalSet n (positiveHomogeneousSeparator n x).equation := by
  show (separatorSuccessorPoint n x hlive :
      ProjectiveSpectrum (ProjectiveGrading n)) ∈
    ProjectiveSpectrum.zeroLocus (ProjectiveGrading n)
      ({(positiveHomogeneousSeparator n x).equation} :
        Set (ProjectiveCoordinateRing n))
  refine ((ProjectiveSpectrum.mem_zeroLocus
      (ProjectiveGrading n)
      (separatorSuccessorPoint n x hlive)
      ({(positiveHomogeneousSeparator n x).equation} :
        Set (ProjectiveCoordinateRing n))).trans
    Set.singleton_subset_iff).mpr ?_
  exact separator_mem_separatorAmbientPrime n x

/-- Projective successor crown. -/
theorem projective_separator_successor_crown
    (n : Nat) (x : projectiveSpace n)
    (hlive : ProjectivelyLiveSource n x) :
    x.asHomogeneousIdeal.toIdeal <
        (separatorSuccessorPoint n x hlive).asHomogeneousIdeal.toIdeal
      ∧ separatorSuccessorPoint n x hlive ∈
        projectivePrincipalSet n (positiveHomogeneousSeparator n x).equation := by
  exact ⟨sourcePrime_lt_separatorAmbientPrime n x,
    separatorSuccessorPoint_mem_principalSet n x hlive⟩

#check separatorMinimalPrime
#check separatorMinimalPrime_height_one
#check separatorAmbientPrime
#check separatorAmbientPrime_mem_minimalPrimes
#check separatorAmbientPrime_isHomogeneous
#check separatorSuccessorPoint
#check separatorSuccessorPoint_ne_source
#check separatorSuccessorPoint_mem_principalSet
#check projective_separator_successor_crown

#print axioms separatorAmbientPrime_mem_minimalPrimes
#print axioms separatorAmbientPrime_isHomogeneous
#print axioms separatorSuccessorPoint
#print axioms projective_separator_successor_crown

end GSTClassicalHodgeProjectiveSeparatorSuccessorPoint
