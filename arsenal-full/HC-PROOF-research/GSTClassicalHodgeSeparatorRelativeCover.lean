import GSTClassicalHodgeSeparatorRelativeCutLanding
import GSTClassicalHodgeSeparatorAmbientPrimeInterval
import GSTClassicalHodgeRelativeSuccessorLowerBound

/-!
# GST CLASSICAL HODGE — RELATIVE COVER OF THE SEPARATOR SUCCESSOR

The quotient separator prime has height one, hence the ambient projective prime
interval between source and successor has only its two endpoints.  This file
transports that interval collapse into the specialization order of the reduced
source-closure scheme.

The result is stronger than a numerical coheight statement: every strict
generalization of the lifted separator successor is the canonical generic
source point.  Thus the successor is covered by the generic point.

No Hodge datum occurs.
-/

set_option maxHeartbeats 50000000
set_option maxRecDepth 1000000

noncomputable section

open TopologicalSpace
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTClassicalHodgePointClosurePrincipalCut
open GSTClassicalHodgePointClosureIrreducible
open GSTClassicalHodgeRelativeSuccessorLowerBound
open GSTClassicalHodgeHeightOneProjectiveRelevance
open GSTClassicalHodgeProjectiveSeparatorSuccessorPoint
open GSTClassicalHodgeProjectiveSeparatorCarrierDescent
open GSTClassicalHodgeSeparatorPointClosureLift
open GSTClassicalHodgeSeparatorAmbientPrimeInterval

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GSTClassicalHodgeSeparatorRelativeCover

attribute [local instance] specializationOrder

/-- Projective specialization is exactly reverse inclusion of the underlying
homogeneous prime ideals. -/
theorem projective_le_iff_prime_reverse_le
    {n : Nat} {a b : projectiveSpace n} :
    a ≤ b ↔ b.asHomogeneousIdeal.toIdeal ≤ a.asHomogeneousIdeal.toIdeal := by
  rw [specializationOrder_iff_specializes]
  have key : ∀ (a b : ProjectiveSpectrum (ProjectiveGrading n)),
      a ∈ closure ({b} : Set (ProjectiveSpectrum (ProjectiveGrading n))) ↔
        b.asHomogeneousIdeal.toIdeal ≤ a.asHomogeneousIdeal.toIdeal := by
    intro a b
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    exact ProjectiveSpectrum.mem_zeroLocus _ _ _
  exact key a b

/-- Every point of the reduced source closure maps to a projective prime above
(the ideal-theoretic sense) the source projective prime. -/
theorem sourcePrime_le_projectiveImage_of_pointClosure
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (z : pointClosureScheme V x) :
    (V.projective.immersion x).asHomogeneousIdeal.toIdeal ≤
      (V.projective.immersion (pointClosureι V x z)).asHomogeneousIdeal.toIdeal := by
  have hzCarrier : pointClosureι V x z ≤ x :=
    pointClosure_image_le_source V x z
  have hzProj :
      V.projective.immersion (pointClosureι V x z) ≤
        V.projective.immersion x :=
    V.projective.immersion.continuous.specialization_monotone hzCarrier
  exact (projective_le_iff_prime_reverse_le).mp hzProj

/-- A point above the separator successor in the source closure has projective
prime below the separator successor prime. -/
theorem projectiveImage_le_separatorPrime_of_successor_le
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x))
    (z : pointClosureScheme V x)
    (hz : pointClosureSeparatorSuccessor V x hlive ≤ z) :
    (V.projective.immersion (pointClosureι V x z)).asHomogeneousIdeal.toIdeal ≤
      separatorAmbientPrime V.projective.n (V.projective.immersion x) := by
  have hzCarrier :
      pointClosureι V x (pointClosureSeparatorSuccessor V x hlive) ≤
        pointClosureι V x z :=
    (pointClosureι V x).continuous.specialization_monotone hz
  have hzProj :
      V.projective.immersion
          (pointClosureι V x (pointClosureSeparatorSuccessor V x hlive)) ≤
        V.projective.immersion (pointClosureι V x z) :=
    V.projective.immersion.continuous.specialization_monotone hzCarrier
  have hprime := (projective_le_iff_prime_reverse_le).mp hzProj
  rw [pointClosureSeparatorSuccessor_maps,
    carrierSeparatorSuccessor_image] at hprime
  exact hprime

/-- **UNIQUE STRICT GENERALIZATION.**
Every point strictly above the lifted separator successor is the canonical
generic point of the reduced source closure. -/
theorem strictAbove_separatorSuccessor_eq_generic
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x))
    (z : pointClosureScheme V x)
    (hz : pointClosureSeparatorSuccessor V x hlive < z) :
    z = closureGenericPoint V x := by
  let R : Ideal (ProjectiveCoordinateRing V.projective.n) :=
    (V.projective.immersion (pointClosureι V x z)).asHomogeneousIdeal.toIdeal
  have hRPrime : R.IsPrime :=
    (V.projective.immersion (pointClosureι V x z)).isPrime
  have hsource :
      (V.projective.immersion x).asHomogeneousIdeal.toIdeal ≤ R :=
    sourcePrime_le_projectiveImage_of_pointClosure V x z
  have hsucc : R ≤
      separatorAmbientPrime V.projective.n (V.projective.immersion x) :=
    projectiveImage_le_separatorPrime_of_successor_le V x hlive z hz.le
  rcases prime_between_source_separator_eq_endpoint
      V.projective.n (V.projective.immersion x) R hRPrime hsource hsucc with
    hRsource | hRsucc
  · have hProjEq :
        V.projective.immersion (pointClosureι V x z) =
          V.projective.immersion x := by
      apply ProjectiveSpectrum.ext
      exact HomogeneousIdeal.ext hRsource
    have hCarrier : pointClosureι V x z = x := by
      letI : IsClosedImmersion V.projective.immersion :=
        V.projective.closedImmersion
      exact V.projective.immersion.isEmbedding.injective hProjEq
    apply (pointClosureι V x).isEmbedding.injective
    rw [hCarrier, closureGenericPoint_maps_to_source]
  · have hProjEq :
        V.projective.immersion (pointClosureι V x z) =
          separatorSuccessorPoint V.projective.n (V.projective.immersion x) hlive := by
      apply ProjectiveSpectrum.ext
      exact HomogeneousIdeal.ext hRsucc
    have hCarrier :
        pointClosureι V x z = carrierSeparatorSuccessor V x hlive := by
      letI : IsClosedImmersion V.projective.immersion :=
        V.projective.closedImmersion
      apply V.projective.immersion.isEmbedding.injective
      rw [hProjEq, carrierSeparatorSuccessor_image]
    have hzEq : z = pointClosureSeparatorSuccessor V x hlive := by
      apply (pointClosureι V x).isEmbedding.injective
      rw [hCarrier, pointClosureSeparatorSuccessor_maps]
    exact (ne_of_lt hz) hzEq.symm |>.elim

/-- No three-point specialization chain starts at the separator successor:
there is no point strictly between it and its unique generic generalization. -/
theorem no_intermediate_above_separatorSuccessor
    (V : SmoothProjectiveComplexScheme)
    (x : V.X)
    (hlive : ProjectivelyLiveSource V.projective.n (V.projective.immersion x)) :
    ∀ z : pointClosureScheme V x,
      pointClosureSeparatorSuccessor V x hlive < z →
        z = closureGenericPoint V x := by
  intro z hz
  exact strictAbove_separatorSuccessor_eq_generic V x hlive z hz

#check projective_le_iff_prime_reverse_le
#check sourcePrime_le_projectiveImage_of_pointClosure
#check projectiveImage_le_separatorPrime_of_successor_le
#check strictAbove_separatorSuccessor_eq_generic
#check no_intermediate_above_separatorSuccessor

#print axioms projective_le_iff_prime_reverse_le
#print axioms strictAbove_separatorSuccessor_eq_generic
#print axioms no_intermediate_above_separatorSuccessor

end GSTClassicalHodgeSeparatorRelativeCover
