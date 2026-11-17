import GSTClassicalHodgeLocalRegularCutDimension
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# GST CLASSICAL HODGE — RADICAL PRINCIPAL-CUT DIMENSION

The actual projective principal-section geometry in the Hodge route is reduced:
its local defining ideal is the radical of the raw one-equation ideal.  The
existing local regular-cut theorem gives the exact Krull-dimension drop for the
raw principal quotient.  This file proves that passing to the radical does not
change quotient Krull dimension, because both quotients have the same ordered
prime spectrum / zero locus.

Consequently a reduced principal cut by one nonzero nonunit equation in a
Noetherian local domain still lowers Krull dimension by exactly one.  This is
the local algebra statement required by the canonical separator's radial
one-sheet move.
-/

set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000

noncomputable section

open Ideal RingTheory IsLocalRing
open GSTClassicalHodgeLocalRegularCutDimension

namespace GSTClassicalHodgeRadicalPrincipalCutDimension

/-- Quotienting by an ideal or by its radical has the same Krull dimension.
Both quotient prime spectra are order-isomorphic to the same Zariski zero
locus. -/
theorem ringKrullDim_quotient_radical
    {R : Type*} [CommRing R]
    (I : Ideal R) :
    ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  rw [PrimeSpectrum.zeroLocus_radical]

/-- **REDUCED ONE-EQUATION DIMENSION DROP.**
In a Noetherian local domain, reducing the principal zero locus does not alter
the exact one-step Krull-dimension decrement. -/
theorem ringKrullDim_quotient_radical_span_singleton_succ
    {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R]
    {f : R} (hf0 : f ≠ 0) (hfunit : ¬ IsUnit f) :
    ringKrullDim (R ⧸ (Ideal.span {f}).radical) + 1 = ringKrullDim R := by
  rw [ringKrullDim_quotient_radical]
  exact ringKrullDim_quotient_nonzero_nonunit_succ hf0 hfunit

/-- Rewriting form for a geometric cut kernel already identified with the
radical of one principal equation. -/
theorem ringKrullDim_quotient_eq_of_eq_radical_span_singleton
    {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R]
    (J : Ideal R) {f : R}
    (hJ : J = (Ideal.span {f}).radical)
    (hf0 : f ≠ 0) (hfunit : ¬ IsUnit f) :
    ringKrullDim (R ⧸ J) + 1 = ringKrullDim R := by
  rw [hJ]
  exact ringKrullDim_quotient_radical_span_singleton_succ hf0 hfunit

#check ringKrullDim_quotient_radical
#check ringKrullDim_quotient_radical_span_singleton_succ
#check ringKrullDim_quotient_eq_of_eq_radical_span_singleton

#print axioms ringKrullDim_quotient_radical
#print axioms ringKrullDim_quotient_radical_span_singleton_succ
#print axioms ringKrullDim_quotient_eq_of_eq_radical_span_singleton

end GSTClassicalHodgeRadicalPrincipalCutDimension
