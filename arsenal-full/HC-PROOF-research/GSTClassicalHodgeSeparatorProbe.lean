import GSTClassicalHodgeAtomicAnnihilator

/-!
# GST CLASSICAL HODGE — SEPARATORS AS FIBER PROBES

A rational linear detector on ambient cohomology restricts to a functional on
each genuine rational `(p,p)` Hodge fiber.  Relative to the unrestricted
chosen basis of that fiber, this restricted functional is exactly evaluation
against a completed coordinate probe.

Thus the annihilator formulation of the classical Hodge target can be read in
the same compact/completed language as limitless GST Poincare duality:
finite-support Hodge coordinates pair against arbitrary completed probes.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicAnnihilator

namespace GSTClassicalHodgeSeparatorProbe

/-- Completed probe on one fixed classical rational Hodge multiplicity fiber. -/
abbrev HodgeFiberProbe
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  ClassicalHodgeBasisIndex V H p → ℚ

/-- Compact/completed pairing on one fixed Hodge fiber. -/
def hodgeFiberPairing
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    {p : Nat}
    (a : ClassicalHodgeBasisIndex V H p →₀ ℚ)
    (g : HodgeFiberProbe V H p) : ℚ :=
  a.sum (fun i q => q * g i)

/-- Coordinate probe obtained by restricting an ambient cohomology functional
to the genuine Hodge basis vectors. -/
def functionalHodgeProbe
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ) :
    HodgeFiberProbe V H p :=
  fun i => ell (classicalHodgeBasis V H p i).1

/-- Restriction of an ambient cohomology detector to the Hodge fiber. -/
def restrictedHodgeFunctional
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
  ell.comp (rationalHodgeSubspace (H.hodgeBigrading p)).subtype

/-- The completed probe acts linearly on finite-support basis coordinates. -/
noncomputable def hodgeFiberProbeLinearMap
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (g : HodgeFiberProbe V H p) :
    (ClassicalHodgeBasisIndex V H p →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ g

/-- **FUNCTIONAL/PROBE IDENTIFICATION.**  Every ambient rational detector,
when restricted to the Hodge fiber, is exactly the pairing of the class's
finite-support basis coordinates with the detector's completed basis probe. -/
theorem restrictedHodgeFunctional_eq_probe_pairing
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (alpha : ClassicalHodgeFiber V H p) :
    restrictedHodgeFunctional V H p ell alpha =
      hodgeFiberPairing
        ((classicalHodgeBasis V H p).repr alpha)
        (functionalHodgeProbe V H p ell) := by
  let b := classicalHodgeBasis V H p
  have hmaps :
      restrictedHodgeFunctional V H p ell =
        (hodgeFiberProbeLinearMap V H p
          (functionalHodgeProbe V H p ell)).comp b.repr.toLinearMap := by
    apply b.ext
    intro i
    simp [restrictedHodgeFunctional, hodgeFiberProbeLinearMap,
      functionalHodgeProbe, b, hodgeFiberPairing]
  change restrictedHodgeFunctional V H p ell alpha = _
  rw [hmaps]
  rfl

/-- A detector sees a nonzero Hodge class exactly as a nonzero completed-probe
pairing against its compact basis coordinates. -/
theorem functional_detects_hodge_iff_probe_pairing_ne_zero
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (ell : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ)
    (alpha : ClassicalHodgeFiber V H p) :
    ell alpha.1 ≠ 0 ↔
      hodgeFiberPairing
        ((classicalHodgeBasis V H p).repr alpha)
        (functionalHodgeProbe V H p ell) ≠ 0 := by
  have h := restrictedHodgeFunctional_eq_probe_pairing V H p ell alpha
  show restrictedHodgeFunctional V H p ell alpha ≠ 0 ↔ _ ≠ 0
  rw [h]

/-- A concrete separator package in pure compact/completed coordinate form. -/
structure AtomicSeparatorProbe
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) where
  alpha : ClassicalHodgeFiber V H p
  detector :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ
  annihilates_atoms :
    AnnihilatesPointCycleClasses p (H.cycleClass p) detector
  pairing_nonzero :
    hodgeFiberPairing
      ((classicalHodgeBasis V H p).repr alpha)
      (functionalHodgeProbe V H p detector) ≠ 0

/-- A nonzero annihilator witness is equivalent to an explicit nonzero
compact/completed Hodge-fiber probe witness. -/
theorem exists_atomic_separator_iff_exists_separatorProbe
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    (∃ alpha : RationalSingularCohomology H.analytification (2 * p),
        alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) ∧
        ∃ ell :
          RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ] ℚ,
          AnnihilatesPointCycleClasses p (H.cycleClass p) ell ∧
          ell alpha ≠ 0) ↔
      Nonempty (AtomicSeparatorProbe V H p) := by
  constructor
  · rintro ⟨alpha, halpha, ell, hatoms, hdetect⟩
    let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
    refine ⟨{
      alpha := alphaH
      detector := ell
      annihilates_atoms := hatoms
      pairing_nonzero := ?_ }⟩
    exact (functional_detects_hodge_iff_probe_pairing_ne_zero
      V H p ell alphaH).mp hdetect
  · rintro ⟨S⟩
    refine ⟨S.alpha.1, S.alpha.2, S.detector,
      S.annihilates_atoms, ?_⟩
    exact (functional_detects_hodge_iff_probe_pairing_ne_zero
      V H p S.detector S.alpha).mpr S.pairing_nonzero

/-- **SEPARATOR-PROBE FORM OF HODGE FAILURE.**  Failure of the Stage-2G target
is equivalent to the existence of one weight carrying a completed probe that
annihilates every genuine algebraic atom yet pairs nontrivially with a compact
Hodge coordinate state. -/
theorem not_bigradedBettiHodgeStatement_iff_exists_separatorProbe
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    ¬ BigradedBettiHodgeStatement V H ↔
      ∃ p : Nat, Nonempty (AtomicSeparatorProbe V H p) := by
  rw [not_bigradedBettiHodgeStatement_iff_exists_atomic_separator V H]
  constructor
  · rintro ⟨p, alpha, halpha, ell, hatoms, hdetect⟩
    refine ⟨p, ?_⟩
    exact (exists_atomic_separator_iff_exists_separatorProbe V H p).mp
      ⟨alpha, halpha, ell, hatoms, hdetect⟩
  · rintro ⟨p, hprobe⟩
    rcases (exists_atomic_separator_iff_exists_separatorProbe V H p).mpr hprobe
      with ⟨alpha, halpha, ell, hatoms, hdetect⟩
    exact ⟨p, alpha, halpha, ell, hatoms, hdetect⟩

/-- Positive target form: proving that no atomic separator probe exists at any
weight is exactly sufficient and necessary for the full Stage-2G Hodge
statement. -/
theorem bigradedBettiHodgeStatement_iff_no_separatorProbe
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∀ p : Nat, IsEmpty (AtomicSeparatorProbe V H p) := by
  rw [← not_iff_not]
  push_neg
  exact not_bigradedBettiHodgeStatement_iff_exists_separatorProbe V H

#check HodgeFiberProbe
#check hodgeFiberPairing
#check functionalHodgeProbe
#check restrictedHodgeFunctional
#check hodgeFiberProbeLinearMap
#check restrictedHodgeFunctional_eq_probe_pairing
#check functional_detects_hodge_iff_probe_pairing_ne_zero
#check AtomicSeparatorProbe
#check exists_atomic_separator_iff_exists_separatorProbe
#check not_bigradedBettiHodgeStatement_iff_exists_separatorProbe
#check bigradedBettiHodgeStatement_iff_no_separatorProbe

#print axioms restrictedHodgeFunctional_eq_probe_pairing
#print axioms exists_atomic_separator_iff_exists_separatorProbe
#print axioms not_bigradedBettiHodgeStatement_iff_exists_separatorProbe
#print axioms bigradedBettiHodgeStatement_iff_no_separatorProbe

end GSTClassicalHodgeSeparatorProbe
