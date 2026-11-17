import GSTClassicalHodgeAtomicSpan
import GSTWorldPoincareDuality

/-!
# GST CLASSICAL HODGE — ATOMIC DEFECT AND FIBERED DUALITY

This module turns the basis-free atomic-span formulation into a vanishing
problem and extends the limitless compact/completed Poincare logic to the
full classical Hodge multiplicity universe.

For each weight p, quotient rational cohomology by the span of genuine
codimension-p point-cycle classes.  The induced map from the rational
`(p,p)` Hodge fiber is the atomic defect map.  The classical Hodge statement
is exactly the assertion that every one of these defect maps is zero.

Independently, the fibered Hodge address universe carries a perfect pairing
between finite-support rational addresses and arbitrary rational probes.
Thus no multiplicity direction can disappear inside the limitless GST base.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicSpan

namespace GSTClassicalHodgeAtomicDefectDuality

/-- Completed rational probe universe dual to finite-support fibered Hodge
addresses. -/
abbrev FiberedCompletedAddress
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :=
  FiberedHodgeIndex V H → ℚ

/-- Rational compact/completed pairing on the full classical fibered Hodge
universe. -/
def fiberedPairing
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (g : FiberedCompletedAddress V H) : ℚ :=
  f.sum (fun s q => q * g s)

/-- Coordinate delta probe at one total fibered Hodge address. -/
def fiberedProbe
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (s : FiberedHodgeIndex V H) :
    FiberedCompletedAddress V H :=
  fun t => if t = s then 1 else 0

@[simp]
theorem fiberedPairing_probe
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (f : FiberedHodgeAddress V H)
    (s : FiberedHodgeIndex V H) :
    fiberedPairing f (fiberedProbe s) = f s := by
  classical
  by_cases hs : f s = 0
  · simp [fiberedPairing, Finsupp.sum, fiberedProbe, hs]
  · simp [fiberedPairing, Finsupp.sum, fiberedProbe,
      Finsupp.mem_support_iff, hs]

/-- Pairing against a Kronecker-single address reads off one probe value. -/
theorem fiberedPairing_single_left
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (s : FiberedHodgeIndex V H)
    (g : FiberedCompletedAddress V H) :
    fiberedPairing (Finsupp.single s 1) g = g s := by
  have h1 : fiberedPairing (Finsupp.single s 1) g = 1 * g s :=
    Finsupp.sum_single_index (a := s) (b := 1)
      (h := fun t (q : ℚ) => q * g t) (by simp)
  simpa using h1

/-- **FIBERED LEFT NONDEGENERACY.**  A compact fibered Hodge address that
pairs to zero against every completed probe is the zero address. -/
theorem fiberedPairing_nondegenerate_left
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (f : FiberedHodgeAddress V H)
    (h : ∀ g : FiberedCompletedAddress V H,
      fiberedPairing f g = 0) :
    f = 0 := by
  apply Finsupp.ext
  intro s
  simpa using h (fiberedProbe s)

/-- **FIBERED RIGHT NONDEGENERACY.**  A completed probe invisible to every
compact fibered Hodge address is the zero probe. -/
theorem fiberedPairing_nondegenerate_right
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (g : FiberedCompletedAddress V H)
    (h : ∀ f : FiberedHodgeAddress V H,
      fiberedPairing f g = 0) :
    g = 0 := by
  funext s
  have h2 := h (Finsupp.single s 1)
  rw [fiberedPairing_single_left s g] at h2
  simpa using h2

/-- Every genuine class in a fixed rational `(p,p)` Hodge fiber is perfectly
detected after embedding its basis coordinates into the total limitless
fibered universe. -/
theorem fiberedWeightCoordinates_pairing_nondegenerate
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (h : ∀ g : FiberedCompletedAddress V H,
      fiberedPairing (fiberedWeightCoordinates V H p alpha) g = 0) :
    alpha = 0 := by
  have haddr : fiberedWeightCoordinates V H p alpha = 0 :=
    fiberedPairing_nondegenerate_left V H
      (fiberedWeightCoordinates V H p alpha) h
  apply fiberedWeightCoordinates_injective V H p
  simpa [fiberedWeightCoordinates] using haddr

/-- Equality of genuine Hodge classes can be tested against all completed
fibered probes. -/
theorem fiberedWeightCoordinates_ext_by_pairing
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha beta : ClassicalHodgeFiber V H p)
    (h : ∀ g : FiberedCompletedAddress V H,
      fiberedPairing (fiberedWeightCoordinates V H p alpha) g =
        fiberedPairing (fiberedWeightCoordinates V H p beta) g) :
    alpha = beta := by
  apply fiberedWeightCoordinates_injective V H p
  apply Finsupp.ext
  intro s
  have hs := h (fiberedProbe s)
  simpa using hs

/-- The basis-free atomic defect space in codimension p. -/
abbrev AtomicDefectSpace
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :=
  RationalSingularCohomology H.analytification (2 * p) ⧸
    pointCycleClassSpan p (H.cycleClass p)

/-- The atomic defect map: include the rational `(p,p)` Hodge fiber into
cohomology and then quotient by the span of genuine point-cycle classes. -/
noncomputable def atomicDefectLinearMap
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] AtomicDefectSpace V H p :=
  (Submodule.mkQ (pointCycleClassSpan p (H.cycleClass p))).comp
    (rationalHodgeSubspace (H.hodgeBigrading p)).subtype

@[simp]
theorem atomicDefectLinearMap_apply
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p) :
    atomicDefectLinearMap V H p alpha =
      Submodule.Quotient.mk alpha.1 :=
  rfl

/-- Vanishing of the atomic defect map is exactly inclusion of the Hodge
fiber in the atomic point-cycle span. -/
theorem atomicDefectLinearMap_eq_zero_iff
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    atomicDefectLinearMap V H p = 0 ↔
      rationalHodgeSubspace (H.hodgeBigrading p) ≤
        pointCycleClassSpan p (H.cycleClass p) := by
  constructor
  · intro h alpha halpha
    let alphaH : ClassicalHodgeFiber V H p := ⟨alpha, halpha⟩
    have hz : atomicDefectLinearMap V H p alphaH = 0 := by
      rw [h]
      rfl
    exact (Submodule.Quotient.mk_eq_zero
      (pointCycleClassSpan p (H.cycleClass p))).mp hz
  · intro h
    apply LinearMap.ext
    intro alpha
    apply (Submodule.Quotient.mk_eq_zero
      (pointCycleClassSpan p (H.cycleClass p))).mpr
    exact h alpha.2

/-- **ATOMIC DEFECT VANISHING FORM OF HODGE.**  The genuine Stage-2G Hodge
statement is exactly the simultaneous vanishing of all atomic defect maps. -/
theorem bigradedBettiHodgeStatement_iff_atomicDefect_zero
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∀ p : Nat, atomicDefectLinearMap V H p = 0 := by
  rw [bigradedBettiHodgeStatement_iff_atomic_span V H]
  constructor
  · intro h p
    exact (atomicDefectLinearMap_eq_zero_iff V H p).2 (h p)
  · intro h p
    exact (atomicDefectLinearMap_eq_zero_iff V H p).1 (h p)

/-- A linear map out of one Hodge fiber vanishes exactly when it vanishes on
the chosen unrestricted basis of that fiber. -/
theorem atomicDefect_zero_iff_basis_zero
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat) :
    atomicDefectLinearMap V H p = 0 ↔
      ∀ i : ClassicalHodgeBasisIndex V H p,
        atomicDefectLinearMap V H p
          (classicalHodgeBasis V H p i) = 0 := by
  constructor
  · intro h i
    rw [h]
    rfl
  · intro h
    apply (classicalHodgeBasis V H p).ext
    intro i
    simpa using h i

/-- The full classical target can therefore be tested atom-by-atom in the
limitless multiplicity basis, while the fibered Poincare pairing guarantees
that no nonzero basis direction is invisible to the coordinate universe. -/
theorem bigradedBettiHodgeStatement_iff_basis_atomicDefect_zero
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    BigradedBettiHodgeStatement V H ↔
      ∀ p : Nat, ∀ i : ClassicalHodgeBasisIndex V H p,
        atomicDefectLinearMap V H p
          (classicalHodgeBasis V H p i) = 0 := by
  rw [bigradedBettiHodgeStatement_iff_atomicDefect_zero V H]
  constructor
  · intro h p
    exact (atomicDefect_zero_iff_basis_zero V H p).1 (h p)
  · intro h p
    exact (atomicDefect_zero_iff_basis_zero V H p).2 (h p)

/-- Duality crown for the unrestricted classical multiplicity universe. -/
theorem fibered_duality_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    (∀ f : FiberedHodgeAddress V H,
      (∀ g : FiberedCompletedAddress V H, fiberedPairing f g = 0) →
        f = 0)
    ∧ (∀ g : FiberedCompletedAddress V H,
      (∀ f : FiberedHodgeAddress V H, fiberedPairing f g = 0) →
        g = 0)
    ∧ (∀ p : Nat, ∀ alpha beta : ClassicalHodgeFiber V H p,
      (∀ g : FiberedCompletedAddress V H,
        fiberedPairing (fiberedWeightCoordinates V H p alpha) g =
          fiberedPairing (fiberedWeightCoordinates V H p beta) g) →
        alpha = beta) := by
  exact ⟨
    fiberedPairing_nondegenerate_left V H,
    fiberedPairing_nondegenerate_right V H,
    fiberedWeightCoordinates_ext_by_pairing V H⟩

#check FiberedCompletedAddress
#check fiberedPairing
#check fiberedProbe
#check fiberedPairing_probe
#check fiberedPairing_nondegenerate_left
#check fiberedPairing_nondegenerate_right
#check fiberedWeightCoordinates_pairing_nondegenerate
#check fiberedWeightCoordinates_ext_by_pairing
#check AtomicDefectSpace
#check atomicDefectLinearMap
#check atomicDefectLinearMap_eq_zero_iff
#check bigradedBettiHodgeStatement_iff_atomicDefect_zero
#check atomicDefect_zero_iff_basis_zero
#check bigradedBettiHodgeStatement_iff_basis_atomicDefect_zero
#check fibered_duality_crown

#print axioms fiberedPairing_nondegenerate_left
#print axioms fiberedPairing_nondegenerate_right
#print axioms fiberedWeightCoordinates_ext_by_pairing
#print axioms atomicDefectLinearMap_eq_zero_iff
#print axioms bigradedBettiHodgeStatement_iff_atomicDefect_zero
#print axioms bigradedBettiHodgeStatement_iff_basis_atomicDefect_zero
#print axioms fibered_duality_crown

end GSTClassicalHodgeAtomicDefectDuality
