import GSTClassicalHodgeFiniteSupportChart
import GSTHodgePoincareStrands
import GSTSquarePureHodgeDuality
import GSTWorldCosmology

/-!
# GST CLASSICAL HODGE — PURE SQUARE STRAND LOCALIZATION

A finite-support classical Hodge state can be represented more strongly than
by an arbitrary finite world: place its N live multiplicity coordinates on
the diagonal of an N x N GST square.

This makes the local state a pure Hodge state, equivalently a charge-zero
state.  Poincare duality preserves charge zero in a balanced square.  An
arbitrary completed probe may therefore be projected to its zero-charge part
without changing its pairing with the localized Hodge state.

Consequently every separator witness localizes to a nonzero pure-vs-pure
Poincare pairing inside one finite square GST world.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTProjectiveOverC
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeSeparatorProbe
open GSTClassicalHodgeFiniteSupportChart
open GSTHodgePoincareStrands
open GSTWorldPoincareDuality
open GSTWorldCosmology
open GSTGeometricRealizationStage2G

namespace GSTClassicalHodgeSquareStrandLocalization

/-- Rational coefficient field on one finite square GST world. -/
abbrev RationalWorldCoef (N : Nat) := WorldCell N N → ℚ

/-- Rational pure-Hodge support condition. -/
def IsRationalPureHodge
    {N : Nat} (f : RationalWorldCoef N) : Prop :=
  ∀ c : WorldCell N N, c.1.1 ≠ c.2.1 → f c = 0

/-- Rational charge-strand projector, parallel to the integral GST projector. -/
def rationalHodgeStrandProj
    {N : Nat} (q : Int) (f : RationalWorldCoef N) :
    RationalWorldCoef N :=
  fun c => if worldHodgeCharge c = q then f c else 0

/-- Put every live coordinate of one compact Hodge address on the diagonal of
its N x N multiplicity square. -/
def supportDiagonalWorld
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    RationalWorldCoef (fiberedSupportSize f) :=
  fun c =>
    if h : c.1 = c.2 then
      f (((fiberedSupportEquivFin f).symm c.1).1)
    else 0

@[simp]
theorem supportDiagonalWorld_at_diagonal
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (i : Fin (fiberedSupportSize f)) :
    supportDiagonalWorld f (i,i) =
      f (((fiberedSupportEquivFin f).symm i).1) := by
  simp [supportDiagonalWorld]

/-- The support-square state is pure. -/
theorem supportDiagonalWorld_isPure
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    IsRationalPureHodge (supportDiagonalWorld f) := by
  intro c hc
  have hne : c.1 ≠ c.2 := by
    intro h
    exact hc (congrArg Fin.val h)
  simp [supportDiagonalWorld, hne]

/-- Rational purity is exactly fixedness under the zero-charge projector. -/
theorem rationalPure_iff_zeroCharge_fixed
    {N : Nat} (f : RationalWorldCoef N) :
    IsRationalPureHodge f ↔ rationalHodgeStrandProj 0 f = f := by
  constructor
  · intro hf
    funext c
    by_cases hdiag : c.1.1 = c.2.1
    · have hq : worldHodgeCharge c = 0 := by
        unfold worldHodgeCharge
        omega
      simp [rationalHodgeStrandProj, hq]
    · have hq : worldHodgeCharge c ≠ 0 := by
        intro h
        unfold worldHodgeCharge at h
        omega
      simp [rationalHodgeStrandProj, hq, hf c hdiag]
  · intro hfix c hdiag
    have hq : worldHodgeCharge c ≠ 0 := by
      intro h
      unfold worldHodgeCharge at h
      omega
    have hc := congrFun hfix c
    simp [rationalHodgeStrandProj, hq] at hc
    exact hc.symm

/-- The localized state is fixed by the pure charge-zero projector. -/
theorem supportDiagonalWorld_zeroCharge
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    rationalHodgeStrandProj 0 (supportDiagonalWorld f) =
      supportDiagonalWorld f :=
  (rationalPure_iff_zeroCharge_fixed _).mp
    (supportDiagonalWorld_isPure f)

/-- The diagonal localization retains the full compact address. -/
theorem supportDiagonalWorld_eq_zero_iff
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    supportDiagonalWorld f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    apply Finsupp.ext
    intro s
    by_cases hs : s ∈ f.support
    · let slive : LiveFiberedAddress f := ⟨s,hs⟩
      let i := fiberedSupportEquivFin f slive
      have hi := congrFun hz (i,i)
      simpa [i,slive] using hi
    · exact Finsupp.notMem_support_iff.mp hs
  · rintro rfl
    funext c
    simp [supportDiagonalWorld]

/-- Pull a completed Hodge probe into the square with the Poincare involution
inserted, so pairing after dualization reads the original live coordinate. -/
def dualizedSquareProbe
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (g : FiberedCompletedAddress V H) :
    RationalWorldCoef (fiberedSupportSize f) :=
  fun c =>
    g (((fiberedSupportEquivFin f).symm (worldDual c).1).1)

/-- The square localization computes the same compact/completed pairing as the
original limitless fibered universe. -/
theorem fiberedPairing_eq_squarePoincare
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (g : FiberedCompletedAddress V H) :
    fiberedPairing f g =
      rationalWorldTopPairing
        (supportDiagonalWorld f)
        (dualizedSquareProbe f g) := by
  classical
  have hoff :
      ∀ c : WorldCell (fiberedSupportSize f) (fiberedSupportSize f),
        c.1 ≠ c.2 →
        supportDiagonalWorld f c *
          g (((fiberedSupportEquivFin f).symm
            (worldDual (worldDual c)).1).1) = 0 := by
    intro c hc
    simp [supportDiagonalWorld, hc]
  calc fiberedPairing f g
      = ∑ s : LiveFiberedAddress f, f s.1 * g s.1 :=
        (supportSubtype_sum_eq_fiberedPairing f g).symm
    _ = ∑ i : Fin (fiberedSupportSize f),
          supportDiagonalWorld f (i,i) *
            g (((fiberedSupportEquivFin f).symm
              (worldDual (worldDual (i,i))).1).1) := by
        exact Fintype.sum_equiv (fiberedSupportEquivFin f)
          (fun s => f s.1 * g s.1)
          (fun i => supportDiagonalWorld f (i,i) *
            g (((fiberedSupportEquivFin f).symm
              (worldDual (worldDual (i,i))).1).1))
          (by intro s; simp)
    _ = ∑ c : WorldCell (fiberedSupportSize f) (fiberedSupportSize f),
          supportDiagonalWorld f c *
            g (((fiberedSupportEquivFin f).symm
              (worldDual (worldDual c)).1).1) := by
        have hinj : Function.Injective
            (fun i : Fin (fiberedSupportSize f) => (i, i)) :=
          fun i j h => congrArg Prod.fst h
        rw [← Finset.sum_image
          (s := (Finset.univ : Finset (Fin (fiberedSupportSize f))))
          (f := fun c => supportDiagonalWorld f c *
            g (((fiberedSupportEquivFin f).symm
              (worldDual (worldDual c)).1).1))
          (g := fun i : Fin (fiberedSupportSize f) => (i, i))
          hinj.injOn]
        exact Finset.sum_subset (Finset.subset_univ _)
          (by
            intro c _ hni
            refine hoff c ?_
            intro hcc
            exact hni (Finset.mem_image.mpr
              ⟨c.1, Finset.mem_univ _,
                congrArg (fun x : Fin (fiberedSupportSize f) => (c.1, x)) hcc⟩))
    _ = rationalWorldTopPairing
          (supportDiagonalWorld f) (dualizedSquareProbe f g) := by
        rfl
/-- A pure square state pairs only with the zero-charge part of any probe. -/
theorem rationalWorldTopPairing_eq_zeroChargeProbe
    {N : Nat}
    (a b : RationalWorldCoef N)
    (ha : IsRationalPureHodge a) :
    rationalWorldTopPairing a (rationalHodgeStrandProj 0 b) =
      rationalWorldTopPairing a b := by
  classical
  unfold rationalWorldTopPairing
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hdiag : c.1.1 = c.2.1
  · have hdual0 : worldHodgeCharge (worldDual c) = 0 := by
      rw [worldHodgeCharge_dual]
      unfold worldChargeCenter worldHodgeCharge
      omega
    simp [rationalHodgeStrandProj, hdual0]
  · have hazero := ha c hdiag
    simp [hazero]

/-- Zero-charge projection of a rational probe is itself pure in a square. -/
theorem zeroChargeProbe_isPure
    {N : Nat} (b : RationalWorldCoef N) :
    IsRationalPureHodge (rationalHodgeStrandProj 0 b) := by
  rw [rationalPure_iff_zeroCharge_fixed]
  funext c
  by_cases hq : worldHodgeCharge c = 0 <;>
    simp [rationalHodgeStrandProj, hq]

/-- **PURE-SQUARE LOCALIZATION OF A PAIRING.**  Every limitless fibered
pairing equals a finite square Poincare pairing between two rational pure
Hodge states. -/
theorem fiberedPairing_eq_pureSquarePoincare
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (g : FiberedCompletedAddress V H) :
    fiberedPairing f g =
      rationalWorldTopPairing
        (supportDiagonalWorld f)
        (rationalHodgeStrandProj 0 (dualizedSquareProbe f g)) := by
  rw [fiberedPairing_eq_squarePoincare f g]
  symm
  exact rationalWorldTopPairing_eq_zeroChargeProbe
    (supportDiagonalWorld f)
    (dualizedSquareProbe f g)
    (supportDiagonalWorld_isPure f)

/-- Separator witnesses may therefore always be chosen inside one finite
pure-vs-pure square sector. -/
theorem atomicSeparatorProbe_has_pureSquare_witness
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (S : AtomicSeparatorProbe V H p) :
    ∃ a b : RationalWorldCoef
        (fiberedSupportSize (fiberedWeightCoordinates V H p S.alpha)),
      IsRationalPureHodge a ∧
      IsRationalPureHodge b ∧
      rationalWorldTopPairing a b ≠ 0 := by
  let f := fiberedWeightCoordinates V H p S.alpha
  let g : FiberedCompletedAddress V H :=
    fun s =>
      if hp : s.1 = p then
        match hp ▸ s.2 with
        | i => functionalHodgeProbe V H p S.detector i
      else 0
  let a := supportDiagonalWorld f
  let b := rationalHodgeStrandProj 0 (dualizedSquareProbe f g)
  refine ⟨a,b,supportDiagonalWorld_isPure f,
    zeroChargeProbe_isPure _, ?_⟩
  have hpair : fiberedPairing f g ≠ 0 := by
    have hcoords :
        fiberedPairing f g =
          hodgeFiberPairing
            ((classicalHodgeBasis V H p).repr S.alpha)
            (functionalHodgeProbe V H p S.detector) := by
      classical
      unfold f g fiberedPairing hodgeFiberPairing fiberedWeightCoordinates
      simp [weightFiberEmbedding, Finsupp.sum_embDomain]
      rfl
    rw [hcoords]
    exact S.pairing_nonzero
  rw [fiberedPairing_eq_pureSquarePoincare f g] at hpair
  exact hpair

/-- **PURE-SQUARE REDUCTION OF HODGE FAILURE.**  Any failure witness for the
classical Stage-2G target would survive as a nonzero Poincare pairing entirely
inside the charge-zero pure sector of one finite balanced GST square. -/
theorem not_hodge_yields_nonzero_pureSquare_pairing
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hnot : ¬ BigradedBettiHodgeStatement V H) :
    ∃ p : Nat, ∃ S : AtomicSeparatorProbe V H p,
    ∃ a b : RationalWorldCoef
        (fiberedSupportSize (fiberedWeightCoordinates V H p S.alpha)),
      IsRationalPureHodge a ∧
      IsRationalPureHodge b ∧
      rationalWorldTopPairing a b ≠ 0 := by
  obtain ⟨p,hS⟩ :=
    (not_bigradedBettiHodgeStatement_iff_exists_separatorProbe V H).mp hnot
  let S := Classical.choice hS
  obtain ⟨a,b,ha,hb,hpair⟩ :=
    atomicSeparatorProbe_has_pureSquare_witness V H p S
  exact ⟨p,S,a,b,ha,hb,hpair⟩

#check RationalWorldCoef
#check IsRationalPureHodge
#check rationalHodgeStrandProj
#check supportDiagonalWorld
#check supportDiagonalWorld_isPure
#check rationalPure_iff_zeroCharge_fixed
#check supportDiagonalWorld_zeroCharge
#check supportDiagonalWorld_eq_zero_iff
#check dualizedSquareProbe
#check fiberedPairing_eq_squarePoincare
#check rationalWorldTopPairing_eq_zeroChargeProbe
#check zeroChargeProbe_isPure
#check fiberedPairing_eq_pureSquarePoincare
#check atomicSeparatorProbe_has_pureSquare_witness
#check not_hodge_yields_nonzero_pureSquare_pairing

#print axioms supportDiagonalWorld_isPure
#print axioms supportDiagonalWorld_eq_zero_iff
#print axioms fiberedPairing_eq_pureSquarePoincare
#print axioms atomicSeparatorProbe_has_pureSquare_witness
#print axioms not_hodge_yields_nonzero_pureSquare_pairing

end GSTClassicalHodgeSquareStrandLocalization
