import GSTClassicalHodgeFiniteSupportChart
import GSTPureHodgeLefschetzKernel
import GSTLefschetzPoincareReciprocity
import GSTGlobalPureHodgeCosmology

/-!
# GST CLASSICAL HODGE — FINITE LEFSCHETZ TOMOGRAPHY

Every concrete Hodge class has finite multiplicity support.  After coding that
support by `Fin N`, place the N live multiplicity directions on the diagonal
of the square N x N GST world.

The existing pure-Hodge Lefschetz kernel is triangular on this diagonal:
from source i to target j it is zero for j < i and, for i <= j, has exact
coefficient

  choose (2*(j-i)) (j-i).

The diagonal coefficient is choose 0 0 = 1.  Hence the full finite transform
is unit triangular and injective.  This gives an exact tomography theorem:
all finite multiplicity coordinates of a Hodge state are recoverable from its
Lefschetz moments.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTProjectiveOverC
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiniteSupportChart
open GSTPureHodgeLefschetzKernel
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTTruncatedWorldCohomologyRing
open GSTGlobalPureHodgeCosmology
open GSTGeometricRealizationStage2G

namespace GSTClassicalHodgeLefschetzTomography

/-- Rationalized exact diagonal Lefschetz kernel on a finite multiplicity
chart. -/
def multiplicityLefschetzKernel
    {N : Nat} (i j : Fin N) : ℚ :=
  if h : i.1 ≤ j.1 then
    (Nat.choose (2 * (j.1 - i.1)) (j.1 - i.1) : ℚ)
  else 0

@[simp]
theorem multiplicityLefschetzKernel_self
    {N : Nat} (i : Fin N) :
    multiplicityLefschetzKernel i i = 1 := by
  simp [multiplicityLefschetzKernel]

@[simp]
theorem multiplicityLefschetzKernel_zero_of_lt
    {N : Nat} (i j : Fin N) (hji : j.1 < i.1) :
    multiplicityLefschetzKernel i j = 0 := by
  simp [multiplicityLefschetzKernel, show ¬ i.1 ≤ j.1 by omega]

/-- The rational kernel is exactly the rationalization of the existing GST
pure-diagonal transition coefficient at its unique live time. -/
theorem multiplicityLefschetzKernel_eq_worldAct
    {N : Nat} (i j : Fin N) (hij : i.1 ≤ j.1) :
    multiplicityLefschetzKernel i j =
      (worldAct N N
        ((L N N)^(2 * pureWeightGap
          (Fin.castLE (show N ≤ min N N by omega) i)
          (Fin.castLE (show N ≤ min N N by omega) j)))
        (GSTWorldPoincareDuality.worldBasis
          (pureDiagonalState (Fin.castLE (show N ≤ min N N by omega) i)))
        (pureDiagonalState (Fin.castLE (show N ≤ min N N by omega) j)) : ℚ) := by
  rw [pure_diagonal_lefschetz_forward_exact
    (Fin.castLE (show N ≤ min N N by omega) i)
    (Fin.castLE (show N ≤ min N N by omega) j)
    (by simpa [Fin.val_castLE] using hij)]
  simp [multiplicityLefschetzKernel, hij, pureWeightGap, Fin.val_castLE]
  try push_cast

/-- Exact finite Lefschetz tomography transform.  The q-th moment receives
contributions only from source coordinates i <= q. -/
def lefschetzTomography
    {N : Nat} (a : Fin N → ℚ) : Fin N → ℚ :=
  fun q => ∑ i : Fin N, multiplicityLefschetzKernel i q * a i

/-- The q-th tomography coordinate is its original q-coordinate plus terms
strictly below q. -/
theorem lefschetzTomography_triangular
    {N : Nat} (a : Fin N → ℚ) (q : Fin N) :
    lefschetzTomography a q =
      a q +
        ∑ i : Fin N with i.1 < q.1,
            multiplicityLefschetzKernel i q * a i := by
  classical
  have hsplit :
      ∑ i : Fin N, multiplicityLefschetzKernel i q * a i
        = multiplicityLefschetzKernel q q * a q
          + ∑ i ∈ (Finset.univ : Finset (Fin N)).erase q,
              multiplicityLefschetzKernel i q * a i :=
    (Finset.add_sum_erase Finset.univ
      (fun i => multiplicityLefschetzKernel i q * a i)
      (Finset.mem_univ q)).symm
  unfold lefschetzTomography
  rw [hsplit, multiplicityLefschetzKernel_self, one_mul]
  apply congrArg (fun z : ℚ => a q + z)
  refine (Finset.sum_subset ?_ ?_).symm
  · intro i hi
    have hi2 : i.1 < q.1 := (Finset.mem_filter.mp hi).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
    intro hval
    subst hval
    omega
  · intro i hiE hiF
    have hiF2 : ¬ i.1 < q.1 := fun hlt => hiF (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
    rcases Finset.mem_erase.mp hiE with ⟨hine, _⟩
    have hne : i.1 ≠ q.1 := by
      intro hval
      exact hine (Fin.ext hval)
    have hgt : q.1 < i.1 := by omega
    rw [multiplicityLefschetzKernel_zero_of_lt i q hgt]
    simp

/-- **UNIT-TRIANGULAR INJECTIVITY.**  Exact Lefschetz tomography loses no
finite multiplicity information. -/
theorem lefschetzTomography_injective
    {N : Nat} : Function.Injective (@lefschetzTomography N) := by
  intro a b hab
  have key : ∀ k : Nat, ∀ i : Fin N, i.1 ≤ k → a i = b i := by
    intro k
    induction k with
    | zero =>
        intro i hi
        have hq := congrFun hab i
        rw [lefschetzTomography_triangular a i,
            lefschetzTomography_triangular b i] at hq
        have hza : ∑ j : Fin N with j.1 < i.1,
            multiplicityLefschetzKernel j i * a j = 0 := by
          refine Finset.sum_eq_zero ?_
          intro j hj
          simp only [Finset.mem_filter] at hj
          exact absurd hj.2 (by omega)
        have hzb : ∑ j : Fin N with j.1 < i.1,
            multiplicityLefschetzKernel j i * b j = 0 := by
          refine Finset.sum_eq_zero ?_
          intro j hj
          simp only [Finset.mem_filter] at hj
          exact absurd hj.2 (by omega)
        rw [hza, hzb] at hq
        simpa using hq
    | succ k ih =>
        intro i hi
        have hq := congrFun hab i
        rw [lefschetzTomography_triangular a i,
            lefschetzTomography_triangular b i] at hq
        have hsum : (∑ j : Fin N with j.1 < i.1,
              multiplicityLefschetzKernel j i * a j) =
            (∑ j : Fin N with j.1 < i.1,
              multiplicityLefschetzKernel j i * b j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp only [Finset.mem_filter] at hj
          rw [ih j (by omega)]
        rw [hsum] at hq
        exact add_right_cancel hq
  funext q
  exact key q.1 q le_rfl

/-- Zero tomography is equivalent to a zero finite state. -/
theorem lefschetzTomography_eq_zero_iff
    {N : Nat} (a : Fin N → ℚ) :
    lefschetzTomography a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 : lefschetzTomography (0 : Fin N → ℚ) = 0 := by
      funext q
      simp [lefschetzTomography]
    exact lefschetzTomography_injective (h.trans h0.symm)
  · rintro rfl
    funext q
    simp [lefschetzTomography]

/-- Any nonzero finite multiplicity state has a nonzero exact Lefschetz
moment. -/
theorem exists_nonzero_lefschetzMoment
    {N : Nat} (a : Fin N → ℚ) (ha : a ≠ 0) :
    ∃ q : Fin N, lefschetzTomography a q ≠ 0 := by
  by_contra h
  push_neg at h
  apply ha
  exact (lefschetzTomography_eq_zero_iff a).mp (by
    funext q
    exact h q)

/-- Finite vector of the live coefficients of a compact fibered Hodge state. -/
def supportCoordinateVector
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    Fin (fiberedSupportSize f) → ℚ :=
  fun i => f (((fiberedSupportEquivFin f).symm i).1)

/-- The support vector is zero exactly when the original compact address is
zero. -/
theorem supportCoordinateVector_eq_zero_iff
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H) :
    supportCoordinateVector f = 0 ↔ f = 0 := by
  constructor
  · intro hz
    apply Finsupp.ext
    intro s
    by_cases hs : s ∈ f.support
    · let slive : LiveFiberedAddress f := ⟨s, hs⟩
      have hi := congrFun hz (fiberedSupportEquivFin f slive)
      simpa [supportCoordinateVector, slive] using hi
    · exact Finsupp.notMem_support_iff.mp hs
  · rintro rfl
    funext i
    simp [supportCoordinateVector]

/-- **LEFSCHETZ TOMOGRAPHY OF ONE CLASSICAL HODGE STATE.**  A nonzero
finite-support Hodge coordinate state always produces a nonzero exact
central-binomial Lefschetz moment in its finite multiplicity chart. -/
theorem nonzero_fiberedAddress_has_nonzero_lefschetzMoment
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (f : FiberedHodgeAddress V H)
    (hf : f ≠ 0) :
    ∃ q : Fin (fiberedSupportSize f),
      lefschetzTomography (supportCoordinateVector f) q ≠ 0 := by
  have hvec : supportCoordinateVector f ≠ 0 := by
    intro hz
    exact hf ((supportCoordinateVector_eq_zero_iff f).mp hz)
  exact exists_nonzero_lefschetzMoment (supportCoordinateVector f) hvec

/-- Any nonzero genuine rational Hodge class has a finite multiplicity chart
with a nonzero exact GST Lefschetz moment. -/
theorem nonzero_hodgeClass_has_nonzero_lefschetzMoment
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : Nat)
    (alpha : ClassicalHodgeFiber V H p)
    (halpha : alpha ≠ 0) :
    ∃ q : Fin
        (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)),
      lefschetzTomography
        (supportCoordinateVector
          (fiberedWeightCoordinates V H p alpha)) q ≠ 0 := by
  apply nonzero_fiberedAddress_has_nonzero_lefschetzMoment
  intro hzero
  apply halpha
  apply fiberedWeightCoordinates_injective V H p
  simpa [fiberedWeightCoordinates] using hzero

/-- Tomography crown: exact central-binomial kernel, unit-triangular
injectivity, and finite detection of every nonzero classical Hodge state. -/
theorem classical_hodge_lefschetz_tomography_crown
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V) :
    (∀ N, Function.Injective (@lefschetzTomography N))
    ∧ (∀ p : Nat, ∀ alpha : ClassicalHodgeFiber V H p,
      alpha ≠ 0 →
        ∃ q : Fin
            (fiberedSupportSize (fiberedWeightCoordinates V H p alpha)),
          lefschetzTomography
            (supportCoordinateVector
              (fiberedWeightCoordinates V H p alpha)) q ≠ 0) := by
  exact ⟨
    fun N => lefschetzTomography_injective,
    fun p alpha h =>
      nonzero_hodgeClass_has_nonzero_lefschetzMoment V H p alpha h⟩

#check multiplicityLefschetzKernel
#check multiplicityLefschetzKernel_eq_worldAct
#check lefschetzTomography
#check lefschetzTomography_triangular
#check lefschetzTomography_injective
#check lefschetzTomography_eq_zero_iff
#check exists_nonzero_lefschetzMoment
#check supportCoordinateVector
#check supportCoordinateVector_eq_zero_iff
#check nonzero_fiberedAddress_has_nonzero_lefschetzMoment
#check nonzero_hodgeClass_has_nonzero_lefschetzMoment
#check classical_hodge_lefschetz_tomography_crown

#print axioms multiplicityLefschetzKernel_eq_worldAct
#print axioms lefschetzTomography_injective
#print axioms nonzero_hodgeClass_has_nonzero_lefschetzMoment
#print axioms classical_hodge_lefschetz_tomography_crown

end GSTClassicalHodgeLefschetzTomography
