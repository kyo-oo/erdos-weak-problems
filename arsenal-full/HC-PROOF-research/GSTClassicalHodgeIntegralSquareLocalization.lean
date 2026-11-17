import GSTClassicalHodgeSquareStrandLocalization
import GSTGlobalPureHodgeCosmology

/-!
# GST CLASSICAL HODGE — INTEGRAL PURE-SQUARE LOCALIZATION

Every concrete classical rational Hodge state has finite basis support.  Hence
all denominators occurring in one local finite square can be cleared by one
positive integer.  This module performs that clearing uniformly.

The result is an integral pure-Hodge GST square, exactly in the coefficient
ring used by the strongest existing Poincare/Lefschetz/Hodge theorems.  For a
pair of rational pure states, clearing the two denominator families scales the
rational Poincare pairing by the positive product of the denominators and
turns it into the integral GST top pairing.

Thus any nonzero rational separator witness admits a nonzero integral
pure-vs-pure GST witness in one finite square.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTProjectiveOverC
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeAtomicDefectDuality
open GSTClassicalHodgeSeparatorProbe
open GSTClassicalHodgeSquareStrandLocalization
open GSTWorldPoincareDuality
open GSTGlobalPureHodgeCosmology
open GSTWorldRecoordinationGroupoid
open GSTWorldCosmology
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiniteSupportChart

namespace GSTClassicalHodgeIntegralSquareLocalization

/-! ## 1. One common denominator for a finite rational family -/

/-- Product of all reduced denominators in one finite rational family. -/
def commonDenominator
    {ι : Type*} [Fintype ι]
    (a : ι → ℚ) : Nat :=
  ∏ i : ι, (a i).den

/-- The common denominator is strictly positive. -/
theorem commonDenominator_pos
    {ι : Type*} [Fintype ι]
    (a : ι → ℚ) :
    0 < commonDenominator a := by
  classical
  unfold commonDenominator
  exact Finset.prod_pos fun i _ => Rat.pos (a i)

/-- Every coordinate denominator divides the global denominator. -/
theorem denominator_dvd_commonDenominator
    {ι : Type*} [Fintype ι]
    (a : ι → ℚ) (i : ι) :
    (a i).den ∣ commonDenominator a := by
  classical
  unfold commonDenominator
  exact Finset.dvd_prod_of_mem (fun j => (a j).den) (Finset.mem_univ i)

/-- Multiplication by the common denominator makes every coordinate integral. -/
theorem commonDenominator_integral
    {ι : Type*} [Fintype ι]
    (a : ι → ℚ) (i : ι) :
    ∃ z : ℤ,
      (commonDenominator a : ℚ) * a i = (z : ℚ) := by
  obtain ⟨k, hk⟩ := denominator_dvd_commonDenominator a i
  refine ⟨(a i).num * (k : ℤ), ?_⟩
  rw [hk]
  push_cast
  rw [mul_comm ((a i).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
  ring

/-- Canonically choose the integral coordinate produced by denominator
clearing. -/
noncomputable def clearedCoordinate
    {ι : Type*} [Fintype ι]
    (a : ι → ℚ) (i : ι) : ℤ :=
  Classical.choose (commonDenominator_integral a i)

@[simp]
theorem commonDenominator_mul_eq_clearedCoordinate
    {ι : Type*} [Fintype ι]
    (a : ι → ℚ) (i : ι) :
    (commonDenominator a : ℚ) * a i =
      (clearedCoordinate a i : ℚ) :=
  Classical.choose_spec (commonDenominator_integral a i)

/-- Finite denominator-clearing crown. -/
theorem finite_rational_clear_denominators
    {ι : Type*} [Fintype ι]
    (a : ι → ℚ) :
    ∃ D : Nat, 0 < D ∧
      ∃ z : ι → ℤ,
        ∀ i, (D : ℚ) * a i = (z i : ℚ) := by
  exact ⟨commonDenominator a, commonDenominator_pos a,
    clearedCoordinate a,
    commonDenominator_mul_eq_clearedCoordinate a⟩

/-! ## 2. Integralization of a rational pure GST square -/

/-- Diagonal coordinates of a rational pure square. -/
def rationalPureCoordinates
    {N : Nat} (a : RationalWorldCoef N) : Fin N → ℚ :=
  fun i => a (i,i)

/-- Integral diagonal world obtained by clearing the denominators of the
rational diagonal coordinates. -/
def clearedIntegralWorld
    {N : Nat} (a : RationalWorldCoef N) :
    ShapeCoef (outputShape N N) := by
  classical
  exact fun c =>
    if h : c.1 = c.2 then
      clearedCoordinate (rationalPureCoordinates a) c.1
    else 0

/-- The cleared world is an integral pure-Hodge world. -/
theorem clearedIntegralWorld_isPure
    {N : Nat} (a : RationalWorldCoef N) :
    isWorldPureHodge (clearedIntegralWorld a) := by
  intro c hc
  have hne : c.1 ≠ c.2 := by
    intro h
    exact hc (congrArg Fin.val h)
  simp [clearedIntegralWorld, hne]

/-- Clearing is exact on every diagonal coordinate. -/
theorem clearedIntegralWorld_diagonal
    {N : Nat} (a : RationalWorldCoef N) (i : Fin N) :
    (commonDenominator (rationalPureCoordinates a) : ℚ) * a (i,i) =
      (clearedIntegralWorld a (i,i) : ℚ) := by
  have hdite : (clearedIntegralWorld a (i,i) : ℤ) =
      (clearedCoordinate (rationalPureCoordinates a) i : ℤ) :=
    dif_pos (rfl : (i, i).1 = (i, i).2)
  rw [hdite]
  exact commonDenominator_mul_eq_clearedCoordinate
      (rationalPureCoordinates a) i

/-- For a rational pure state, denominator clearing agrees pointwise on the
whole square, not only on the diagonal. -/
theorem clearedIntegralWorld_pointwise
    {N : Nat} (a : RationalWorldCoef N)
    (ha : IsRationalPureHodge a)
    (c : WorldCell N N) :
    (commonDenominator (rationalPureCoordinates a) : ℚ) * a c =
      (clearedIntegralWorld a c : ℚ) := by
  by_cases hdiag : c.1.1 = c.2.1
  · have heq : c.1 = c.2 := Fin.ext hdiag
    have hcc : c = (c.1, c.2) := rfl
    rw [hcc, ← heq]
    exact clearedIntegralWorld_diagonal a c.1
  · have hazero := ha c hdiag
    have hne : c.1 ≠ c.2 := by
      intro h
      exact hdiag (congrArg Fin.val h)
    have hdite : clearedIntegralWorld a c = 0 := by
      simp only [clearedIntegralWorld]
      exact dif_neg hne
    rw [hdite]
    push_cast
    rw [mul_eq_zero]
    exact Or.inr hazero

/-- Package one rational pure state together with its exact positive integral
scaling and integral GST representative. -/
structure IntegralPureSquareModel
    {N : Nat} (a : RationalWorldCoef N) where
  scale : Nat
  scale_pos : 0 < scale
  world : ShapeCoef (outputShape N N)
  world_pure : isWorldPureHodge world
  scaled_eq : ∀ c : WorldCell N N,
    (scale : ℚ) * a c = (world c : ℚ)

/-- Canonical integral model of a rational pure square. -/
noncomputable def canonicalIntegralPureSquareModel
    {N : Nat} (a : RationalWorldCoef N)
    (ha : IsRationalPureHodge a) :
    IntegralPureSquareModel a where
  scale := commonDenominator (rationalPureCoordinates a)
  scale_pos := commonDenominator_pos (rationalPureCoordinates a)
  world := clearedIntegralWorld a
  world_pure := clearedIntegralWorld_isPure a
  scaled_eq := clearedIntegralWorld_pointwise a ha

/-- Positive denominator clearing cannot erase a nonzero rational pure state. -/
theorem canonicalIntegralPureSquareModel_ne_zero
    {N : Nat} (a : RationalWorldCoef N)
    (ha : IsRationalPureHodge a)
    (hne : a ≠ 0) :
    (canonicalIntegralPureSquareModel a ha).world ≠ 0 := by
  intro hw
  apply hne
  funext c
  have hscaled :=
    (canonicalIntegralPureSquareModel a ha).scaled_eq c
  rw [hw] at hscaled
  have hzc : ((0 : ShapeCoef (outputShape N N)) c : ℚ) = 0 := rfl
  rw [hzc] at hscaled
  have hD :
      (canonicalIntegralPureSquareModel a ha).scale ≠ 0 :=
    Nat.ne_of_gt (canonicalIntegralPureSquareModel a ha).scale_pos
  have hDz :
      ((canonicalIntegralPureSquareModel a ha).scale : ℚ) ≠ 0 := by
    exact_mod_cast hD
  exact (mul_eq_zero.mp hscaled).resolve_left hDz

/-! ## 3. Pairing transport from Q to Z -/

/-- Clearing denominators on two rational pure states converts their rational
Poincare pairing into the integral GST top pairing, up to the positive product
of the two clearing scales. -/
theorem integralModels_pairing_scale
    {N : Nat} (a b : RationalWorldCoef N)
    (ha : IsRationalPureHodge a)
    (hb : IsRationalPureHodge b) :
    (((canonicalIntegralPureSquareModel a ha).scale : ℚ) *
      ((canonicalIntegralPureSquareModel b hb).scale : ℚ)) *
        rationalWorldTopPairing a b =
      ((worldTopPairing
        (canonicalIntegralPureSquareModel a ha).world
        (canonicalIntegralPureSquareModel b hb).world : ℤ) : ℚ) := by
  classical
  unfold rationalWorldTopPairing worldTopPairing
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro c hc
  have haC := (canonicalIntegralPureSquareModel a ha).scaled_eq c
  have hbC := (canonicalIntegralPureSquareModel b hb).scaled_eq (worldDual c)
  have hcongr :
      (((canonicalIntegralPureSquareModel a ha).scale : ℚ) * a c) *
      (((canonicalIntegralPureSquareModel b hb).scale : ℚ) *
        b (worldDual c)) =
      (((canonicalIntegralPureSquareModel a ha).world c : ℤ) : ℚ) *
      (((canonicalIntegralPureSquareModel b hb).world (worldDual c) : ℤ) :
        ℚ) :=
    congrArg₂ (fun x y : ℚ => x * y) haC hbC
  calc (((canonicalIntegralPureSquareModel a ha).scale : ℚ) *
      ((canonicalIntegralPureSquareModel b hb).scale : ℚ)) *
      (a c * b (worldDual c))
      = (((canonicalIntegralPureSquareModel a ha).scale : ℚ) * a c) *
        (((canonicalIntegralPureSquareModel b hb).scale : ℚ) *
          b (worldDual c)) := by
        ring
    _ = (((canonicalIntegralPureSquareModel a ha).world c : ℤ) : ℚ) *
        (((canonicalIntegralPureSquareModel b hb).world (worldDual c) : ℤ) :
          ℚ) := hcongr

/-- Nonzero rational pure pairing survives denominator clearing as a nonzero
integral GST Poincare pairing. -/
theorem nonzero_rationalPairing_yields_nonzero_integralPairing
    {N : Nat} (a b : RationalWorldCoef N)
    (ha : IsRationalPureHodge a)
    (hb : IsRationalPureHodge b)
    (hpair : rationalWorldTopPairing a b ≠ 0) :
    worldTopPairing
      (canonicalIntegralPureSquareModel a ha).world
      (canonicalIntegralPureSquareModel b hb).world ≠ 0 := by
  intro hzero
  have hscale := integralModels_pairing_scale a b ha hb
  rw [hzero] at hscale
  simp at hscale
  have hDa :
      ((canonicalIntegralPureSquareModel a ha).scale : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (canonicalIntegralPureSquareModel a ha).scale_pos
  have hDb :
      ((canonicalIntegralPureSquareModel b hb).scale : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (canonicalIntegralPureSquareModel b hb).scale_pos
  exact hpair ((mul_eq_zero.mp (by simpa using hscale)).resolve_left
    (mul_ne_zero hDa hDb))

/-- **INTEGRAL PURE-SQUARE REDUCTION OF HODGE FAILURE.**
Any classical Stage-2G separator witness gives one finite square and two
integral pure GST worlds with nonzero native integral Poincare pairing. -/
theorem not_hodge_yields_nonzero_integralPureSquare_pairing
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hnot : ¬ GSTGeometricRealizationStage2G.BigradedBettiHodgeStatement V H) :
    ∃ N : Nat,
    ∃ A B : ShapeCoef (outputShape N N),
      isWorldPureHodge A ∧
      isWorldPureHodge B ∧
      worldTopPairing A B ≠ 0 := by
  obtain ⟨p,S,a,b,ha,hb,hpair⟩ :=
    not_hodge_yields_nonzero_pureSquare_pairing V H hnot
  let IA := canonicalIntegralPureSquareModel a ha
  let IB := canonicalIntegralPureSquareModel b hb
  refine ⟨fiberedSupportSize
      (fiberedWeightCoordinates V H p S.alpha),
    IA.world, IB.world, IA.world_pure, IB.world_pure, ?_⟩
  exact nonzero_rationalPairing_yields_nonzero_integralPairing
    a b ha hb hpair

/-- The same reduction packaged through the canonical pure-Hodge coordinate
equivalence: every witness lies in a finite free integral diagonal module. -/
theorem not_hodge_yields_nonzero_integralPureCoordinates
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (hnot : ¬ GSTGeometricRealizationStage2G.BigradedBettiHodgeStatement V H) :
    ∃ N : Nat,
    ∃ A B : PureWorldHodge N N,
      worldTopPairing A.1 B.1 ≠ 0 := by
  obtain ⟨N,A,B,hA,hB,hpair⟩ :=
    not_hodge_yields_nonzero_integralPureSquare_pairing V H hnot
  exact ⟨N, ⟨A,hA⟩, ⟨B,hB⟩, hpair⟩

#check commonDenominator
#check commonDenominator_pos
#check denominator_dvd_commonDenominator
#check commonDenominator_integral
#check finite_rational_clear_denominators
#check rationalPureCoordinates
#check clearedIntegralWorld
#check clearedIntegralWorld_isPure
#check clearedIntegralWorld_pointwise
#check IntegralPureSquareModel
#check canonicalIntegralPureSquareModel
#check canonicalIntegralPureSquareModel_ne_zero
#check integralModels_pairing_scale
#check nonzero_rationalPairing_yields_nonzero_integralPairing
#check not_hodge_yields_nonzero_integralPureSquare_pairing
#check not_hodge_yields_nonzero_integralPureCoordinates

#print axioms finite_rational_clear_denominators
#print axioms clearedIntegralWorld_pointwise
#print axioms canonicalIntegralPureSquareModel_ne_zero
#print axioms integralModels_pairing_scale
#print axioms nonzero_rationalPairing_yields_nonzero_integralPairing
#print axioms not_hodge_yields_nonzero_integralPureSquare_pairing
#print axioms not_hodge_yields_nonzero_integralPureCoordinates

end GSTClassicalHodgeIntegralSquareLocalization
