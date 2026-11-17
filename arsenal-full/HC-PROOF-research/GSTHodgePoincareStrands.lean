import Mathlib
import GSTWorldPoincareDuality
import GSTGlobalPureHodgeCosmology

/-!
# GST HODGE-POINCARE STRAND GEOMETRY

For a cell (C,d) define its signed Hodge charge q = C-d.

The full rectangular GST world decomposes into charge strands. Poincare
duality reflects charge around the world asymmetry A-B,

    q |-> (A-B)-q.

Digit transport lowers charge, carry transport raises charge, and the top
pairing is orthogonal between all strand pairs except complementary ones.
The pure diagonal is exactly the q=0 strand. Therefore the pure diagonal is
Poincare-stable precisely in balanced square worlds.

This adds a second grading to the existing total Lefschetz degree and exposes
how the Hodge bigrading, axis cups and Poincare duality fit together.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTHodgePoincareStrands

open GSTWorldCosmology
open GSTGradedWorldAlgebra
open GSTWorldPoincareDuality
open GSTGlobalPureHodgeCosmology
open GSTWorldRecoordinationGroupoid

/-- Signed Hodge charge of one world cell. -/
def worldHodgeCharge {A B : Nat} (c : WorldCell A B) : Int :=
  (c.1.1 : Int) - (c.2.1 : Int)

/-- Affine center of Poincare charge reflection. -/
def worldChargeCenter (A B : Nat) : Int :=
  (A : Int) - (B : Int)

/-- **HODGE-POINCARE CHARGE REFLECTION.**
Complementation reflects charge around A-B. -/
theorem worldHodgeCharge_dual
    {A B : Nat} (c : WorldCell A B) :
    worldHodgeCharge (worldDual c) =
      worldChargeCenter A B - worldHodgeCharge c := by
  rcases c with ⟨⟨C,hC⟩,⟨d,hd⟩⟩
  unfold worldHodgeCharge worldChargeCenter worldDual complementFin
  simp only
  omega

/-- Cells on one exact Hodge-charge strand. -/
abbrev HodgeChargeCell (A B : Nat) (q : Int) : Type :=
  {c : WorldCell A B // worldHodgeCharge c = q}

/-- Poincare duality is an equivalence between complementary charge strands. -/
def chargeDualEquiv
    {A B : Nat} (q : Int) :
    HodgeChargeCell A B q ≃
      HodgeChargeCell A B (worldChargeCenter A B - q) where
  toFun c :=
    ⟨worldDual c.1, by
      rw [worldHodgeCharge_dual, c.2]⟩
  invFun c :=
    ⟨worldDual c.1, by
      rw [worldHodgeCharge_dual, c.2]
      ring⟩
  left_inv c := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- Charge strands occur in exact Poincare-symmetric cardinalities. -/
theorem chargeCell_card_symmetry
    {A B : Nat} (q : Int) :
    Fintype.card (HodgeChargeCell A B q) =
      Fintype.card
        (HodgeChargeCell A B (worldChargeCenter A B - q)) := by
  exact Fintype.card_congr (chargeDualEquiv q)

/-- Project a world amplitude onto one Hodge-charge strand. -/
def worldHodgeStrandProj
    {A B : Nat} (q : Int)
    (f : WorldCoef A B) : WorldCoef A B :=
  fun c => if worldHodgeCharge c = q then f c else 0

/-- Charge projectors are idempotent. -/
theorem worldHodgeStrandProj_idempotent
    {A B : Nat} (q : Int) (f : WorldCoef A B) :
    worldHodgeStrandProj q (worldHodgeStrandProj q f) =
      worldHodgeStrandProj q f := by
  funext c
  by_cases h : worldHodgeCharge c = q <;>
    simp [worldHodgeStrandProj, h]

/-- Distinct charge strands are exactly orthogonal. -/
theorem worldHodgeStrandProj_orthogonal
    {A B : Nat} (q r : Int) (hqr : q ≠ r)
    (f : WorldCoef A B) :
    worldHodgeStrandProj q (worldHodgeStrandProj r f) =
      fun _ => 0 := by
  funext c
  by_cases hq : worldHodgeCharge c = q
  · have hr : worldHodgeCharge c ≠ r := by
      intro h
      apply hqr
      linarith
    simp [worldHodgeStrandProj, hq, hr, hqr]
  · simp [worldHodgeStrandProj, hq]

/-- Digit-axis transport lowers Hodge charge by exactly n. -/
theorem digitShiftN_respects_hodgeCharge
    {A B : Nat} (n : Nat) (q : Int) (f : WorldCoef A B) :
    digitShiftN n (worldHodgeStrandProj q f) =
      worldHodgeStrandProj (q - (n : Int)) (digitShiftN n f) := by
  funext c
  by_cases hn : n ≤ c.2.1
  · have hiff : ∀ p : c.2.1 - n < B,
        worldHodgeCharge
            ((c.1, ⟨c.2.1 - n, p⟩) : WorldCell A B) = q ↔
          worldHodgeCharge c = q - (n : Int) := by
      intro p
      show ((c.1).1 : Int) - ((c.2.1 - n : Nat) : Int) = q ↔
        ((c.1).1 : Int) - ((c.2).1 : Int) = q - (n : Int)
      omega
    simp [digitShiftN, worldHodgeStrandProj, hn, hiff]
  · simp [digitShiftN, worldHodgeStrandProj, hn]

/-- Carry-axis transport raises Hodge charge by exactly n. -/
theorem carryShiftN_respects_hodgeCharge
    {A B : Nat} (n : Nat) (q : Int) (f : WorldCoef A B) :
    carryShiftN n (worldHodgeStrandProj q f) =
      worldHodgeStrandProj (q + (n : Int)) (carryShiftN n f) := by
  funext c
  by_cases hn : n ≤ c.1.1
  · have hiff : ∀ p : c.1.1 - n < A,
        worldHodgeCharge
            ((⟨c.1.1 - n, p⟩, c.2) : WorldCell A B) = q ↔
          worldHodgeCharge c = q + (n : Int) := by
      intro p
      show ((c.1.1 - n : Nat) : Int) - ((c.2).1 : Int) = q ↔
        ((c.1).1 : Int) - ((c.2).1 : Int) = q + (n : Int)
      omega
    simp [carryShiftN, worldHodgeStrandProj, hn, hiff]
  · simp [carryShiftN, worldHodgeStrandProj, hn]

/-- Pure diagonal support is exactly fixed support in the zero-charge strand. -/
theorem pure_iff_zero_charge_fixed
    {A B : Nat} (f : ShapeCoef (outputShape A B)) :
    isWorldPureHodge f ↔
      worldHodgeStrandProj 0 f = f := by
  constructor
  · intro hf
    funext c
    by_cases hdiag : c.1.1 = c.2.1
    · have hq : worldHodgeCharge c = 0 := by
        unfold worldHodgeCharge
        omega
      simp [worldHodgeStrandProj, hq]
    · have hq : worldHodgeCharge c ≠ 0 := by
        intro h
        unfold worldHodgeCharge at h
        omega
      simp [worldHodgeStrandProj, hq, hf c hdiag]
  · intro hfix c hdiag
    have hq : worldHodgeCharge c ≠ 0 := by
      intro h
      unfold worldHodgeCharge at h
      omega
    have hc := congrFun hfix c
    simp [worldHodgeStrandProj, hq] at hc
    exact hc.symm

/-- Pull a cochain back through Poincare complement. -/
def worldDualPullback
    {A B : Nat} (f : WorldCoef A B) : WorldCoef A B :=
  fun c => f (worldDual c)

@[simp]
theorem worldDualPullback_involutive
    {A B : Nat} (f : WorldCoef A B) :
    worldDualPullback (worldDualPullback f) = f := by
  funext c
  simp [worldDualPullback]

/-- Poincare pullback transports a charge-q strand to its exact reflected
charge (A-B)-q. -/
theorem worldDualPullback_strand
    {A B : Nat} (q : Int) (f : WorldCoef A B) :
    worldDualPullback (worldHodgeStrandProj q f) =
      worldHodgeStrandProj (worldChargeCenter A B - q)
        (worldDualPullback f) := by
  funext c
  have hiff :
      worldHodgeCharge (worldDual c) = q ↔
        worldHodgeCharge c = worldChargeCenter A B - q := by
    rw [worldHodgeCharge_dual]
    constructor <;> intro h <;> linarith
  simp [worldDualPullback, worldHodgeStrandProj, hiff]

/-- **HODGE-POINCARE STRAND ORTHOGONALITY.**
Two charge strands pair to zero unless their charges add to A-B. -/
theorem worldTopPairing_charge_strands_zero
    {A B : Nat} (q r : Int)
    (hqr : q + r ≠ worldChargeCenter A B)
    (f g : WorldCoef A B) :
    worldTopPairing
      (worldHodgeStrandProj q f)
      (worldHodgeStrandProj r g) = 0 := by
  classical
  unfold worldTopPairing
  apply Finset.sum_eq_zero
  intro c hc
  by_cases hq : worldHodgeCharge c = q
  · by_cases hr : worldHodgeCharge (worldDual c) = r
    · exfalso
      apply hqr
      have hd := worldHodgeCharge_dual c
      linarith
    · simp [worldHodgeStrandProj, hq, hr]
  · simp [worldHodgeStrandProj, hq]

/-- In balanced square worlds, Poincare duality preserves the pure diagonal
sector exactly. -/
theorem worldDualPullback_preserves_pure_square
    {A : Nat} (f : ShapeCoef (outputShape A A))
    (hf : isWorldPureHodge f) :
    isWorldPureHodge (worldDualPullback f) := by
  rw [pure_iff_zero_charge_fixed (A := A) (B := A)] at hf
  have hstep1 : worldDualPullback f =
      worldDualPullback (worldHodgeStrandProj 0 f) :=
    congrArg worldDualPullback hf.symm
  have hstrand : worldDualPullback (worldHodgeStrandProj 0 f) =
      worldHodgeStrandProj (worldChargeCenter A A - 0) (worldDualPullback f) :=
    worldDualPullback_strand (A := A) (B := A) 0 f
  have hcenter : worldChargeCenter A A - 0 = 0 := by
    unfold worldChargeCenter
    ring
  rw [hcenter] at hstrand
  have hfinal : worldDualPullback f =
      worldHodgeStrandProj 0 (worldDualPullback f) :=
    hstep1.trans hstrand
  exact (pure_iff_zero_charge_fixed (A := A) (B := A) (worldDualPullback f)).mpr
    hfinal.symm

/-- The diagonal charge is Poincare self-complementary exactly for balanced
world dimensions. -/
theorem zero_charge_dual_center
    (A B : Nat) :
    worldChargeCenter A B - 0 = 0 ↔ A = B := by
  unfold worldChargeCenter
  omega

/-- One crown collecting the Hodge-charge/Poincare upgrade. -/
theorem hodge_poincare_strand_crown :
    (∀ A B (c : WorldCell A B),
      worldHodgeCharge (worldDual c) =
        worldChargeCenter A B - worldHodgeCharge c)
    ∧ (∀ A B (q : Int),
      Fintype.card (HodgeChargeCell A B q) =
        Fintype.card
          (HodgeChargeCell A B (worldChargeCenter A B - q)))
    ∧ (∀ A B (q r : Int),
      q+r ≠ worldChargeCenter A B ->
      ∀ f g : WorldCoef A B,
        worldTopPairing
          (worldHodgeStrandProj q f)
          (worldHodgeStrandProj r g) = 0)
    ∧ (∀ A (f : ShapeCoef (outputShape A A)),
      isWorldPureHodge f ->
        isWorldPureHodge (worldDualPullback f)) := by
  exact ⟨
    fun A B c => @worldHodgeCharge_dual A B c,
    fun A B q => @chargeCell_card_symmetry A B q,
    fun A B q r hqr f g => @worldTopPairing_charge_strands_zero A B q r hqr f g,
    fun A f hf => @worldDualPullback_preserves_pure_square A f hf⟩

#check worldHodgeCharge
#check worldHodgeCharge_dual
#check chargeDualEquiv
#check chargeCell_card_symmetry
#check worldHodgeStrandProj
#check digitShiftN_respects_hodgeCharge
#check carryShiftN_respects_hodgeCharge
#check pure_iff_zero_charge_fixed
#check worldDualPullback_strand
#check worldTopPairing_charge_strands_zero
#check worldDualPullback_preserves_pure_square
#check zero_charge_dual_center
#check hodge_poincare_strand_crown

#print axioms worldHodgeCharge_dual
#print axioms chargeCell_card_symmetry
#print axioms digitShiftN_respects_hodgeCharge
#print axioms worldTopPairing_charge_strands_zero
#print axioms worldDualPullback_preserves_pure_square
#print axioms hodge_poincare_strand_crown

end GSTHodgePoincareStrands
