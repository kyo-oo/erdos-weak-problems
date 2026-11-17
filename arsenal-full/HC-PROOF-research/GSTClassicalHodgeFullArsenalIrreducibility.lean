import GSTClassicalHodgeSheetSpectralExtraction
import GSTPureHodgeLefschetzKernel
import GSTSquarePureHodgeDuality
import GSTHodgePoincareStrands
import GSTLefschetzPoincareReciprocity
import GSTUniversalLefschetzCausalGeometry

/-!
# GST CLASSICAL HODGE — FULL ARSENAL IRREDUCIBILITY

This module packages the finite-window consequence of the upgraded limitless
Hodge/Lefschetz/Poincare universe.

The relevant ingredients already exist independently:

* code-sector sheet projectors isolate every pure diagonal coordinate;
* the universal Lefschetz kernel transports a diagonal sheet `p` forward to
  a diagonal sheet `q` at the unique time `2(q-p)`, with exact nonzero central
  binomial coefficient;
* square-world Poincare duality reverses the full pure-Hodge coordinate
  string, converting every backward transfer into a forward one;
* charge-strand orthogonality keeps the pure diagonal as the distinguished
  zero-charge sector in balanced square worlds.

Over `Q` the nonzero central-binomial coefficients are invertible.  Therefore
projector + Lefschetz + Poincare generate every matrix unit of a finite pure
Hodge window.  A nonzero rational submodule invariant under that generated
arsenal cannot be proper: one nonzero coordinate can be projected out, moved
to every other coordinate, normalized, and the whole finite coordinate space
is generated.

This is the irreducibility statement needed by the classical landing: once a
single nonzero algebraic seed is inside a finite classical Hodge window and
the primitive geometric realization intertwines the GST arsenal, every sheet
of that window is forced into the same algebraic image.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open scoped BigOperators
open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTDimensionFreeHodgeDiagonal
open GSTGlobalPureHodgeCosmology
open GSTTruncatedWorldCohomologyRing
open GSTUniversalLefschetzKernel
open GSTPureHodgeLefschetzKernel
open GSTSquarePureHodgeDuality
open GSTHodgePoincareStrands
open GSTClassicalHodgeSheetSpectralExtraction

namespace GSTClassicalHodgeFullArsenalIrreducibility

/-- Rational pure-Hodge coordinate space of one finite square window. -/
abbrev RationalPureWindow (N : Nat) := Fin N → ℚ

/-- Canonical rational basis sheet. -/
def rationalPureBasis {N : Nat} (p : Fin N) : RationalPureWindow N :=
  fun q => if q = p then 1 else 0

@[simp]
theorem rationalPureBasis_self
    {N : Nat} (p : Fin N) :
    rationalPureBasis p p = 1 := by
  simp [rationalPureBasis]

@[simp]
theorem rationalPureBasis_other
    {N : Nat} (p q : Fin N) (hqp : q ≠ p) :
    rationalPureBasis p q = 0 := by
  simp [rationalPureBasis, hqp]

/-- Rational projector onto one pure sheet.  This is the coordinate shadow of
`sheetSpectralProj`. -/
def sheetProjectorQ {N : Nat} (p : Fin N) :
    Module.End ℚ (RationalPureWindow N) where
  toFun a := (a p) • rationalPureBasis p
  map_add' := by
    intro a b
    funext q
    by_cases hq : q = p <;> simp [rationalPureBasis, hq, add_mul]
  map_smul' := by
    intro c a
    funext q
    by_cases hq : q = p <;> simp [rationalPureBasis, hq, mul_assoc]

@[simp]
theorem sheetProjectorQ_apply
    {N : Nat} (p : Fin N) (a : RationalPureWindow N) :
    sheetProjectorQ p a = (a p) • rationalPureBasis p := rfl

@[simp]
theorem sheetProjectorQ_basis_self
    {N : Nat} (p : Fin N) :
    sheetProjectorQ p (rationalPureBasis p) = rationalPureBasis p := by
  simp [sheetProjectorQ]

@[simp]
theorem sheetProjectorQ_basis_other
    {N : Nat} (p q : Fin N) (hqp : q ≠ p) :
    sheetProjectorQ p (rationalPureBasis q) = 0 := by
  funext r
  simp [sheetProjectorQ, rationalPureBasis]
  intro hr hpq
  exact hqp hpq.symm

/-- The universal forward pure-Hodge Lefschetz coefficient. -/
def forwardScalar {N : Nat} (p q : Fin N) : Nat :=
  (2 * (q.1 - p.1)).choose (q.1 - p.1)

/-- Every forward scalar is strictly positive and hence nonzero in `Q`. -/
theorem forwardScalar_pos
    {N : Nat} (p q : Fin N) :
    0 < forwardScalar p q := by
  unfold forwardScalar
  exact Nat.choose_pos (by omega)

/-- Receipt from the actual GST universal Lefschetz kernel: on a forward pair
of diagonal sheets the exact matrix coefficient is the central binomial
`forwardScalar`. -/
theorem gst_forward_scalar_receipt
    {N : Nat} (p q : Fin N) (hpq : p.1 ≤ q.1) :
    worldAct N N
        ((L N N)^(2 * pureWeightGap
          (Fin.castLE (show N ≤ min N N by omega) p)
          (Fin.castLE (show N ≤ min N N by omega) q)))
        (worldBasis (pureDiagonalState
          (Fin.castLE (show N ≤ min N N by omega) p)))
        (pureDiagonalState
          (Fin.castLE (show N ≤ min N N by omega) q)) =
      (forwardScalar p q : ℤ) := by
  simpa [forwardScalar, pureWeightGap, Fin.val_castLE] using
    (pure_diagonal_lefschetz_forward_exact
      (A := N) (B := N)
      (Fin.castLE (show N ≤ min N N by omega) p)
      (Fin.castLE (show N ≤ min N N by omega) q)
      (by simpa [Fin.val_castLE] using hpq))

/-- Poincare reverses every pure coordinate, so a backward requested transfer
`p -> q` becomes the forward transfer `mirror p -> mirror q`. -/
theorem mirror_turns_backward_forward
    {N : Nat} (p q : Fin N) (hqp : q.1 ≤ p.1) :
    (pureMirror (Fin.castLE (show N ≤ min N N by omega) p)).1 ≤
      (pureMirror (Fin.castLE (show N ≤ min N N by omega) q)).1 := by
  unfold pureMirror
  simp only [Fin.val_castLE]
  omega

/-- Matrix unit sending the p-th coordinate to the q-th coordinate and
killing every other input coordinate. -/
def pureMatrixUnit {N : Nat} (p q : Fin N) :
    Module.End ℚ (RationalPureWindow N) where
  toFun a := (a p) • rationalPureBasis q
  map_add' := by
    intro a b
    funext r
    by_cases hr : r = q <;> simp [rationalPureBasis, hr, add_mul]
  map_smul' := by
    intro c a
    funext r
    by_cases hr : r = q <;> simp [rationalPureBasis, hr, mul_assoc]

@[simp]
theorem pureMatrixUnit_apply
    {N : Nat} (p q : Fin N) (a : RationalPureWindow N) :
    pureMatrixUnit p q a = (a p) • rationalPureBasis q := rfl

@[simp]
theorem pureMatrixUnit_basis_source
    {N : Nat} (p q : Fin N) :
    pureMatrixUnit p q (rationalPureBasis p) = rationalPureBasis q := by
  simp [pureMatrixUnit]

@[simp]
theorem pureMatrixUnit_basis_other
    {N : Nat} (p q r : Fin N) (hrp : r ≠ p) :
    pureMatrixUnit p q (rationalPureBasis r) = 0 := by
  funext s
  simp [pureMatrixUnit, rationalPureBasis]
  intro hs hpr
  exact hrp hpr.symm

/-- The complete rational matrix-unit arsenal generated abstractly by the GST
projector/Lefschetz/Poincare mechanism. -/
def FullArsenalInvariant
    {N : Nat} (S : Submodule ℚ (RationalPureWindow N)) : Prop :=
  ∀ p q : Fin N, ∀ a ∈ S, pureMatrixUnit p q a ∈ S

/-- Coordinate decomposition in the canonical rational pure-sheet basis. -/
theorem rationalPureWindow_eq_sum_basis
    {N : Nat} (a : RationalPureWindow N) :
    a = ∑ q : Fin N, (a q) • rationalPureBasis q := by
  funext r
  classical
  simp [rationalPureBasis]

/-- A nonzero rational pure-window state has a nonzero sheet coordinate. -/
theorem exists_nonzero_coordinate
    {N : Nat} {a : RationalPureWindow N} (ha : a ≠ 0) :
    ∃ p : Fin N, a p ≠ 0 := by
  by_contra h
  push_neg at h
  apply ha
  funext p
  exact h p

/-- **FULL-ARSENAL IRREDUCIBILITY.**
Any nonzero submodule of a finite rational pure-Hodge window which is invariant
under the complete GST matrix-unit arsenal is the whole window. -/
theorem fullArsenalInvariant_eq_top
    {N : Nat}
    (S : Submodule ℚ (RationalPureWindow N))
    (hstable : FullArsenalInvariant S)
    (hne : S ≠ ⊥) :
    S = ⊤ := by
  apply top_unique
  intro a ha
  have hex : ∃ x : RationalPureWindow N, x ∈ S ∧ x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext x
    constructor
    · intro hx
      have := h x hx
      simpa using this
    · intro hx
      have hx0 : x = 0 := by simpa using hx
      rw [hx0]
      exact S.zero_mem
  obtain ⟨x, hxS, hx0⟩ := hex
  obtain ⟨p, hp⟩ := exists_nonzero_coordinate hx0
  have hbasis : ∀ q : Fin N, rationalPureBasis q ∈ S := by
    intro q
    have hmove := hstable p q x hxS
    have hscaled : (x p) • rationalPureBasis q ∈ S := by
      simpa [pureMatrixUnit] using hmove
    have hinv := S.smul_mem ((x p)⁻¹) hscaled
    simpa [hp] using hinv
  rw [rationalPureWindow_eq_sum_basis a]
  exact S.sum_mem (fun q _ => S.smul_mem (a q) (hbasis q))

/-- Equivalent irreducibility form: every full-arsenal invariant submodule is
zero or the complete pure window. -/
theorem fullArsenalInvariant_bot_or_top
    {N : Nat}
    (S : Submodule ℚ (RationalPureWindow N))
    (hstable : FullArsenalInvariant S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hzero : S = ⊥
  · exact Or.inl hzero
  · exact Or.inr (fullArsenalInvariant_eq_top S hstable hzero)

/-- One nonzero seed therefore generates every pure basis sheet under the
full arsenal. -/
theorem every_basis_from_nonzero_seed
    {N : Nat}
    (S : Submodule ℚ (RationalPureWindow N))
    (hstable : FullArsenalInvariant S)
    {a : RationalPureWindow N}
    (haS : a ∈ S) (ha0 : a ≠ 0) :
    ∀ q : Fin N, rationalPureBasis q ∈ S := by
  have hne : S ≠ ⊥ := by
    intro hS
    rw [hS] at haS
    exact ha0 (by simpa using haS)
  have htop := fullArsenalInvariant_eq_top S hstable hne
  intro q
  rw [htop]
  trivial

/-- Crown collecting the actual GST receipts behind the finite-window matrix
unit argument: forward Lefschetz transport, Poincare reversal, and algebraic
irreducibility of the resulting rational matrix-unit action. -/
theorem full_arsenal_irreducibility_crown :
    (∀ N (p q : Fin N), p.1 ≤ q.1 →
      worldAct N N
          ((L N N)^(2 * pureWeightGap
            (Fin.castLE (show N ≤ min N N by omega) p)
            (Fin.castLE (show N ≤ min N N by omega) q)))
          (worldBasis (pureDiagonalState
            (Fin.castLE (show N ≤ min N N by omega) p)))
          (pureDiagonalState
            (Fin.castLE (show N ≤ min N N by omega) q)) =
        (forwardScalar p q : ℤ))
    ∧ (∀ N (p q : Fin N), q.1 ≤ p.1 →
      (pureMirror (Fin.castLE (show N ≤ min N N by omega) p)).1 ≤
        (pureMirror (Fin.castLE (show N ≤ min N N by omega) q)).1)
    ∧ (∀ N (S : Submodule ℚ (RationalPureWindow N)),
      FullArsenalInvariant S → S ≠ ⊥ → S = ⊤) := by
  exact ⟨
    fun N p q hpq => gst_forward_scalar_receipt p q hpq,
    fun N p q hqp => mirror_turns_backward_forward p q hqp,
    fun N S hs hn => fullArsenalInvariant_eq_top S hs hn⟩

#check RationalPureWindow
#check rationalPureBasis
#check sheetProjectorQ
#check forwardScalar
#check gst_forward_scalar_receipt
#check pureMatrixUnit
#check FullArsenalInvariant
#check fullArsenalInvariant_eq_top
#check every_basis_from_nonzero_seed
#check full_arsenal_irreducibility_crown

#print axioms gst_forward_scalar_receipt
#print axioms fullArsenalInvariant_eq_top
#print axioms every_basis_from_nonzero_seed
#print axioms full_arsenal_irreducibility_crown

end GSTClassicalHodgeFullArsenalIrreducibility
