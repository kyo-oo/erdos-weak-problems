/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1075 / 1132
/-    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/HandwrittenBigNBinaryFactorScratch.lean
/-    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
/-    First-commit : 2026-08-17 22:06:13 +0530  (deea9a0)
/-    Last-commit  : 2026-08-17 22:06:13 +0530  (deea9a0)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-17 22:06:13 +0530  deea9a0  (ker07-dev)
/-        surgery: lock 5c579 with full BIG-N right-chord research monolith
/- ====================================================================== -/

import HandwrittenBigNOmegaScratch
import CanonicalTrapScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Binary factorisation of the GST shared carrier

Exact algebra only.  No residual termination or global transport theorem is
asserted here.
-/

/-- Numerical value of the redundant ternary event word attached to an exact
binary bridge `R -> Y`.  If its local digits are `d + 3e`, its base-three
value is literally `R + 3Y`. -/
def gstBinaryEventWordValueS (R Y : Nat) : Nat := R + 3*Y

/-- A seeded multiply-by-two bridge has global event value `7R + 3a`. -/
theorem gst_binary_seeded_event_valueS (a R : Nat) :
    gstBinaryEventWordValueS R (a + 2*R) = 7*R + 3*a := by
  unfold gstBinaryEventWordValueS
  ring

/-- Two binary bridge layers are exactly one seeded multiply-by-four wave.
The full interior event word cancels from the combination below, leaving only
the two bits of the incoming GST carry. -/
theorem gst_binary_two_layer_event_chargeS
    (a b R : Nat) :
    let Y := a + 2*R
    let Z := b + 2*Y
    gstBinaryEventWordValueS Y Z =
      2 * gstBinaryEventWordValueS R Y + (a + 3*b) := by
  dsimp only
  unfold gstBinaryEventWordValueS
  ring

/-- For a physical GST seed `D<4`, binary bit reversal gives the exact global
space charge of the two microscopic event words. -/
def gstBinarySpaceChargeS (D : Nat) : Nat :=
  D / 2 + 3 * (D % 2)

theorem gst_binary_space_charge_four_valuesS
    (D : Nat) (hD : D < 4) :
    (D = 0 ∧ gstBinarySpaceChargeS D = 0) ∨
    (D = 1 ∧ gstBinarySpaceChargeS D = 3) ∨
    (D = 2 ∧ gstBinarySpaceChargeS D = 1) ∨
    (D = 3 ∧ gstBinarySpaceChargeS D = 4) := by
  have hcases : D = 0 ∨ D = 1 ∨ D = 2 ∨ D = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3 <;>
    subst D <;> norm_num [gstBinarySpaceChargeS]

/-- The central charge `2` never occurs for a legal GST carry. -/
theorem gst_binary_space_charge_ne_twoS
    (D : Nat) (hD : D < 4) :
    gstBinarySpaceChargeS D ≠ 2 := by
  rcases gst_binary_space_charge_four_valuesS D hD with
      h0 | h1 | h2 | h3 <;> omega

/-- NULL/GST+ are exactly the two endpoints of the binary event charge; ALT-
occupies the two interior noncentral values. -/
theorem gst_binary_good_space_charge_endpointsS
    (D : Nat) (hD : D < 4) :
    (D = 0 ∨ D = 3) ↔
      (gstBinarySpaceChargeS D = 0 ∨ gstBinarySpaceChargeS D = 4) := by
  rcases gst_binary_space_charge_four_valuesS D hD with
      h0 | h1 | h2 | h3 <;> omega

/-- Exact event-charge identity for a seeded x4 wave.  The first binary layer
has seed bit `D/2`, the second has seed bit `D%2`; the whole wave collapses to
`gstBinarySpaceChargeS D`. -/
theorem gst_seeded_x4_event_chargeS
    (D R : Nat) :
    let a := D / 2
    let b := D % 2
    let Y := a + 2*R
    let Z := b + 2*Y
    gstBinaryEventWordValueS Y Z =
      2 * gstBinaryEventWordValueS R Y + gstBinarySpaceChargeS D := by
  dsimp only
  exact gst_binary_two_layer_event_chargeS (D/2) (D%2) R

/-- The final integer after the two binary layers is exactly `D + 4R`. -/
theorem gst_seeded_x4_binary_layers_exactS
    (D R : Nat) :
    D % 2 + 2 * (D / 2 + 2*R) = D + 4*R := by
  have hD := Nat.mod_add_div D 2
  omega

/-- Every legal x4 shared-information equation factors through a unique-style
intermediate binary remainder.  `Wmid` is the information state after the
first x2 bridge layer.

The theorem is stated existentially to avoid building subtraction into the
state definition. -/
theorem gst_shared_x4_binary_factorS
    (A D Z W C : Nat)
    (hA : 0 < A)
    (hD : D < 4)
    (hC : C < 4)
    (hW : W < A)
    (hshared : D + 4*Z = W + A*C) :
    ∃ a b c e Wmid,
      D = 2*a + b ∧
      C = 2*c + e ∧
      a < 2 ∧ b < 2 ∧ c < 2 ∧ e < 2 ∧
      Wmid < A ∧
      a + 2*Z = Wmid + A*c ∧
      b + 2*Wmid = W + A*e := by
  let a := D / 2
  let b := D % 2
  let c := C / 2
  let e := C % 2
  let Wmid := (W + A*e) / 2
  have h2 : 0 < (2:Nat) := by decide
  have hDb : D = 2*a + b := by
    dsimp [a, b]
    exact (Nat.mod_add_div D 2).symm
  have hCe : C = 2*c + e := by
    dsimp [c, e]
    exact (Nat.mod_add_div C 2).symm
  have ha : a < 2 := by
    dsimp [a]
    omega
  have hb : b < 2 := by
    dsimp [b]
    exact Nat.mod_lt _ h2
  have hc : c < 2 := by
    dsimp [c]
    omega
  have he : e < 2 := by
    dsimp [e]
    exact Nat.mod_lt _ h2
  have hpar : (W + A*e) % 2 = b := by
    have hmod := congrArg (fun x : Nat => x % 2) hshared
    rw [hDb, hCe] at hmod
    dsimp [b, e]
    omega
  have hWsplit : b + 2*Wmid = W + A*e := by
    dsimp [Wmid]
    have h := Nat.mod_add_div (W + A*e) 2
    rw [hpar] at h
    omega
  have hmid : a + 2*Z = Wmid + A*c := by
    rw [hDb, hCe] at hshared
    omega
  have hWmid : Wmid < A := by
    by_cases he0 : e = 0
    · rw [he0, Nat.mul_zero, Nat.add_zero] at hWsplit
      omega
    · have he1 : e = 1 := by omega
      rw [he1, Nat.mul_one] at hWsplit
      omega
  exact ⟨a, b, c, e, Wmid, hDb, hCe, ha, hb, hc, he,
    hWmid, hmid, hWsplit⟩

/-- After a last child Happy Gate the regenerated child carry `C` is 2 or 3,
so the high binary child bit in the factored shared carrier is forced to one. -/
theorem gst_shared_x4_binary_factor_last_gate_high_bitS
    (A D Z W C : Nat)
    (hA : 0 < A)
    (hD : D < 4)
    (hC : C = 2 ∨ C = 3)
    (hW : W < A)
    (hshared : D + 4*Z = W + A*C) :
    ∃ a b e Wmid,
      D = 2*a + b ∧
      C = 2 + e ∧
      a < 2 ∧ b < 2 ∧ e < 2 ∧ Wmid < A ∧
      a + 2*Z = Wmid + A ∧
      b + 2*Wmid = W + A*e := by
  have hClt : C < 4 := by rcases hC with rfl | rfl <;> decide
  obtain ⟨a,b,c,e,Wmid,hDb,hCe,ha,hb,hc,he,hmid,h1,h2⟩ :=
    gst_shared_x4_binary_factorS A D Z W C hA hD hClt hW hshared
  have hc1 : c = 1 := by
    rcases hC with hC2 | hC3 <;> rw [hC2] at hCe <;> try rw [hC3] at hCe <;> omega
  subst c
  refine ⟨a,b,e,Wmid,hDb,?_,ha,hb,he,hmid,?_,h2⟩
  · omega
  · simpa using h1
