import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Low-digit extraction from the shared trap word. -/
theorem gst_trap_low_digit_exactS
    (N D Z W C : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hEq : D + 4*Z = W + 4^N*C) :
    W % 4 = D := by
  have hpow : 4^N = 4 * 4^(N-1) := by
    calc
      4^N = 4^((N-1)+1) := by congr 1 <;> omega
      _ = 4^(N-1) * 4 := by rw [Nat.pow_succ]
      _ = 4 * 4^(N-1) := by ac_rfl
  have hhigh : (4^N*C) % 4 = 0 := by
    rw [hpow]
    simp [Nat.mul_assoc]
  have hleft : (D + 4*Z) % 4 = D := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hD]
  have hright : (W + 4^N*C) % 4 = W % 4 := by
    rw [Nat.add_mod, hhigh, Nat.add_zero, Nat.mod_mod]
  rw [hEq] at hleft
  rw [hright] at hleft
  exact hleft

/-- Therefore W has the exact form D+4*w. -/
theorem gst_trap_high_remainder_splitS
    (N D Z W C : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hEq : D + 4*Z = W + 4^N*C) :
    W = D + 4*(W/4) := by
  have hmod := gst_trap_low_digit_exactS N D Z W C hN hD hEq
  have hsplit : W = 4*(W/4) + W%4 :=
    (Nat.div_add_mod W 4).symm
  rw [hmod] at hsplit
  omega

/-- Removing the common low digit gives one-column horizontal descent of Z. -/
theorem gst_trap_width_peel_quotientS
    (N D Z W C : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hEq : D + 4*Z = W + 4^N*C) :
    Z = W/4 + 4^(N-1)*C := by
  have hW := gst_trap_high_remainder_splitS N D Z W C hN hD hEq
  have hpow : 4^N = 4 * 4^(N-1) := by
    calc
      4^N = 4^((N-1)+1) := by congr 1 <;> omega
      _ = 4^(N-1) * 4 := by rw [Nat.pow_succ]
      _ = 4 * 4^(N-1) := by ac_rfl
  have hEq' :
      D + 4*Z = (D + 4*(W/4)) + (4 * 4^(N-1))*C := by
    calc
      D + 4*Z = W + 4^N*C := hEq
      _ = (D + 4*(W/4)) + 4^N*C := by
        exact congrArg (fun x : Nat => x + 4^N*C) hW
      _ = (D + 4*(W/4)) + (4 * 4^(N-1))*C := by
        exact congrArg (fun x : Nat => (D + 4*(W/4)) + x*C) hpow
  have hfactored :
      D + 4*Z = D + 4*(W/4 + 4^(N-1)*C) := by
    calc
      D + 4*Z = (D + 4*(W/4)) + (4 * 4^(N-1))*C := hEq'
      _ = D + 4*(W/4 + 4^(N-1)*C) := by ring
  have hmul : 4*Z = 4*(W/4 + 4^(N-1)*C) :=
    Nat.add_left_cancel hfactored
  omega

/-- The full trapped parent tail after the cut can therefore be rewritten with one fewer x4 column. -/
theorem gst_trap_width_peel_tailS
    (N D Z W C Y : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hEq : D + 4*Z = W + 4^N*C) :
    Z + 4^N*Y =
      W/4 + 4^(N-1) * (C + 4*Y) := by
  rw [gst_trap_width_peel_quotientS N D Z W C hN hD hEq]
  have hpow : 4^N = 4^(N-1) * 4 := by
    calc
      4^N = 4^((N-1)+1) := by congr 1 <;> omega
      _ = 4^(N-1) * 4 := by rw [Nat.pow_succ]
  rw [hpow]
  ring

/-- If W was strictly inside the old interval, its peeled remainder is inside the new interval. -/
theorem gst_trap_width_peel_remainder_boundS
    (N W : Nat)
    (hN : 1 ≤ N)
    (hW : W < 4^N) :
    W/4 < 4^(N-1) := by
  have hpow : 4^N = 4^(N-1) * 4 := by
    calc
      4^N = 4^((N-1)+1) := by congr 1 <;> omega
      _ = 4^(N-1) * 4 := by rw [Nat.pow_succ]
  rw [hpow] at hW
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).2 (by
    simpa [Nat.mul_comm] using hW)

/-- Packaged one-step arithmetic width descent. -/
theorem gst_trap_width_peel_packageS
    (N D Z W C Y : Nat)
    (hN : 1 ≤ N)
    (hD : D < 4)
    (hW : W < 4^N)
    (hEq : D + 4*Z = W + 4^N*C) :
    let w := W/4
    let X := C + 4*Y
    w < 4^(N-1) ∧
      Z = w + 4^(N-1)*C ∧
      Z + 4^N*Y = w + 4^(N-1)*X := by
  dsimp only
  exact ⟨gst_trap_width_peel_remainder_boundS N W hN hW,
    gst_trap_width_peel_quotientS N D Z W C hN hD hEq,
    gst_trap_width_peel_tailS N D Z W C Y hN hD hEq⟩