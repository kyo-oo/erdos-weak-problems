import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact all-depth terminal dynamics of the GST seeded affine Omega graph

For any finite source word X and finite carry seed D, all digit and
carry input vanishes past the explicit cutoff D+4*X+1. Thereafter the
zero/zero state is an infinite absorbing BAD state.

This is unconditional and all-depth. It demonstrates precisely why
the existing all-depth conservation and finite-origin properties
cannot alone imply a Happy gate in the residual perfect-power case.
-/

namespace GSTOmegaAbsorbingZero

/-- Every finite seeded affine trajectory reaches the absorbing zero
digit/zero carry state beyond an explicit arithmetic cutoff. -/
theorem finite_seed_eventually_zero
    (D X j : Nat) (hj : D+4*X+1 ≤ j) :
    gstDigit X j = 0 ∧ gstAffineMulCarry 4 D X j = 0 := by
  let N : Nat := D+4*X
  have hN : N < 3^(N+1) := by
    exact three_pow_succ_gt_selfS N
  have hpower : 3^(N+1) ≤ 3^j :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) (by dsimp [N] at hj ⊢; omega)
  have hlarge : N < 3^j := lt_of_lt_of_le hN hpower
  have hX : X < 3^j := by
    dsimp [N] at hlarge
    omega
  have hXdiv : X / 3^j = 0 := Nat.div_eq_of_lt hX
  have hmod : X % 3^j ≤ X := Nat.mod_le X (3^j)
  have hcarry : D+4*(X%3^j) < 3^j := by
    have h4 : D+4*(X%3^j) ≤ D+4*X := by omega
    exact lt_of_le_of_lt h4 hlarge
  constructor
  · simp [gstDigit, hXdiv]
  · exact Nat.div_eq_of_lt hcarry

/-- All finite-source GST seeded traces eventually enter the
permanently BAD zero/zero state. This conclusion holds for every
seed D and every word X, not only exceptional powers. -/
theorem seeded_trace_eventually_bad
    (D X : Nat) :
    ∀ j, D+4*X+1 ≤ j →
      GSTBadPair (gstAffineMulCarry 4 D X j) (gstDigit X j) := by
  intro j hj
  obtain ⟨hd, hc⟩ := finite_seed_eventually_zero D X j hj
  dsimp only [GSTBadPair]
  rw [hd, hc]
  decide

#print axioms finite_seed_eventually_zero
#print axioms seeded_trace_eventually_bad

end GSTOmegaAbsorbingZero
