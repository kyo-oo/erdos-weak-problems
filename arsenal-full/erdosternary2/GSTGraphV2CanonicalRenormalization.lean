import GSTGraphV2SeededPrefix
import GSTPrefixOneSeedCore

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2CanonicalRenormalization

open GSTPerfectPowerTailNavigation
open GSTPrefixOneSeedCore

/-- The quotient left after removing the least canonical ternary phase. -/
def phaseOffset (r a : Nat) : Nat :=
  canonicalTail r a / 3

/-- Exact product recurrence before splitting the leading canonical trit. -/
theorem canonicalTail_block_recurrence
    (r a m : Nat) :
    canonicalTail r (a + 3*m) =
      canonicalTail r a +
        3 * 4^(a * 3^r) * canonicalTail (r+1) m := by
  let P : Nat := 3^(r+1)
  let A : Nat := 4^(3^r * a)
  let Qa : Nat := canonicalTail r a
  let Qm : Nat := canonicalTail (r+1) m
  let Q : Nat := canonicalTail r (a + 3*m)

  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hExp :
      3^r * (a + 3*m) =
        3^r * a + 3^(r+1) * m := by
    rw [Nat.pow_succ]
    ring
  have hProduct :
      4^(3^r * (a + 3*m)) =
        A * 4^(3^(r+1) * m) := by
    rw [hExp, Nat.pow_add]
  have hA :
      A = 1 + P * Qa := by
    dsimp [A, P, Qa]
    simpa using canonical_tail_decomposition r a
  have hM :
      4^(3^(r+1) * m) =
        1 + 3 * P * Qm := by
    have h := canonical_tail_decomposition (r+1) m
    rw [show (r+1)+1 = r+2 by omega] at h
    have hpow : 3^(r+2) = 3 * P := by
      dsimp [P]
      rw [show r+2 = (r+1)+1 by omega, Nat.pow_succ]
      ring
    rw [hpow] at h
    simpa [Qm, Nat.mul_assoc] using h
  have hShape :
      4^(3^r * (a + 3*m)) =
        1 + P * (Qa + 3 * A * Qm) := by
    rw [hProduct, hM, hA]
    ring
  have hCanonical :
      4^(3^r * (a + 3*m)) =
        1 + P * Q := by
    dsimp [P, Q]
    exact canonical_tail_decomposition r (a + 3*m)
  have hEq :
      1 + P * Q =
        1 + P * (Qa + 3 * A * Qm) :=
    hCanonical.symm.trans hShape
  have hEqInt := congrArg (fun x : Nat => (x : Int)) hEq
  push_cast at hEqInt
  have hPInt : (0 : Int) < (P : Int) := by
    exact_mod_cast hP
  have hResultInt :
      (Q : Int) = (Qa + 3 * A * Qm : Nat) := by
    push_cast
    nlinarith
  have hResult : Q = Qa + 3 * A * Qm := by
    exact_mod_cast hResultInt
  simpa [Q, Qa, A, Qm, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hResult


/-- Exact arbitrary-cutoff canonical recurrence.  Removing `K` origin trits
retains the complete low canonical prefix and identifies the live upper packet
with the next canonical scale. -/
theorem canonicalTail_power_block_recurrence
    (r a m K : Nat) :
    canonicalTail r (a + 3^K * m) =
      canonicalTail r a +
        3^K * 4^(a * 3^r) * canonicalTail (r+K) m := by
  let P : Nat := 3^(r+1)
  let A : Nat := 4^(3^r * a)
  let Qa : Nat := canonicalTail r a
  let Qm : Nat := canonicalTail (r+K) m
  let Q : Nat := canonicalTail r (a + 3^K * m)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have hExp :
      3^r * (a + 3^K * m) =
        3^r * a + 3^(r+K) * m := by
    rw [show 3^(r+K) = 3^r * 3^K by rw [pow_add]]
    ring
  have hProduct :
      4^(3^r * (a + 3^K * m)) =
        A * 4^(3^(r+K) * m) := by
    rw [hExp, Nat.pow_add]
  have hA :
      A = 1 + P * Qa := by
    dsimp [A, P, Qa]
    simpa using canonical_tail_decomposition r a
  have hScale :
      3^((r+K)+1) = P * 3^K := by
    dsimp [P]
    rw [← Nat.pow_add]
    congr 1
    omega
  have hM :
      4^(3^(r+K) * m) =
        1 + P * 3^K * Qm := by
    have h := canonical_tail_decomposition (r+K) m
    rw [hScale] at h
    simpa [Qm, Nat.mul_assoc] using h
  have hShape :
      4^(3^r * (a + 3^K * m)) =
        1 + P * (Qa + 3^K * A * Qm) := by
    rw [hProduct, hM, hA]
    ring
  have hCanonical :
      4^(3^r * (a + 3^K * m)) =
        1 + P * Q := by
    dsimp [P, Q]
    exact canonical_tail_decomposition r (a + 3^K * m)
  have hEq :
      1 + P * Q =
        1 + P * (Qa + 3^K * A * Qm) :=
    hCanonical.symm.trans hShape
  have hEqInt := congrArg (fun x : Nat => (x : Int)) hEq
  push_cast at hEqInt
  have hPInt : (0 : Int) < (P : Int) := by
    exact_mod_cast hP
  have hResultInt :
      (Q : Int) = (Qa + 3^K * A * Qm : Nat) := by
    push_cast
    nlinarith
  have hResult : Q = Qa + 3^K * A * Qm := by
    exact_mod_cast hResultInt
  simpa [Q, Qa, A, Qm, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hResult

/-- Zero-prefix specialization of the arbitrary-cutoff recurrence. -/
theorem canonicalTail_zero_power_strip
    (r m K : Nat) :
    canonicalTail r (3^K * m) =
      3^K * canonicalTail (r+K) m := by
  have h := canonicalTail_power_block_recurrence r 0 m K
  have hden : 1 < 3^(r+1) := by
    rw [Nat.pow_succ]
    have hp : 0 < 3^r := by positivity
    nlinarith
  simpa [canonicalTail, Nat.div_eq_of_lt hden] using h

/-- The two-unit canonical tail is an exact square expansion. -/
theorem canonicalTail_two_exact (r : Nat) :
    canonicalTail r 2 =
      2 * canonicalTail r 1 +
        3^(r+1) * canonicalTail r 1 * canonicalTail r 1 := by
  let P : Nat := 3^(r+1)
  let Q1 : Nat := canonicalTail r 1
  let Q2 : Nat := canonicalTail r 2
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have h1 :
      4^(3^r) = 1 + P * Q1 := by
    dsimp [P, Q1]
    simpa using canonical_tail_decomposition r 1
  have h2 :
      4^(3^r * 2) = 1 + P * Q2 := by
    dsimp [P, Q2]
    exact canonical_tail_decomposition r 2
  have hpow :
      4^(3^r * 2) = 4^(3^r) * 4^(3^r) := by
    rw [show 3^r * 2 = 3^r + 3^r by ring, Nat.pow_add]
  have hEq :
      1 + P * Q2 =
        (1 + P * Q1) * (1 + P * Q1) := by
    rw [← h2, hpow, h1]
  have hEqInt := congrArg (fun x : Nat => (x : Int)) hEq
  push_cast at hEqInt
  have hPInt : (0 : Int) < (P : Int) := by
    exact_mod_cast hP
  have hResultInt :
      (Q2 : Int) =
        (2 * Q1 + P * Q1 * Q1 : Nat) := by
    push_cast
    nlinarith
  have hResult : Q2 = 2 * Q1 + P * Q1 * Q1 := by
    exact_mod_cast hResultInt
  simpa [Q2, Q1, P] using hResult

/-- The canonical phase quotient exposes precisely its leading phase modulo 3. -/
theorem canonicalTail_mod_three
    (r a : Nat) (ha : a < 3) :
    canonicalTail r a % 3 = a := by
  have haCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases haCases with rfl | rfl | rfl
  · have hden : 1 < 3^(r+1) := by
      rw [Nat.pow_succ]
      have hp : 0 < 3^r := by positivity
      nlinarith
    simp [canonicalTail, Nat.div_eq_of_lt hden]
  · simpa [unitTail] using unitTail_mod3_one r
  · rw [canonicalTail_two_exact]
    rw [show canonicalTail r 1 = unitTail r by rfl]
    rw [unitTail_prefix_one]
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_succ]

/-- Exact all-three-phase canonical renormalization. -/
theorem canonicalTail_three_adic_strip
    (r a m : Nat) (ha : a < 3) :
    canonicalTail r (a + 3*m) =
      a + 3 *
        (phaseOffset r a +
          4^(a * 3^r) * canonicalTail (r+1) m) := by
  have hRec := canonicalTail_block_recurrence r a m
  have hSplit := (Nat.mod_add_div (canonicalTail r a) 3).symm
  rw [canonicalTail_mod_three r a ha] at hSplit
  rw [hRec, hSplit]
  unfold phaseOffset
  ring

/-- Zero-phase specialization of canonical renormalization. -/
theorem canonicalTail_zero_strip
    (r m : Nat) :
    canonicalTail r (3*m) =
      3 * canonicalTail (r+1) m := by
  have h := canonicalTail_three_adic_strip r 0 m (by decide)
  have hden : 1 < 3^(r+1) := by
    rw [Nat.pow_succ]
    have hp : 0 < 3^r := by positivity
    nlinarith
  simpa [phaseOffset, canonicalTail, Nat.div_eq_of_lt hden] using h

/-- Prefix-one specialization, definitionally aligned with the existing core. -/
theorem canonicalTail_one_strip
    (r m : Nat) :
    canonicalTail r (1 + 3*m) =
      1 + 3 *
        (prefixOffset r +
          4^(3^r) * canonicalTail (r+1) m) := by
  exact prefix_one_tail_shape r m

#check canonicalTail_block_recurrence
#check canonicalTail_power_block_recurrence
#check canonicalTail_zero_power_strip
#check canonicalTail_mod_three
#check canonicalTail_three_adic_strip
#check canonicalTail_zero_strip
#check canonicalTail_one_strip
#print axioms canonicalTail_three_adic_strip

end GSTGraphV2CanonicalRenormalization
