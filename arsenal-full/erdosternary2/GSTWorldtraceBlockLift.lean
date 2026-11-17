import GSTCanonicalTailLTE
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST / Worldtrace whole-block linear lift

For U | T, U > 1 and T > 0, the first entire U-block of the quotient
by T evolves LINEARLY as the exponent b varies:

  (A * (1 + T*c)^b / T) mod U = (A/T + b*c*A) mod U.

This is not a bounded experiment or a hypothesis. The proof is by exact
quotient recurrence, and its period input is only U | T. It retains
the physical source A, including its lower-prefix carry state.
-/

namespace GSTWorldtraceBlockLift

/-- An exact quotient recurrence; no power expansion or discarded carry. -/
theorem quotient_multiply_step
    (P T c : Nat) (hT : 0 < T) :
    (P * (1 + T*c)) / T = P/T + c*P := by
  have hshape : P * (1+T*c) = P + T*(c*P) := by ring
  rw [hshape, Nat.add_mul_div_left _ _ hT]

/-- The whole quotient block evolves linearly when the modulus divides
the scale. This is the GST affine carrier identity on a finite band. -/
theorem quotient_block_lift
    (A c b T U : Nat) (hT : 0 < T) (hU : 1 < U)
    (hUT : U ∣ T) :
    (A * (1+T*c)^b / T) % U =
      (A/T + b*c*A) % U := by
  have hTzero : T % U = 0 := Nat.mod_eq_zero_of_dvd hUT
  have hunit : (1+T*c) % U = 1 := by
    simp [Nat.add_mod, Nat.mul_mod, hTzero, Nat.mod_eq_of_lt hU]
  have hpower (n : Nat) : (1+T*c)^n % U = 1 := by
    rw [Nat.pow_mod, hunit]
    simp [Nat.mod_eq_of_lt hU]
  have hcarrier (n : Nat) :
      (A*(1+T*c)^n) % U = A % U := by
    simp [Nat.mul_mod, hpower, Nat.mod_mod]
  induction b with
  | zero =>
      simp
  | succ b ih =>
      let P := A * (1+T*c)^b
      have hshape :
          A*(1+T*c)^(b+1) = P*(1+T*c) := by
        simp only [P, pow_succ]
        ring
      have hind : (P/T)%U = (A/T+b*c*A)%U := ih
      have hmul : (c*P)%U = (c*A)%U := by
        calc
          (c*P)%U = ((c%U)*(P%U))%U := Nat.mul_mod c P U
          _ = ((c%U)*(A%U))%U := by rw [show P%U=A%U from hcarrier b]
          _ = (c*A)%U := (Nat.mul_mod c A U).symm
      have hsum :
          (P/T+c*P)%U = ((A/T+b*c*A)+c*A)%U := by
        calc
          (P/T+c*P)%U = (((P/T)%U)+((c*P)%U))%U :=
            Nat.add_mod (P/T) (c*P) U
          _ = (((A/T+b*c*A)%U)+((c*A)%U))%U := by rw [hind, hmul]
          _ = ((A/T+b*c*A)+c*A)%U :=
            (Nat.add_mod (A/T+b*c*A) (c*A) U).symm
      calc
        (A*(1+T*c)^(b+1)/T)%U = (P/T+c*P)%U := by
          rw [hshape, quotient_multiply_step P T c hT]
        _ = ((A/T+b*c*A)+c*A)%U := hsum
        _ = (A/T+(b+1)*c*A)%U := by congr 1; ring

/-- Worldtrace whole-block exponent transport, from the exact LTE coefficient:
simultaneously controls the w consecutive trits starting at position t+1.
The permissible band is 1 <= w <= t+1. -/
theorem pow4_whole_block_lift
    (M b t w : Nat) (hw : 1 ≤ w) (hband : w ≤ t+1) :
    (4^(M+b*3^t) / 3^(t+1)) % 3^w =
      (4^M / 3^(t+1) + b * GSTCanonicalTailLTE.lteCoeff t * 4^M) % 3^w := by
  have hU : 1 < 3^w := by
    have he : 3^1 ≤ 3^w :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hw
    norm_num at he
    omega
  have hUT : 3^w ∣ 3^(t+1) := by
    refine ⟨3^(t+1-w), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  have hp : 4^(M+b*3^t) =
      4^M * (1+3^(t+1)*GSTCanonicalTailLTE.lteCoeff t)^b := by
    rw [show M+b*3^t = M+3^t*b by ac_rfl, pow_add, pow_mul,
      GSTCanonicalTailLTE.pow4_three_power_lte_exact t]
  rw [hp]
  exact quotient_block_lift (4^M) (GSTCanonicalTailLTE.lteCoeff t)
    b (3^(t+1)) (3^w) (by positivity) hU hUT

#print axioms quotient_multiply_step
#print axioms quotient_block_lift
#print axioms pow4_whole_block_lift

end GSTWorldtraceBlockLift
