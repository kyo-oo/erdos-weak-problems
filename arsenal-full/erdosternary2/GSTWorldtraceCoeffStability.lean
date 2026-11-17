import GSTCanonicalTailLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Unconditional stabilization of GST Worldtrace LTE coefficients

The coefficient c_s from 4^(3^s)=1+3^(s+1)*c_s stabilizes on
every fixed finite ternary band as the scale s increases. This
identifies the exact finite truncations of the GST worldtrace limit
without postulating any convergence axiom.
-/

namespace GSTWorldtraceCoeffStability

open GSTCanonicalTailLTE

/-- The exact cubic recurrence, with both nonlinear corrections explicit. -/
theorem coeff_step (s : Nat) :
    lteCoeff (s+1) =
      lteCoeff s +
        3^(s+1)*((lteCoeff s)^2+3^s*(lteCoeff s)^3) := by
  have hp : 3^(2*s+1)=3^(s+1)*3^s := by
    rw [show 2*s+1=(s+1)+s by omega, pow_add]
  simp only [lteCoeff]
  rw [hp]
  ring

/-- The GST tower coefficient is unchanged modulo its own next cut. -/
theorem coeff_step_mod (s : Nat) :
    lteCoeff (s+1) % 3^(s+1) = lteCoeff s % 3^(s+1) := by
  rw [coeff_step, Nat.add_mul_mod_self_left]

/-- From scale 17 upward the first eighteen coefficient digits are fixed. -/
theorem coeff_step_mod18 (s : Nat) (hs : 17 ≤ s) :
    lteCoeff (s+1) % 3^18 = lteCoeff s % 3^18 := by
  have hdiv : 3^18 ∣ 3^(s+1) := Nat.pow_dvd_pow 3 (by omega)
  calc
    lteCoeff (s+1) % 3^18 =
      (lteCoeff (s+1) % 3^(s+1)) % 3^18 :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
    _ = (lteCoeff s % 3^(s+1)) % 3^18 := by rw [coeff_step_mod]
    _ = lteCoeff s % 3^18 := Nat.mod_mod_of_dvd _ hdiv

/-- Uniform, scale-unbounded stabilization on the 18-trit band. -/
theorem coeff_mod18_stable (s : Nat) (hs : 17 ≤ s) :
    lteCoeff s % 3^18 = lteCoeff 17 % 3^18 := by
  have hbase : ∀ k : Nat,
      lteCoeff (17+k) % 3^18 = lteCoeff 17 % 3^18 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [show 17+(k+1) = (17+k)+1 by omega]
        exact (coeff_step_mod18 (17+k) (by omega)).trans ih
  rw [show s=17+(s-17) by omega]
  exact hbase (s-17)

#print axioms coeff_step
#print axioms coeff_step_mod
#print axioms coeff_mod18_stable

end GSTWorldtraceCoeffStability
