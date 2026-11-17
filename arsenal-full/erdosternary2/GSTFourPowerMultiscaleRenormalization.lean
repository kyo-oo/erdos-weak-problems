import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerMultiscaleRenormalization

open GSTFourPowerDirectResidue

/-- Normalized affine coordinate at ternary exponent scale `3^m`.

`scaleOrbit m q` is defined without division.  The theorem below proves the
exact identity
`4^(3^m*q) = 1 + 3^(m+1) * scaleOrbit m q`. -/
def scaleOrbit (m : Nat) : Nat → Nat
  | 0 => 0
  | q+1 => 4^(3^m) * scaleOrbit m q + lteCoeff m

/-- Exact multiscale renormalization identity. -/
theorem scaleOrbit_exact (m : Nat) : ∀ q : Nat,
    4^(3^m * q) = 1 + 3^(m+1) * scaleOrbit m q
  | 0 => by simp [scaleOrbit]
  | q+1 => by
      have ih := scaleOrbit_exact m q
      have hbase := pow4_three_power_lte_exact m
      calc
        4^(3^m * (q+1)) = 4^(3^m*q) * 4^(3^m) := by
          rw [Nat.mul_succ, Nat.pow_add]
        _ = (1 + 3^(m+1) * scaleOrbit m q) *
              (1 + 3^(m+1) * lteCoeff m) := by rw [ih, hbase]
        _ = 1 + 3^(m+1) *
              ((1 + 3^(m+1) * lteCoeff m) * scaleOrbit m q +
                lteCoeff m) := by ring
        _ = 1 + 3^(m+1) *
              (4^(3^m) * scaleOrbit m q + lteCoeff m) := by rw [hbase]
        _ = 1 + 3^(m+1) * scaleOrbit m (q+1) := by rfl

/-- Every multiscale coefficient is a 3-adic unit, so the normalized orbit
    records the current exponent trit literally. -/
theorem scaleOrbit_mod_three (m : Nat) : ∀ q : Nat,
    scaleOrbit m q % 3 = q % 3
  | 0 => by simp [scaleOrbit]
  | q+1 => by
      have ih := scaleOrbit_mod_three m q
      simp only [scaleOrbit]
      rw [Nat.add_mod, Nat.mul_mod, pow4_mod3_one, lteCoeff_mod3_one, ih]
      simp [Nat.succ_eq_add_one, Nat.add_mod]

/-- Exact cross-scale conjugacy.  Consuming one ternary exponent digit and
    increasing the renormalization depth commute literally. -/
theorem scaleOrbit_three_mul (m q : Nat) :
    scaleOrbit m (3*q) = 3 * scaleOrbit (m+1) q := by
  have hexp : 3^m * (3*q) = 3^(m+1) * q := by
    rw [Nat.pow_succ]
    ring
  have hEq :
      1 + 3^(m+1) * scaleOrbit m (3*q) =
        1 + 3^((m+1)+1) * scaleOrbit (m+1) q := by
    calc
      1 + 3^(m+1) * scaleOrbit m (3*q)
          = 4^(3^m * (3*q)) := (scaleOrbit_exact m (3*q)).symm
      _ = 4^(3^(m+1) * q) := by rw [hexp]
      _ = 1 + 3^((m+1)+1) * scaleOrbit (m+1) q :=
        scaleOrbit_exact (m+1) q
  have hmul :
      3^(m+1) * scaleOrbit m (3*q) =
        3^((m+1)+1) * scaleOrbit (m+1) q := by
    exact Nat.add_left_cancel hEq
  have hmul' :
      3^(m+1) * scaleOrbit m (3*q) =
        3^(m+1) * (3 * scaleOrbit (m+1) q) := by
    simpa [Nat.pow_succ, Nat.mul_assoc] using hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 3^(m+1)) hmul'

/-- At scale zero the normalized orbit is the familiar recurrence
    `Y(0)=0`, `Y(q+1)=4Y(q)+1`. -/
theorem scaleOrbit_zero_succ (q : Nat) :
    scaleOrbit 0 (q+1) = 4 * scaleOrbit 0 q + 1 := by
  simp [scaleOrbit, lteCoeff]

/-- At scale one the renormalized orbit is exactly the base-64 affine system
    discovered by peeling one ternary exponent digit. -/
theorem scaleOrbit_one_succ (q : Nat) :
    scaleOrbit 1 (q+1) = 64 * scaleOrbit 1 q + 7 := by
  norm_num [scaleOrbit, lteCoeff]

/-- The scale coefficient itself is the first nonzero orbit point. -/
theorem scaleOrbit_one_point (m : Nat) :
    scaleOrbit m 1 = lteCoeff m := by
  simp [scaleOrbit]

/-- Exact block law: advancing the coarse exponent by `q` multiplies the
    original power by a canonical `3^(m+1)`-resolved affine factor. -/
theorem coarse_power_factorization (m q : Nat) :
    4^(3^m*q) = 1 + 3^(m+1) * scaleOrbit m q :=
  scaleOrbit_exact m q

#check scaleOrbit_exact
#check scaleOrbit_mod_three
#check scaleOrbit_three_mul
#check scaleOrbit_zero_succ
#check scaleOrbit_one_succ
#print axioms scaleOrbit_exact
#print axioms scaleOrbit_mod_three
#print axioms scaleOrbit_three_mul

end GSTFourPowerMultiscaleRenormalization
