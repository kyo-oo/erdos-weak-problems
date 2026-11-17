import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerExponentTritObstruction

open GSTFourPowerDirectResidue

/-- Low ternary prefix of the exponent below scale `3^p`. -/
def exponentPrefix (K p : Nat) : Nat := K % 3^p

/-- The `p`-th ternary trit of the exponent. -/
def exponentTrit (K p : Nat) : Nat := K / 3^p % 3

/-- Exact base-three decomposition of an exponent into low prefix, current
trit, and the remaining higher suffix. -/
theorem exponent_prefix_trit_decomposition (K p : Nat) :
    K = exponentPrefix K p
      + exponentTrit K p * 3^p
      + 3^(p+1) * ((K / 3^p) / 3) := by
  unfold exponentPrefix exponentTrit
  calc
    K = K % 3^p + 3^p * (K / 3^p) :=
      (Nat.mod_add_div K (3^p)).symm
    _ = K % 3^p
        + 3^p * ((K / 3^p) % 3 + 3 * ((K / 3^p) / 3)) := by
          rw [Nat.mod_add_div (K / 3^p) 3]
    _ = K % 3^p
        + (K / 3^p % 3) * 3^p
        + 3^(p+1) * ((K / 3^p) / 3) := by
          rw [Nat.pow_succ]
          ring

/-- A common higher exponent suffix is invisible at row `p+1`; the current
exponent trit shifts both consecutive-power digits by exactly the same amount.
This is the direct ternary-tree transition rule. -/
theorem pow4_shared_trit_pair
    (p m a u : Nat) (ha : a < 3) :
    let K := m + a * 3^p + 3^(p+1) * u
    digit3 (4^K) (p+1) =
        (digit3 (4^m) (p+1) + a) % 3
      ∧
    digit3 (4^(K+1)) (p+1) =
        (digit3 (4^(m+1)) (p+1) + a) % 3 := by
  dsimp
  constructor
  · calc
      digit3 (4^(m + a * 3^p + 3^(p+1) * u)) (p+1)
          = digit3 (4^(m + a * 3^p)) (p+1) := by
              simpa [Nat.add_assoc] using
                pow4_digit_period (p+1) (m + a * 3^p) u
      _ = (digit3 (4^m) (p+1) + a) % 3 :=
        pow4_exponent_trit_lift_digit p m a ha
  · have hshape :
        (m + a * 3^p + 3^(p+1) * u) + 1
          = (m+1) + a * 3^p + 3^(p+1) * u := by
        omega
    rw [hshape]
    calc
      digit3 (4^((m+1) + a * 3^p + 3^(p+1) * u)) (p+1)
          = digit3 (4^((m+1) + a * 3^p)) (p+1) := by
              simpa [Nat.add_assoc] using
                pow4_digit_period (p+1) ((m+1) + a * 3^p) u
      _ = (digit3 (4^(m+1)) (p+1) + a) % 3 :=
        pow4_exponent_trit_lift_digit p (m+1) a ha

/-- Exact pair formula for the actual exponent `K`: the `p`-th ternary trit
shifts both low-prefix row values by the same amount. -/
theorem pow4_pair_from_exponent_trit (K p : Nat) :
    digit3 (4^K) (p+1) =
        (digit3 (4^(exponentPrefix K p)) (p+1) + exponentTrit K p) % 3
      ∧
    digit3 (4^(K+1)) (p+1) =
        (digit3 (4^((exponentPrefix K p)+1)) (p+1) + exponentTrit K p) % 3 := by
  let m := exponentPrefix K p
  let a := exponentTrit K p
  let u := (K / 3^p) / 3
  have ha : a < 3 := by
    dsimp [a, exponentTrit]
    exact Nat.mod_lt _ (by decide)
  have hK : K = m + a * 3^p + 3^(p+1) * u := by
    simpa [m, a, u] using exponent_prefix_trit_decomposition K p
  have hp := pow4_shared_trit_pair p m a u ha
  constructor
  · calc
      digit3 (4^K) (p+1)
          = digit3 (4^(m + a * 3^p + 3^(p+1) * u)) (p+1) := by rw [hK]
      _ = (digit3 (4^m) (p+1) + a) % 3 := hp.1
      _ = (digit3 (4^(exponentPrefix K p)) (p+1) + exponentTrit K p) % 3 := by
            simp [m, a]
  · calc
      digit3 (4^(K+1)) (p+1)
          = digit3 (4^((m + a * 3^p + 3^(p+1) * u)+1)) (p+1) := by rw [hK]
      _ = (digit3 (4^(m+1)) (p+1) + a) % 3 := hp.2
      _ = (digit3 (4^((exponentPrefix K p)+1)) (p+1) + exponentTrit K p) % 3 := by
            simp [m, a]

/-- For three-valued digits/trits, two equally shifted values are both `2`
exactly when the base values agree and the shift is the unique killing trit. -/
theorem shifted_pair_eq_two_iff
    (d0 d1 a : Nat) (hd0 : d0 < 3) (hd1 : d1 < 3) (ha : a < 3) :
    ((d0 + a) % 3 = 2 ∧ (d1 + a) % 3 = 2) ↔
      (d0 = d1 ∧ a = 2 - d0) := by
  interval_cases d0 <;> interval_cases d1 <;> interval_cases a <;> norm_num

/-- Exact direct normal form for a common digit-two row.  Row `p+1` is common
iff the two low-prefix row values agree and the actual `p`-th ternary trit of
`K` is the unique killing trit.  This is an equivalence, not merely an
obstruction. -/
theorem row_common_two_iff_prefix_killing_trit (K p : Nat) :
    (digit3 (4^K) (p+1) = 2 ∧ digit3 (4^(K+1)) (p+1) = 2) ↔
      (digit3 (4^(exponentPrefix K p)) (p+1) =
          digit3 (4^((exponentPrefix K p)+1)) (p+1) ∧
       exponentTrit K p =
          2 - digit3 (4^(exponentPrefix K p)) (p+1)) := by
  have hd0 : digit3 (4^(exponentPrefix K p)) (p+1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  have hd1 : digit3 (4^((exponentPrefix K p)+1)) (p+1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  have ha : exponentTrit K p < 3 := by
    unfold exponentTrit
    exact Nat.mod_lt _ (by decide)
  have hp := pow4_pair_from_exponent_trit K p
  rw [hp.1, hp.2]
  exact shifted_pair_eq_two_iff
    (digit3 (4^(exponentPrefix K p)) (p+1))
    (digit3 (4^((exponentPrefix K p)+1)) (p+1))
    (exponentTrit K p) hd0 hd1 ha

/-- Exact row formula in terms of the actual `p`-th ternary trit of `K`. -/
theorem pow4_digit_from_exponent_trit (K p : Nat) :
    digit3 (4^K) (p+1) =
      (digit3 (4^(exponentPrefix K p)) (p+1)
        + exponentTrit K p) % 3 := by
  exact (pow4_pair_from_exponent_trit K p).1

/-- If the two low-prefix row values agree, there is a canonical exponent trit
that makes both consecutive powers equal to digit `2` at row `p+1`.
The killing trit is exactly `2 - d`. -/
theorem equal_prefix_pair_has_killing_trit
    (p m u : Nat)
    (heq : digit3 (4^m) (p+1) = digit3 (4^(m+1)) (p+1)) :
    let d := digit3 (4^m) (p+1)
    let a := 2 - d
    a < 3 ∧
      digit3 (4^(m + a * 3^p + 3^(p+1) * u)) (p+1) = 2 ∧
      digit3 (4^((m + a * 3^p + 3^(p+1) * u)+1)) (p+1) = 2 := by
  dsimp
  have hd : digit3 (4^m) (p+1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  let a := 2 - digit3 (4^m) (p+1)
  have ha : a < 3 := by
    dsimp [a]
    omega
  have hsum : digit3 (4^m) (p+1) + a = 2 := by
    dsimp [a]
    omega
  have hp := pow4_shared_trit_pair p m a u ha
  refine ⟨ha, ?_, ?_⟩
  · calc
      digit3 (4^(m + a * 3^p + 3^(p+1) * u)) (p+1)
          = (digit3 (4^m) (p+1) + a) % 3 := hp.1
      _ = 2 := by simp [hsum]
  · calc
      digit3 (4^((m + a * 3^p + 3^(p+1) * u)+1)) (p+1)
          = (digit3 (4^(m+1)) (p+1) + a) % 3 := hp.2
      _ = (digit3 (4^m) (p+1) + a) % 3 := by rw [← heq]
      _ = 2 := by simp [hsum]

/-- Parametric direct obstruction on every ternary exponent trit.

If `K` has no common digit-two row, and the two low-prefix row values agree,
then the actual `p`-th ternary trit of `K` cannot be the unique killing trit
`2 - d`.  This is a recursive restriction on the ternary expansion of `K`
itself; it contains no inherited witness or relocation hypothesis. -/
theorem no_common_two_exponent_trit_obstruction
    (K p : Nat)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      digit3 (4^K) q = 2 ∧ digit3 (4^(K+1)) q = 2)
    (heq :
      digit3 (4^(exponentPrefix K p)) (p+1) =
      digit3 (4^((exponentPrefix K p)+1)) (p+1)) :
    exponentTrit K p ≠
      2 - digit3 (4^(exponentPrefix K p)) (p+1) := by
  intro hkill
  have hrow := (row_common_two_iff_prefix_killing_trit K p).2 ⟨heq, hkill⟩
  apply hNo
  exact ⟨p+1, by omega, hrow.1, hrow.2⟩

#check exponentPrefix
#check exponentTrit
#check exponent_prefix_trit_decomposition
#check pow4_shared_trit_pair
#check pow4_pair_from_exponent_trit
#check shifted_pair_eq_two_iff
#check row_common_two_iff_prefix_killing_trit
#check pow4_digit_from_exponent_trit
#check equal_prefix_pair_has_killing_trit
#check no_common_two_exponent_trit_obstruction
#print axioms exponent_prefix_trit_decomposition
#print axioms pow4_shared_trit_pair
#print axioms pow4_pair_from_exponent_trit
#print axioms shifted_pair_eq_two_iff
#print axioms row_common_two_iff_prefix_killing_trit
#print axioms pow4_digit_from_exponent_trit
#print axioms equal_prefix_pair_has_killing_trit
#print axioms no_common_two_exponent_trit_obstruction

end GSTFourPowerExponentTritObstruction
