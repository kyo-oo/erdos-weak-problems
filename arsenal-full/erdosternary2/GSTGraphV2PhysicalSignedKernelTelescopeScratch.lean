import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTPhysicalKernel

/-!
# Physical binary-column telescope for the handwritten signed kernel

This is a standalone arithmetic layer.  It does not identify any alternate
coordinate with a physical GST phase and it does not assert the final Erdos
crossing theorem.

Fix an ordinary natural `R` and ternary row `p`.  The `r`-th physical binary
column is `2^r * R`.  Consecutive columns are therefore literal x2/base3 bridge
cells.  The signed 7/(J-6) kernel can consequently be telescoped along these
actual columns, not an abstract re-coordinate orbit.
-/

def binaryColumnDigit (R p r : Nat) : Nat :=
  (2^r * R) / 3^p % 3

def binaryColumnCarry (R p r : Nat) : Nat :=
  (2 * ((2^r * R) % 3^p)) / 3^p

def microOutput (a d : Nat) : Nat := (a + 2*d) % 3

def twoIndicator (d : Nat) : Int := if d = 2 then 1 else 0

def signedKernelTwice (a d : Nat) : Int :=
  14 * (twoIndicator (microOutput a d) - twoIndicator d) +
  7 * twoIndicator d * twoIndicator (microOutput a d)

/-- The physical binary carry is one bit. -/
theorem binaryColumnCarry_lt_two
    (R p r : Nat) : binaryColumnCarry R p r < 2 := by
  unfold binaryColumnCarry
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hr : (2^r * R) % 3^p < 3^p := Nat.mod_lt _ hp
  have hmul : 2 * ((2^r * R) % 3^p) < 3^p * 2 := by
    omega
  exact Nat.div_lt_of_lt_mul hmul

/-- Every physical binary-column digit is ternary. -/
theorem binaryColumnDigit_lt_three
    (R p r : Nat) : binaryColumnDigit R p r < 3 := by
  unfold binaryColumnDigit
  exact Nat.mod_lt _ (by decide)

/-- Exact quotient decomposition for one literal multiply-by-two step. -/
theorem binary_mul_two_quotient_decomposition
    (X p : Nat) :
    (2*X) / 3^p =
      (2 * (X % 3^p)) / 3^p + 2 * (X / 3^p) := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : X = 3^p * (X / 3^p) + X % 3^p :=
    (Nat.div_add_mod X (3^p)).symm
  calc
    (2*X) / 3^p =
        (2 * (3^p * (X / 3^p) + X % 3^p)) / 3^p := by rw [← hsplit]
    _ = (2 * (X % 3^p) + 3^p * (2 * (X / 3^p))) / 3^p := by
      congr 1
      rw [Nat.mul_add]
      ac_rfl
    _ = (2 * (X % 3^p)) / 3^p + 2 * (X / 3^p) := by
      rw [Nat.add_mul_div_left _ _ hp]

/-- The microscopic bridge output is exactly the next physical binary-column
ternary digit. -/
theorem microOutput_eq_next_binaryColumnDigit
    (R p r : Nat) :
    microOutput (binaryColumnCarry R p r) (binaryColumnDigit R p r) =
      binaryColumnDigit R p (r+1) := by
  unfold microOutput binaryColumnCarry binaryColumnDigit
  have hpow : 2^(r+1) * R = 2 * (2^r * R) := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [hpow, binary_mul_two_quotient_decomposition (2^r * R) p]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- The exact signed-kernel identity on one physical binary column. -/
theorem signedKernelTwice_physical_column
    (R p r : Nat) :
    signedKernelTwice (binaryColumnCarry R p r) (binaryColumnDigit R p r) =
      14 * (twoIndicator (binaryColumnDigit R p (r+1)) -
            twoIndicator (binaryColumnDigit R p r)) +
      7 * twoIndicator (binaryColumnDigit R p r) *
          twoIndicator (binaryColumnDigit R p (r+1)) := by
  unfold signedKernelTwice
  rw [microOutput_eq_next_binaryColumnDigit]

/-- Exact physical telescope over `L` consecutive x2 columns.

The CREATE/DESTROY part collapses to the BIG2 endpoint difference.  Every
interior non-boundary contribution is the positive SURVIVE residual
`7 * I₂(d_r) * I₂(d_{r+1})`.
-/
theorem signedKernelTwice_physical_telescope
    (R p L : Nat) :
    Finset.sum (Finset.range L)
      (fun r => signedKernelTwice
        (binaryColumnCarry R p r) (binaryColumnDigit R p r)) =
      14 * (twoIndicator (binaryColumnDigit R p L) -
            twoIndicator (binaryColumnDigit R p 0)) +
      7 * Finset.sum (Finset.range L)
        (fun r => twoIndicator (binaryColumnDigit R p r) *
          twoIndicator (binaryColumnDigit R p (r+1))) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, signedKernelTwice_physical_column, ih,
          Finset.sum_range_succ]
      ring

/-- If no physical x2 SURVIVE occurs in the first `L` binary columns, the whole
signed kernel is pure boundary flux. -/
theorem signedKernelTwice_eq_boundary_of_no_survive
    (R p L : Nat)
    (hno : ∀ r, r < L →
      ¬ (binaryColumnDigit R p r = 2 ∧
         binaryColumnDigit R p (r+1) = 2)) :
    Finset.sum (Finset.range L)
      (fun r => signedKernelTwice
        (binaryColumnCarry R p r) (binaryColumnDigit R p r)) =
      14 * (twoIndicator (binaryColumnDigit R p L) -
            twoIndicator (binaryColumnDigit R p 0)) := by
  rw [signedKernelTwice_physical_telescope]
  have hzero :
      Finset.sum (Finset.range L)
        (fun r => twoIndicator (binaryColumnDigit R p r) *
          twoIndicator (binaryColumnDigit R p (r+1))) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hrL : r < L := Finset.mem_range.mp hr
    have hn := hno r hrL
    by_cases h0 : binaryColumnDigit R p r = 2
    · have h1 : binaryColumnDigit R p (r+1) ≠ 2 := by
        intro h1
        exact hn ⟨h0, h1⟩
      simp [twoIndicator, h0, h1]
    · simp [twoIndicator, h0]
  rw [hzero]
  ring

end GSTPhysicalKernel
