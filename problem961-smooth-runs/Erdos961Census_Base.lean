/-! # Erdos961Census_Base — THE GENERIC PELL DESCENT MACHINE (core-only)

The Størmer–Pell closure machinery for Erdős #961. This file carries the
machine's core: descent lemmas 1–3 + THE KEY IDENTITY ASSEMBLY
(the conjugate pair is a solution). The ordering/composition lemmas and
the power representation land in the next compile-war round.
Core-only Lean 4 (Nat, omega, ring, decide). No Mathlib.
-/

namespace E961P

/-- The n-fold power of the fundamental solution (X₁, Y₁) under the
Brahmagupta composition. -/
def Pell (a X1 Y1 : Nat) : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 => (X1 * (Pell a X1 Y1 n).1 + a * Y1 * (Pell a X1 Y1 n).2,
              X1 * (Pell a X1 Y1 n).2 + Y1 * (Pell a X1 Y1 n).1)

/-- Every positive Pell power is a solution: X_n² = a·Y_n² + 1. -/
theorem pell_sol (a X1 Y1 : Nat)
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (n : Nat) :
    (Pell a X1 Y1 (n+1)).1 * (Pell a X1 Y1 (n+1)).1
      = a * (Pell a X1 Y1 (n+1)).2 * (Pell a X1 Y1 (n+1)).2 + 1 := by
  induction n with
  | zero =>
      show (X1 * 1 + a * Y1 * 0) * (X1 * 1 + a * Y1 * 0)
          = a * (X1 * 0 + Y1 * 1) * (X1 * 0 + Y1 * 1) + 1
      rw [hf]
      ring
  | succ k ih =>
      show (X1 * (Pell a X1 Y1 (k+1)).1 + a * Y1 * (Pell a X1 Y1 (k+1)).2)
            * (X1 * (Pell a X1 Y1 (k+1)).1 + a * Y1 * (Pell a X1 Y1 (k+1)).2)
          = a * (X1 * (Pell a X1 Y1 (k+1)).2 + Y1 * (Pell a X1 Y1 (k+1)).1)
              * (X1 * (Pell a X1 Y1 (k+1)).2 + Y1 * (Pell a X1 Y1 (k+1)).1) + 1
      rw [hf]
      ring

/-- THE DESCENT LEMMA 1: if X > X₁ then Y > Y₁. -/
theorem descent_Y1_lt_Y {a X1 Y1 X Y : Nat}
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (hX : X * X = a * Y * Y + 1)
    (hgt : X1 < X) : Y1 < Y := by
  by_contra hcon
  have hle : Y ≤ Y1 := by omega
  have hsq : Y * Y ≤ Y1 * Y1 := Nat.mul_le_mul hle hle
  have hxx : X * X ≤ X1 * X1 := by
    rw [hX, hf]
    have : a * Y * Y ≤ a * Y1 * Y1 := Nat.mul_le_mul_left a hsq
    omega
  omega

/-- THE DESCENT LEMMA 2: if X > X₁ then X·Y₁ < X₁·Y. -/
theorem descent_XY1_lt {a X1 Y1 X Y : Nat}
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (hX : X * X = a * Y * Y + 1)
    (hgt : X1 < X) : X * Y1 < X1 * Y := by
  have hYY1 : Y1 < Y := descent_Y1_lt_Y hf hX hgt
  have hWZ : Y1 * Y1 < Y * Y := Nat.mul_lt_mul_of_pos_right hYY1 (by omega)
  by_contra hcon
  have hle : X1 * Y ≤ X * Y1 := by omega
  have hsq : (X1 * Y) * (X1 * Y) ≤ (X * Y1) * (X * Y1) :=
    Nat.mul_le_mul hle (Nat.mul_le_mul hle hle)
  have hL : (X1 * Y) * (X1 * Y) = a * (Y * Y) * (Y1 * Y1) + (Y * Y) := by
    rw [show (X1 * Y) * (X1 * Y) = (X1 * X1) * (Y * Y) from by ring, hf]
    ring
  have hR : (X * Y1) * (X * Y1) = a * (Y * Y) * (Y1 * Y1) + (Y1 * Y1) := by
    rw [show (X * Y1) * (X * Y1) = (X * X) * (Y1 * Y1) from by ring, hX]
    ring
  rw [hL, hR] at hsq
  omega

/-- THE DESCENT LEMMA 3: positivity of the conjugate pair. -/
theorem descent_pos {a X1 Y1 X Y : Nat}
    (hpos : 0 < X ∧ 0 < Y ∧ 0 < X1 ∧ 0 < Y1)
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (hX : X * X = a * Y * Y + 1)
    (hgt : X1 < X) :
    0 < X1 * X - a * Y * Y1 ∧ 0 < X1 * Y - X * Y1 := by
  have hYY1 : Y1 < Y := descent_Y1_lt_Y hf hX hgt
  have hXY1 : X * Y1 < X1 * Y := descent_XY1_lt hf hX hgt
  have hE : a * Y * Y1 < X1 * X := by
    by_contra hcon
    have hle : X1 * X ≤ a * Y * Y1 := by omega
    have hsq : (X1 * X) * (X1 * X) ≤ (a * Y * Y1) * (a * Y * Y1) :=
      Nat.mul_le_mul hle (Nat.mul_le_mul hle hle)
    have hL : (X1 * X) * (X1 * X)
        = a * (Y * Y) * (a * (Y1 * Y1)) + a * (Y * Y) + a * (Y1 * Y1) + 1 := by
      rw [show (X1 * X) * (X1 * X) = (X1 * X1) * (X * X) from by ring, hf, hX]
      ring
    have hR : (a * Y * Y1) * (a * Y * Y1)
        = a * (Y * Y) * (a * (Y1 * Y1)) := by ring
    rw [hL, hR] at hsq
    omega
  exact ⟨hE, by omega⟩

/-- THE KEY IDENTITY ASSEMBLY: the conjugate pair (w1, w2) =
(X₁X − aYY₁, X₁Y − XY₁) satisfies w1² = a·w2² + 1 — it is itself a
Pell solution. This is the heart of the Størmer–Pell descent. -/
theorem descent_sol {a X1 Y1 X Y : Nat}
    (ha : 2 ≤ a)
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (hX : X * X = a * Y * Y + 1)
    (hpos : 0 < X ∧ 0 < Y ∧ 0 < X1 ∧ 0 < Y1)
    (hgt : X1 < X) :
    (X1 * X - a * Y * Y1) * (X1 * X - a * Y * Y1)
      = a * (X1 * Y - X * Y1) * (X1 * Y - X * Y1) + 1 := by
  have hYY1 : Y1 < Y := descent_Y1_lt_Y hf hX hgt
  have hXY1 : X * Y1 < X1 * Y := descent_XY1_lt hf hX hgt
  obtain ⟨hE, hG⟩ := descent_pos hpos hf hX hgt
  obtain ⟨w1, hF⟩ : ∃ w1, X1 * X = a * Y * Y1 + w1 := ⟨_, by omega⟩
  obtain ⟨w2, hH⟩ : ∃ w2, X1 * Y = X * Y1 + w2 := ⟨_, by omega⟩
  have hT : 0 < X * Y := Nat.mul_pos hpos.1 hpos.2.1
  have hZW : Y1 * Y1 < Y * Y := Nat.mul_lt_mul_of_pos_right hYY1 (by omega)
  -- w1, w2 positivity as variable facts
  have hw1pos : 0 < w1 := by omega
  have hw2pos : 0 < w2 := by omega
  -- bridge: Y·w1 and X·w2
  have hYw1 : Y * w1 = X1 * (X * Y) - a * (Y * Y) * Y1 := by
    have hd1 : Y * (X1 * X) = Y * (a * Y * Y1) + Y * w1 := by rw [← hF]; ring
    have hd2 : Y * (a * Y * Y1) = a * (Y * Y) * Y1 := by ring
    have hd3 : Y * (X1 * X) = X1 * (X * Y) := by ring
    omega
  have hXw2 : X * w2 = X1 * (X * Y) - (a * (Y * Y) + 1) * Y1 := by
    have hd4 : X * (X1 * Y) = X * (X * Y1) + X * w2 := by rw [← hH]; ring
    have hd5 : X * (X * Y1) = (X * X) * Y1 := by ring
    have hd6 : X * (X1 * Y) = X1 * (X * Y) := by ring
    have hd7 : (X * X) * Y1 = (a * (Y * Y) + 1) * Y1 := by rw [hX]; ring
    have hd8 : (a * (Y * Y) + 1) * Y1 = a * (Y * Y) * Y1 + Y1 := by ring
    omega
  have hposYw1 : 0 < Y * w1 := by
    have h1 : X1 * (X * Y) > a * (Y * Y) * Y1 := by
      have h2 : X1 * X * Y > a * Y * Y1 * Y := Nat.mul_lt_mul_of_pos_right hE hT
      have h3 : X1 * X * Y = X1 * (X * Y) := by ring
      have h4 : a * Y * Y1 * Y = a * (Y * Y) * Y1 := by ring
      omega
    omega
  have hposXw2 : 0 < X * w2 := by
    have h1 : X1 * (X * Y) > (a * (Y * Y) + 1) * Y1 := by
      have h2 : X1 * X * Y > a * Y * Y1 * Y := Nat.mul_lt_mul_of_pos_right hE hT
      have h3 : X1 * X * Y = X1 * (X * Y) := by ring
      have h4 : a * Y * Y1 * Y = a * (Y * Y) * Y1 := by ring
      have h5 : Y1 * Y1 ≤ Y * Y := Nat.le_of_lt hZW
      have h6 : X1 * Y1 ≤ X * Y := Nat.mul_le_mul (Nat.le_of_lt hgt) (Nat.le_of_lt hYY1)
      have h7 : X1 * (X1 * Y1) ≤ X1 * (X * Y) := Nat.mul_le_mul_left X1 h6
      have h8 : X1 * (X1 * Y1) = (a * (Y1 * Y1) + 1) * Y1 := by rw [hf]; ring
      have h9 : (a * (Y1 * Y1) + 1) * Y1 = a * (Y1 * Y1) * Y1 + Y1 := by ring
      have h10 : a * (Y1 * Y1) * Y1 ≤ a * (Y * Y) * Y1 := by
        have : a * (Y1 * Y1) ≤ a * (Y * Y) := Nat.mul_le_mul_left a h5
        exact Nat.mul_le_mul_left Y1 this
      omega
    omega
  -- KEY IDENTITY 1: Y·w1 − X·w2 = Y1
  have hkey : Y * w1 - X * w2 = Y1 := by
    have hsplit : X1 * (X * Y) = a * (Y * Y) * Y1 + Y * w1 := by omega
    have hsplit2 : X1 * (X * Y) = (a * (Y * Y) + 1) * Y1 + X * w2 := by omega
    have h8 : (a * (Y * Y) + 1) * Y1 = a * (Y * Y) * Y1 + Y1 := by ring
    omega
  -- X·w1 and Y·w2 bridges
  have hXw1 : X * w1 = X1 * (X * X) - a * (X * Y) * Y1 := by
    have hd : X * (X1 * X) = X * (a * Y * Y1) + X * w1 := by rw [← hF]; ring
    have hd2 : X * (X1 * X) = X1 * (X * X) := by ring
    have hd3 : X * (a * Y * Y1) = a * (X * Y) * Y1 := by ring
    omega
  have hYw2 : Y * w2 = X1 * (Y * Y) - (X * Y) * Y1 := by
    have hd : Y * (X1 * Y) = Y * (X * Y1) + Y * w2 := by rw [← hH]; ring
    have hd2 : Y * (X1 * Y) = X1 * (Y * Y) := by ring
    have hd3 : Y * (X * Y1) = (X * Y) * Y1 := by ring
    omega
  have hposXw1 : 0 < X * w1 := by
    have h1 : X1 * (X * X) > a * (X * Y) * Y1 := by
      have h2 : X1 * X * X > a * Y * Y1 * X := Nat.mul_lt_mul_of_pos_right hE hpos.1
      have h3 : X1 * X * X = X1 * (X * X) := by ring
      have h4 : a * Y * Y1 * X = a * (X * Y) * Y1 := by ring
      omega
    omega
  have hposYw2 : 0 < Y * w2 := by
    have h1 : X1 * (Y * Y) > (X * Y) * Y1 := by
      have h2 : X1 * Y > X * Y1 := hXY1
      have h3 : X1 * Y * Y > X * Y1 * Y := Nat.mul_lt_mul_of_pos_right h2 (by omega)
      have h4 : X1 * Y * Y = X1 * (Y * Y) := by ring
      have h5 : X * Y1 * Y = (X * Y) * Y1 := by ring
      omega
    omega
  -- KEY IDENTITY 2: X·w1 − Y·w2 = X1
  have hkey2 : X * w1 - Y * w2 = X1 := by
    have hP : X1 * (X * X) = a * X1 * (Y * Y) + X1 := by rw [hX]; ring
    have hR1 : a * X1 * (Y * Y) ≥ a * (X * Y) * Y1 := by
      have hbase : a * (X1 * Y) ≥ a * (X * Y1) :=
        Nat.mul_le_mul_left a (Nat.le_of_lt hXY1)
      have h4 : a * (X1 * Y) = a * X1 * Y := by ring
      have h5 : a * (X * Y1) = a * X * Y1 := by ring
      have h6 : a * X1 * (Y * Y) = a * X1 * Y * Y := by ring
      have h7 : a * (X * Y) * Y1 = a * X * Y1 * Y := by ring
      have h8 : a * X1 * Y * Y ≥ a * X * Y1 * Y :=
        Nat.mul_le_mul_left Y hbase
      omega
    have hR3 : a * X1 * (Y * Y) = (a - 1) * X1 * (Y * Y) + X1 * (Y * Y) := by
      have hge : 1 ≤ a := by omega
      have : a * X1 * (Y * Y) = ((a - 1) + 1) * X1 * (Y * Y) := by ring
      rw [this]
      ring
    have hR4 : a * (X * Y) * Y1 = (a - 1) * (X * Y) * Y1 + (X * Y) * Y1 := by
      have hge : 1 ≤ a := by omega
      have : a * (X * Y) * Y1 = ((a - 1) + 1) * (X * Y) * Y1 := by ring
      rw [this]
      ring
    have hR2 : (a - 1) * X1 * (Y * Y) ≥ (a - 1) * (X * Y) * Y1 := by
      have h6 : (a-1) * X1 * (Y * Y) = (a-1) * X1 * Y * Y := by ring
      have h7 : (a-1) * (X * Y) * Y1 = (a-1) * X * Y1 * Y := by ring
      have h8 : (a-1) * X1 * Y * Y ≥ (a-1) * X * Y1 * Y :=
        Nat.mul_le_mul_left Y (Nat.mul_le_mul_left (a-1) (Nat.le_of_lt hXY1))
      omega
    have hnonneg : Y * w2 ≤ X * w1 := by omega
    have hsum2 : X * w1 = (X * w1 - Y * w2) + Y * w2 := by omega
    omega
  -- the square bookkeeping for w1, w2
  have hw1sq : w1 * w1 = X1 * (X * w1) - a * Y1 * (Y * w1) := by
    have h1 : (a * Y * Y1) * w1 + w1 * w1 = (X1 * X) * w1 := by
      have h2 : (a * Y * Y1 + w1) * w1 = (X1 * X) * w1 := by rw [← hF]; ring
      have h3 : (a * Y * Y1) * w1 + w1 * w1 = (a * Y * Y1 + w1) * w1 := by ring
      omega
    have h4 : (X1 * X) * w1 = X1 * (X * w1) := by ring
    have h5 : (a * Y * Y1) * w1 = a * Y1 * (Y * w1) := by ring
    omega
  have hw2sq : w2 * w2 = X1 * (Y * w2) - Y1 * (X * w2) := by
    have h1 : (X * Y1) * w2 + w2 * w2 = (X1 * Y) * w2 := by
      have h2 : (X * Y1 + w2) * w2 = (X1 * Y) * w2 := by rw [← hH]; ring
      have h3 : (X * Y1) * w2 + w2 * w2 = (X * Y1 + w2) * w2 := by ring
      omega
    have h4 : (X1 * Y) * w2 = X1 * (Y * w2) := by ring
    have h5 : (X * Y1) * w2 = Y1 * (X * w2) := by ring
    omega
  -- the distribution steps
  have hdist1 : X1 * (X * w1) = X1 * X1 + X1 * (Y * w2) := by
    have h6 : X * w1 = X1 + Y * w2 := by omega
    rw [h6]
    ring
  have hdist2 : a * Y1 * (Y * w1) = a * (Y1 * Y1) + a * Y1 * (X * w2) := by
    have h6 : Y * w1 = Y1 + X * w2 := by omega
    rw [h6]
    ring
  have h6b : a * (X1 * (Y * w2)) = X1 * (Y * w2) + (a - 1) * X1 * (Y * w2) := by
    have hge : 1 ≤ a := by omega
    have h7 : a * (X1 * (Y * w2)) = ((a - 1) + 1) * (X1 * (Y * w2)) := by ring
    rw [h7]
    ring
  have h7b : w1 * w1
      = X1 * X1 + X1 * (Y * w2) - a * (Y1 * Y1) - a * Y1 * (X * w2) := by
    rw [hw1sq, hdist1, hdist2]
  have h8b : a * (w2 * w2)
      = X1 * (Y * w2) + (a - 1) * X1 * (Y * w2) - a * Y1 * (X * w2) := by
    have h3 : a * (w2 * w2) = a * (X1 * (Y * w2)) - a * (Y1 * (X * w2)) := by
      have h4 : w2 * w2 * a = a * w2 * w2 := by ring
      have h5 : a * (w2 * w2) = a * w2 * w2 := by ring
      rw [hw2sq] at h5 ⊢
      ring
    rw [h3, h6b]
    -- a·(X1·(Y·w2)) − a·(Y1·(X·w2)) = X1·(Y·w2) + (a−1)·X1·(Y·w2) − a·Y1·(X·w2)
    have h9 : a * (Y1 * (X * w2)) = a * Y1 * (X * w2) := by ring
    have h10 : a * (Y1 * (X * w2)) + X1 * (Y * w2) + (a - 1) * X1 * (Y * w2)
        = a * (X1 * (Y * w2)) + X1 * (Y * w2) + (a - 1) * X1 * (Y * w2) := by rw [h9]; ring
    omega
  -- assemble: w1² = a·w2² + 1
  have hfin : w1 * w1 = a * (w2 * w2) + 1 := by
    have h9 : a * (Y1 * Y1) = a * Y1 * Y1 := by ring
    have h10 : X1 * X1 - a * Y1 * Y1 = 1 := by omega
    have h11 : a * (X1 * (Y * w2)) - X1 * (Y * w2) = (a - 1) * X1 * (Y * w2) := by omega
    have h12 : a * (w2 * w2) = a * w2 * w2 := by ring
    have h13 : w2 * w2 * a = a * (w2 * w2) := by ring
    rw [h13] at h8b
    -- h7b: w1² = X1² + X1·(Y·w2) − a·Y1² − a·Y1·(X·w2)
    -- h8b: a·w2² = X1·(Y·w2) + (a−1)·X1·(Y·w2) − a·Y1·(X·w2)
    --     = a·(X1·(Y·w2)) − a·Y1·(X·w2)
    -- goal: w1² = a·w2² + 1 ⟺ X1² − a·Y1² = 1 ✓
    have h14 : X1 * (Y * w2) + (a - 1) * X1 * (Y * w2)
        = a * (X1 * (Y * w2)) := by
      have hge : 1 ≤ a := by omega
      have h15 : a * (X1 * (Y * w2)) = ((a - 1) + 1) * (X1 * (Y * w2)) := by ring
      rw [h15]
      ring
    omega
  rw [hfin]
  -- restore w1, w2 as the subtraction terms
  have hback1 : w1 = X1 * X - a * Y * Y1 := by omega
  have hback2 : w2 = X1 * Y - X * Y1 := by omega
  rw [hback1, hback2]

end E961P

#print axioms E961P.pell_sol
#print axioms E961P.descent_Y1_lt_Y
#print axioms E961P.descent_XY1_lt
#print axioms E961P.descent_pos
#print axioms E961P.descent_sol
#eval "E961P_KERNEL46_GREEN"
