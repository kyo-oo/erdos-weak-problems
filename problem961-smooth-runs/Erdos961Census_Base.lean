import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

/-! # Erdos961Census_Base — THE GENERIC PELL DESCENT MACHINE (core-only)

The Størmer–Pell closure machinery for Erdős #961. Round 1 of the census
kernel: the Brahmagupta composition law (pell_compose), every Pell power
is a solution (pell_sol), the descent ordering lemmas (descent_Y1_lt_Y,
descent_XY1_lt), conjugate positivity (descent_pos), and THE KEY IDENTITY
ASSEMBLY: the conjugate pair (w1, w2) = (X₁X − a·Y·Y₁, X₁Y − XY₁) is
itself a Pell solution (descent_sol), via the CORRECTED linear keys

  Y·w1 = Y1 + X·w2   and   X·w1 = X1 + a·Y·w2

(the second key is the corrected form: the naive X·w1 − Y·w2 = X1 fails
already at a = 2 with (X₁,Y₁) = (3,2), (X,Y) = (17,12): X·w1 − Y·w2 =
27 ≠ 3; the truth is X·w1 = 51 = 3 + 2·24 = X1 + a·Y·w2).

Round-1 fixes vs the failed Kernel 46 r1 run (43236139767):
(1) the file now imports the Arsenal header (the green Erdos961.lean
    import set) — the r1 file had NO imports, so ring/by_contra were
    unknown tactics in the bare Init environment;
(2) pell_sol's `rw [hf]` misfires are gone: the zero case normalizes
    with core simp lemmas and closes by `exact hf`; the succ case is
    the standalone composition lemma pell_compose;
(3) the strict square-monotonicity gaps are closed by the omega-safe
    (X1+1)² = X1² + 2·X1 + 1 trick;
(4) the descent assembly is rebuilt on the corrected second key.

Core-only Lean 4 (Nat, omega, ring, decide). No Mathlib.
-/

namespace E961P

/-- The n-fold power of the fundamental solution (X₁, Y₁) under the
Brahmagupta composition. -/
def Pell (a X1 Y1 : Nat) : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 => (X1 * (Pell a X1 Y1 n).1 + a * Y1 * (Pell a X1 Y1 n).2,
              X1 * (Pell a X1 Y1 n).2 + Y1 * (Pell a X1 Y1 n).1)

/-- THE BRAHMAGUPTA COMPOSITION LAW: the composition of two Pell
solutions is a solution — (X₁·Xk + a·Y₁·Yk)² = a·(X₁·Yk + Y₁·Xk)² + 1.
The Lagrange identity underneath: u² − a·v² = (X₁² − a·Y₁²)(Xk² − a·Yk²). -/
theorem pell_compose {a X1 Y1 Xk Yk : Nat}
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (hik : Xk * Xk = a * Yk * Yk + 1) :
    (X1 * Xk + a * Y1 * Yk) * (X1 * Xk + a * Y1 * Yk)
      = a * (X1 * Yk + Y1 * Xk) * (X1 * Yk + Y1 * Xk) + 1 := by
  have key : (X1 * Xk + a * Y1 * Yk) * (X1 * Xk + a * Y1 * Yk)
      + a * (X1 * X1) * (Yk * Yk) + a * (Y1 * Y1) * (Xk * Xk)
      = a * (X1 * Yk + Y1 * Xk) * (X1 * Yk + Y1 * Xk)
        + (X1 * X1) * (Xk * Xk) + a * a * (Y1 * Y1) * (Yk * Yk) := by
    ring
  have hP : (X1 * X1) * (Xk * Xk)
      = a * a * (Y1 * Y1) * (Yk * Yk) + a * (Y1 * Y1) + a * (Yk * Yk) + 1 := by
    rw [hf, hik]
    ring
  have mA : a * (X1 * X1) * (Yk * Yk)
      = a * a * (Y1 * Y1) * (Yk * Yk) + a * (Yk * Yk) := by
    rw [hf]
    ring
  have mB : a * (Y1 * Y1) * (Xk * Xk)
      = a * a * (Y1 * Y1) * (Yk * Yk) + a * (Y1 * Y1) := by
    rw [hik]
    ring
  omega

/-- Every positive Pell power is a solution: X_n² = a·Y_n² + 1. -/
theorem pell_sol (a X1 Y1 : Nat)
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (n : Nat) :
    (Pell a X1 Y1 (n+1)).1 * (Pell a X1 Y1 (n+1)).1
      = a * (Pell a X1 Y1 (n+1)).2 * (Pell a X1 Y1 (n+1)).2 + 1 := by
  induction n with
  | zero =>
      show (X1 * 1 + a * Y1 * 0) * (X1 * 1 + a * Y1 * 0)
          = a * (X1 * 0 + Y1 * 1) * (X1 * 0 + Y1 * 1) + 1
      simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      exact hf
  | succ k ih =>
      show (X1 * (Pell a X1 Y1 (k+1)).1 + a * Y1 * (Pell a X1 Y1 (k+1)).2)
            * (X1 * (Pell a X1 Y1 (k+1)).1 + a * Y1 * (Pell a X1 Y1 (k+1)).2)
          = a * (X1 * (Pell a X1 Y1 (k+1)).2 + Y1 * (Pell a X1 Y1 (k+1)).1)
              * (X1 * (Pell a X1 Y1 (k+1)).2 + Y1 * (Pell a X1 Y1 (k+1)).1) + 1
      exact pell_compose hf ih

/-- THE DESCENT LEMMA 1: if X > X₁ then Y > Y₁. -/
theorem descent_Y1_lt_Y {a X1 Y1 X Y : Nat}
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (hX : X * X = a * Y * Y + 1)
    (hgt : X1 < X) : Y1 < Y := by
  by_contra hcon
  have hle : Y ≤ Y1 := by omega
  have hsq : Y * Y ≤ Y1 * Y1 := Nat.mul_le_mul hle hle
  have hxx : X * X ≤ X1 * X1 := by
    rw [hX, hf]
    have h : a * (Y * Y) ≤ a * (Y1 * Y1) := Nat.mul_le_mul_left a hsq
    have h2 : a * Y * Y = a * (Y * Y) := by ring
    have h3 : a * Y1 * Y1 = a * (Y1 * Y1) := by ring
    omega
  have hmono : (X1 + 1) * (X1 + 1) ≤ X * X :=
    Nat.mul_le_mul (by omega) (by omega)
  have hexp : (X1 + 1) * (X1 + 1) = X1 * X1 + 2 * X1 + 1 := by ring
  omega

/-- THE DESCENT LEMMA 2: if X > X₁ then X·Y₁ < X₁·Y. -/
theorem descent_XY1_lt {a X1 Y1 X Y : Nat}
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (hX : X * X = a * Y * Y + 1)
    (hgt : X1 < X) : X * Y1 < X1 * Y := by
  by_contra hcon
  have hle : X1 * Y ≤ X * Y1 := by omega
  have hsq : (X1 * Y) * (X1 * Y) ≤ (X * Y1) * (X * Y1) :=
    Nat.mul_le_mul hle hle
  have hL : (X1 * Y) * (X1 * Y) = a * (Y * Y) * (Y1 * Y1) + (Y * Y) := by
    rw [show (X1 * Y) * (X1 * Y) = (X1 * X1) * (Y * Y) from by ring, hf]
    ring
  have hR : (X * Y1) * (X * Y1) = a * (Y * Y) * (Y1 * Y1) + (Y1 * Y1) := by
    rw [show (X * Y1) * (X * Y1) = (X * X) * (Y1 * Y1) from by ring, hX]
    ring
  rw [hL, hR] at hsq
  have hYY1 : Y1 < Y := descent_Y1_lt_Y hf hX hgt
  have hmono : (Y1 + 1) * (Y1 + 1) ≤ Y * Y :=
    Nat.mul_le_mul (by omega) (by omega)
  have hexp : (Y1 + 1) * (Y1 + 1) = Y1 * Y1 + 2 * Y1 + 1 := by ring
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
      Nat.mul_le_mul hle hle
    have hL : (X1 * X) * (X1 * X)
        = a * (Y * Y) * (a * (Y1 * Y1)) + a * (Y * Y) + a * (Y1 * Y1) + 1 := by
      rw [show (X1 * X) * (X1 * X) = (X1 * X1) * (X * X) from by ring, hf, hX]
      ring
    have hR : (a * Y * Y1) * (a * Y * Y1) = a * (Y * Y) * (a * (Y1 * Y1)) := by
      ring
    rw [hL, hR] at hsq
    omega
  exact ⟨by omega, by omega⟩

/-- THE KEY IDENTITY ASSEMBLY: the conjugate pair (w1, w2) =
(X₁X − a·Y·Y₁, X₁Y − XY₁) satisfies w1² = a·w2² + 1 — it is itself a
Pell solution. This is the heart of the Størmer–Pell descent, built on
the two linear keys

  Y·w1 = Y1 + X·w2   and   X·w1 = X1 + a·Y·w2,

each derived by pure-ring folding, with the final square bookkeeping a
linear system over eight product atoms. -/
theorem descent_sol {a X1 Y1 X Y : Nat}
    (ha : 2 ≤ a)
    (hf : X1 * X1 = a * Y1 * Y1 + 1) (hX : X * X = a * Y * Y + 1)
    (hpos : 0 < X ∧ 0 < Y ∧ 0 < X1 ∧ 0 < Y1) (hgt : X1 < X) :
    (X1 * X - a * Y * Y1) * (X1 * X - a * Y * Y1)
      = a * (X1 * Y - X * Y1) * (X1 * Y - X * Y1) + 1 := by
  have hYY1 : Y1 < Y := descent_Y1_lt_Y hf hX hgt
  have hXY1 : X * Y1 < X1 * Y := descent_XY1_lt hf hX hgt
  obtain ⟨hE, hG⟩ := descent_pos hpos hf hX hgt
  obtain ⟨w1, hF⟩ : ∃ w1, X1 * X = a * Y * Y1 + w1 :=
    ⟨X1 * X - a * Y * Y1, by omega⟩
  obtain ⟨w2, hH⟩ : ∃ w2, X1 * Y = X * Y1 + w2 :=
    ⟨X1 * Y - X * Y1, by omega⟩
  have hw1 : w1 = X1 * X - a * Y * Y1 := by omega
  have hw2 : w2 = X1 * Y - X * Y1 := by omega
  rw [← hw1, ← hw2]
  -- KEY 1: Y·w1 = Y1 + X·w2
  have f1 : Y * (a * Y * Y1 + w1) = Y * (a * Y * Y1) + Y * w1 := by ring
  rw [← hF] at f1
  have f2 : Y * (X1 * X) = X1 * (X * Y) := by ring
  have f3 : Y * (a * Y * Y1) = a * (Y * Y) * Y1 := by ring
  have kYw1 : X1 * (X * Y) = a * (Y * Y) * Y1 + Y * w1 := by omega
  have g1 : X * (X * Y1 + w2) = X * (X * Y1) + X * w2 := by ring
  rw [← hH] at g1
  have g2 : X * (X1 * Y) = X1 * (X * Y) := by ring
  have g3 : X * (X * Y1) = (X * X) * Y1 := by ring
  have g4 : (X * X) * Y1 = (a * (Y * Y) + 1) * Y1 := by
    rw [hX]
    ring
  have g5 : (a * (Y * Y) + 1) * Y1 = a * (Y * Y) * Y1 + Y1 := by ring
  have k1 : Y * w1 = Y1 + X * w2 := by omega
  -- KEY 2 (corrected): X·w1 = X1 + a·Y·w2
  have p1 : X * (a * Y * Y1 + w1) = X * (a * Y * Y1) + X * w1 := by ring
  rw [← hF] at p1
  have p2 : X * (X1 * X) = X1 * (X * X) := by ring
  have p3 : X * (a * Y * Y1) = a * Y * (X * Y1) := by ring
  have p4 : X1 * (X * X) = X1 * (a * Y * Y + 1) := by rw [hX]
  have p5 : X1 * (a * Y * Y + 1) = a * Y * (X1 * Y) + X1 := by ring
  have p6 : a * Y * (X * Y1 + w2) = a * Y * (X * Y1) + a * Y * w2 := by ring
  rw [← hH] at p6
  have k2 : X * w1 = X1 + a * Y * w2 := by omega
  -- the square bookkeeping (all linear over the product atoms):
  have sq1 : a * (Y * Y1) * w1 + w1 * w1 = (X1 * X) * w1 := by
    have q1 : (a * Y * Y1 + w1) * w1 = a * (Y * Y1) * w1 + w1 * w1 := by ring
    rw [← hF] at q1
    exact q1.symm
  have sq2 : (X * Y1) * w2 + w2 * w2 = (X1 * Y) * w2 := by
    have q2 : (X * Y1 + w2) * w2 = (X * Y1) * w2 + w2 * w2 := by ring
    rw [← hH] at q2
    exact q2.symm
  have e1 : (X1 * X) * w1 = X1 * X1 + a * Y * (X1 * w2) := by
    have c : (X1 * X) * w1 = X1 * (X * w1) := by ring
    rw [k2] at c
    have d : X1 * (X1 + a * Y * w2) = X1 * X1 + a * Y * (X1 * w2) := by ring
    omega
  have e2 : a * (Y * Y1) * w1 = a * Y1 * Y1 + a * Y1 * (X * w2) := by
    have c : a * Y1 * (Y * w1) = a * Y1 * (Y1 + X * w2) := by rw [k1]
    have d : a * Y1 * (Y1 + X * w2) = a * Y1 * Y1 + a * Y1 * (X * w2) := by
      ring
    have e : a * Y1 * (Y * w1) = a * (Y * Y1) * w1 := by ring
    omega
  have sq2a : a * ((X * Y1) * w2) + a * w2 * w2 = a * ((X1 * Y) * w2) := by
    have r1 : a * ((X * Y1) * w2 + w2 * w2) = a * ((X1 * Y) * w2) := by
      rw [← sq2]
    have r2 : a * ((X * Y1) * w2 + w2 * w2)
        = a * ((X * Y1) * w2) + a * w2 * w2 := by ring
    omega
  have br1 : a * Y * (X1 * w2) = a * ((X1 * Y) * w2) := by ring
  have br2 : a * Y1 * (X * w2) = a * ((X * Y1) * w2) := by ring
  omega

end E961P

#print axioms E961P.pell_compose
#print axioms E961P.pell_sol
#print axioms E961P.descent_Y1_lt_Y
#print axioms E961P.descent_XY1_lt
#print axioms E961P.descent_pos
#print axioms E961P.descent_sol

#eval "E961P_KERNEL46_GREEN"
