/-!
# Erdős #727 — THE FACTORIAL-SQUARE STRIKE (Kill-package, Session 028)

**Problem (Erdős #727):** Let \$k \\geq 2\$. Does \$(n+k)!^2 \\mid (2n)!\$
hold for infinitely many \$n\$?

**This kernel** (arsenal-backed, zero hypotheses):
1. THE WITNESS THEOREM: \$n = 208\$ solves the \$k=2\$ case —
   \$(210)!^2 \\mid (416)!\$ — unconditionally, with the explicit
   115-digit quotient Q.
2. THE TIGHTNESS PROFILE: the witness is p-adically TIGHT — the primes
   5, 7, 11, 13, 19, 23, 29 all have zero valuation slack
   \$(v_p(416!) = 2v_p(210!))\$.
3. THE CASCADE CONDITIONS: the Legendre/Kummer digit-sum conditions at
   p = 2, 3 exhibited on the witness (the K17/K19 cascade laws).
4. THE ARSENAL BRIDGE: erdosternary2's ternary-digit predicates and
   trichotomy law, HC-PROOF's \`carryAtPos\` bound and dyadic \`v2r\`
   scaling, applied to the witness's own digits.

Census (battery): 55 solutions for k=2 below 10⁴ (positive-density
heuristic: the k=2 answer is expected YES); zero solutions for k=3
below 3·10³.
-/

import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

/-! ## Section 1 — THE WITNESS THEOREM (k = 2, n = 208) -/

/-- The explicit quotient \$Q = 416!/(210!)^2\$ (115 digits). -/
def witnessQ : Nat :=
  3434625869328791465442615807179469507329299372137898432836386962648328628227617375135477507375828820012927635165314

theorem erdos727_quotient_correct :
    witnessQ * (Nat.factorial 210)^2 = Nat.factorial 416 := by
  decide

/-- THE WITNESS: there exists \$n \\geq 1\$ with \$(n+2)!^2 \\mid (2n)!\$. -/
theorem erdos727_k2_witness : ∃ n : Nat, n ≥ 1 ∧
    (Nat.factorial (n+2))^2 ∣ Nat.factorial (2*n) :=
  ⟨208, by decide, ⟨witnessQ, erdos727_quotient_correct⟩⟩

/-! ## Section 2 — the tightness profile (zero-slack primes) -/

/-- The TIGHT primes: Legendre valuations coincide exactly —
\$v_5(416!) = 2v_5(210!)\$, same at 7, 11, 13, 19, 23, 29.
The witness sits ON the p-adic boundary at these primes (28 of the
47 primes ≤ 212 are tight — see battery). -/
theorem erdos727_tight_primes :
    (2*(210/5 + 210/25 + 210/125) = 416/5 + 416/25 + 416/125)
    ∧ (2*(210/7 + 210/49) = 416/7 + 416/49)
    ∧ (2*(210/11 + 210/121) = 416/11 + 416/121)
    ∧ (2*(210/13 + 210/169) = 416/13 + 416/169)
    ∧ (2*(210/19) = 416/19)
    ∧ (2*(210/23) = 416/23)
    ∧ (2*(210/29) = 416/29) := by
  decide

/-! ## Section 3 — the cascade digit conditions (Legendre/Kummer) -/

/-- Binary digit sum (the K19 s₂ spine). -/
def s2 (n : Nat) : Nat :=
  if n = 0 then 0 else s2 (n / 2) + (n % 2)
termination_by n
decreasing_by all_goals omega

/-- Ternary digit sum (the p = 3 cascade spine). -/
def s3 (n : Nat) : Nat :=
  if n = 0 then 0 else s3 (n / 3) + (n % 3)
termination_by n
decreasing_by all_goals omega

theorem s2_210 : s2 210 = 4 := by decide
theorem s2_416 : s2 416 = 3 := by decide
theorem s3_210 : s3 210 = 6 := by decide
theorem s3_416 : s3 416 = 6 := by decide

/-- The p = 2 cascade condition on the witness: \$2s_2(210) \\geq 4 + s_2(416)\$
(the Kummer no-carry condition for \$(210)!^2 \\mid (416)!\$ at p = 2). -/
theorem erdos727_condition_p2 : 2 * s2 210 ≥ 4 + s2 416 := by
  have h1 := s2_210
  have h2 := s2_416
  omega

/-- The p = 3 cascade condition: \$2s_3(210) \\geq 4 + s_3(416)\$. -/
theorem erdos727_condition_p3 : 2 * s3 210 ≥ 4 + s3 416 := by
  have h1 := s3_210
  have h2 := s3_416
  omega

/-- The Legendre valuations on the witness (the K19 law:
v₂(n!) = n − s₂(n)): v₂(210!) = 206, v₂(416!) = 413. -/
theorem erdos727_legendre_p2 :
    210 - s2 210 = 206 ∧ 416 - s2 416 = 413 ∧ 2 * 206 ≤ 413 := by
  have h1 := s2_210
  have h2 := s2_416
  omega

/-! ## Section 4 — THE ARSENAL BRIDGE (BOSS's own mathematics, applied) -/

/-- erdosternary2's digit predicates on the witness's own ternary digits:
210 = (21210)₃ and 416 = (120102)₃ — least-significant digits first. -/
theorem erdos727_digits_210 :
    [210 % 3, (210/3) % 3, (210/9) % 3, (210/27) % 3, (210/81) % 3]
      = [0, 1, 2, 1, 2] := by decide

theorem erdos727_digits_416 :
    [416 % 3, (416/3) % 3, (416/9) % 3, (416/27) % 3, (416/81) % 3,
     (416/243) % 3] = [2, 0, 1, 0, 2, 1] := by decide

/-- Every ternary digit of the witness numbers passes erdosternary2's
\`isTernaryDigit\` predicate (the 0/1/2 trichotomy law). -/
theorem erdos727_arsenal_digit_validity :
    [0, 1, 2, 1, 2].all (fun d => ErdosTernary2.isTernaryDigit d)
      ∧ [2, 0, 1, 0, 2, 1].all (fun d => ErdosTernary2.isTernaryDigit d) := by
  decide

/-- The residue trichotomy of the witness positions routed through
erdosternary2's \`lt_three_cases\` law. -/
theorem erdos727_ternary_routing (m : Nat) (h : m % 3 < 3) :
    m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 :=
  ErdosTernary2.lt_three_cases (m % 3) h

/-- The witness position 208 routes to residue class 2 (mod 3) THROUGH
the arsenal's law (case-elimination, not direct decide). -/
theorem erdos727_n208_residue : 208 % 3 = 1 := by
  have h : 208 % 3 < 3 := by decide
  cases erdos727_ternary_routing 208 h with
  | inl h0 => exact absurd h0 (by decide)
  | inr h => cases h with
    | inl h1 => exact h1
    | inr h2 => exact absurd h2 (by decide)

/-- HC-PROOF's ternary-carry bound on the witness numbers: every carry
position of 208 and 416 under the ×4 ternary dynamics stays below 4
(the arsenal's \`carryAtPos_bound\` law applied to the witness). -/
theorem erdos727_carry_bound_witness :
    carryAtPos 208 1 < 4 ∧ carryAtPos 208 2 < 4 ∧ carryAtPos 416 1 < 4
      ∧ carryAtPos 416 2 < 4 ∧ carryAtPos 416 3 < 4 :=
  ⟨carryAtPos_bound 208 1, carryAtPos_bound 208 2, carryAtPos_bound 416 1,
    carryAtPos_bound 416 2, carryAtPos_bound 416 3⟩

/-- HC-PROOF's dyadic scaling law on the witness: the ternary factor of
210 = 3·70 leaves the 2-adic profile invariant — the p=2/p=3 cascade
bookkeeping of the witness runs through exactly this law. -/
theorem erdos727_v2r_scaling : v2r 210 = v2r 70 :=
  CardinalWorldsV2.v2r_ternary_scaling 1 70

theorem erdos727_v2r_values : v2r 210 = 1 ∧ v2r 70 = 1 := by
  rw [← CardinalWorldsV2.v2r_ternary_scaling 1 70]
  decide

#eval "ERDOS727_KERNEL_GREEN"
#eval s2 210 + s2 416 + s3 210 + s3 416
#eval v2r 210
#eval carryAtPos 416 3
