import Mathlib

/-- If n < 4, then n = 0 or n = 1 or n = 2 or n = 3. -/
theorem nat_lt_four_cases (n : Nat) (hn : n < 4) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
  omega

/-- If `d < 3`, then `d` is one of the three exact ternary digits. -/
theorem nat_lt_three_cases (d : Nat) (hd : d < 3) :
    d = 0 ∨ d = 1 ∨ d = 2 := by
  omega

/-- If n < m, then n+1 < m or n+1 = m. -/
theorem nat_succ_lt_or_eq (n m : Nat) (hn : n < m) :
    n + 1 < m ∨ n + 1 = m := by
  omega

/-- If n < 4 and n ≠ 0 and n ≠ 1 and n ≠ 3, then n = 2. -/
theorem nat_lt_four_imp_eq_two (n : Nat) (hn : n < 4)
    (hne0 : n ≠ 0) (hne1 : n ≠ 1) (hne3 : n ≠ 3) : n = 2 := by
  omega

/-- If n < 4 and n ≠ 0 and n ≠ 3, then n = 1 or n = 2. -/
theorem nat_lt_four_imp_one_or_two (n : Nat) (hn : n < 4)
    (hne0 : n ≠ 0) (hne3 : n ≠ 3) : n = 1 ∨ n = 2 := by
  omega

/-- 3 ≠ 0 (decidable) -/
theorem gst_three_ne_zero : (3 : Nat) ≠ 0 := by decide

/-- If C(start) = 3 and start+1 = N, then C(N) = 3, contradicting bridge C(N) = 0. -/
theorem carry3_at_bridge_contradicts (R N : Nat)
    (hC1_3 : (4 * (R % 3^N)) / 3^N = 3)
    (h_bridge : (4 * (R % 3^N)) / 3^N = 0) : False := by
  omega

/-- GST+ space: C(p) % 3 = 0. -/
def is_gst_positive (R p : Nat) : Prop :=
  (4 * (R % 3^p)) / 3^p % 3 = 0

/-- ALT- space: C(p) % 3 ≠ 0. -/
def is_alt_negative (R p : Nat) : Prop :=
  (4 * (R % 3^p)) / 3^p % 3 ≠ 0

/-- NULL space: C(p) = 0. -/
def is_null_space (R p : Nat) : Prop :=
  (4 * (R % 3^p)) / 3^p = 0

/-- The bridge C(N) = 0 means N is a NULL space position. -/
theorem bridge_is_null_space (R N : Nat)
    (h_bridge : (4 * (R % 3^N)) / 3^N = 0) :
    is_null_space R N := h_bridge

/-- GST+ and ALT- are complementary. -/
theorem gst_or_alt (R p : Nat) :
    is_gst_positive R p ∨ is_alt_negative R p := by
  by_cases h : (4 * (R % 3^p)) / 3^p % 3 = 0
  · exact Or.inl h
  · exact Or.inr h

/-- NULL space implies GST+. -/
theorem null_imp_gst_positive (R p : Nat)
    (h_null : is_null_space R p) :
    is_gst_positive R p := by
  simpa [is_null_space, is_gst_positive] using congrArg (fun x => x % 3) h_null

/-- A witness lies in GST+. -/
theorem witness_is_gst_positive (R p : Nat)
    (hd2 : R / 3^p % 3 = 2)
    (hc0 : (4 * (R % 3^p)) / 3^p % 3 = 0) :
    is_gst_positive R p := hc0

/-- The cascade case lies in ALT-. -/
theorem cascade_is_alt_negative (R p : Nat)
    (hd2 : R / 3^p % 3 = 2)
    (hc_ne0 : (4 * (R % 3^p)) / 3^p % 3 ≠ 0) :
    is_alt_negative R p := hc_ne0

/-- n + 1 ≤ m → n < m. -/
theorem nat_lt_of_add_one_le (n m : Nat) (h : n + 1 ≤ m) : n < m := by omega

/-- n ≤ m → n < m + 1. -/
theorem nat_lt_succ_of_le' (n m : Nat) (h : n ≤ m) : n < m + 1 := by omega

/-!
`gst_omega` keeps the original decreasing-goal solver and a deliberately
small residual arithmetic normalizer.  During final surgery it does not call
Aesop: if the listed kernel equalities and Presburger arithmetic do not close
a residual branch, Lean must leave that branch visible rather than hiding it
behind unbounded proof search.
-/
elab "gst_omega" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    first
      | (simp_wf
         <;> first
           | exact Nat.sub_lt_sub_left (nat_lt_of_add_one_le _ _ (by assumption)) (by assumption)
           | exact Nat.sub_lt_sub_left (by assumption) (by assumption)
           | assumption
           | exact Nat.sub_succ_lt_self _ _ (by assumption)
           | exact Nat.sub_lt_self (by assumption) (by assumption)
           | exact Nat.lt_succ_of_le (by assumption)
           | decreasing_trivial_pre_omega
           | decreasing_trivial)
      | contradiction
      | omega
      | (simp_all (config := { maxSteps := 1000000 }) only [GSTResidualBoundary, GSTOmegaChildZeroSet,
            GSTOmegaBadSet, GSTOmegaBadBlock, GSTSeededAffineBadTrace,
            Set.mem_setOf_eq]
         <;> first | contradiction | omega | skip)
  ))

syntax "gst_carry_cases " ident : tactic
syntax "gst_digit_cases " ident : tactic
syntax "gst_carry_eq_cases " ident : tactic
syntax "gst_origin_residue_cases " ident : tactic

macro_rules
  | `(tactic| gst_carry_cases $C:ident) =>
      `(tactic|
        (have gstCarryCases := nat_lt_four_cases $C (by assumption);
         rcases gstCarryCases with h0 | h1 | h2 | h3
         <;> subst $C))
  | `(tactic| gst_digit_cases $d:ident) =>
      `(tactic|
        (have gstDigitCases := nat_lt_three_cases $d (by assumption);
         rcases gstDigitCases with h0 | h1 | h2
         <;> subst $d))
  | `(tactic| gst_carry_eq_cases $C:ident) =>
      `(tactic|
        (have gstCarryEqCases := nat_lt_four_cases $C (by assumption);
         rcases gstCarryEqCases with h0 | h1 | h2 | h3))
  | `(tactic| gst_origin_residue_cases $d:ident) =>
      `(tactic|
        (have gstOriginResidueCases := nat_lt_three_cases $d (by assumption);
         rcases gstOriginResidueCases with h0 | h1 | h2
         <;> subst $d
         <;> first | contradiction | skip))

/-!
  ## gst_end — the final closing tactic for the RED incision
-/
elab "gst_end" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    first
      | (apply_assumption)
      | (exact absurd (by assumption) (by assumption))
      | (simp only [GSTOmegaGatePolynomial, gstOmega, gstDigit, gstCarry,
            gstNavigationConstant, Nat.pow_one, Nat.add_mod, Nat.mul_mod,
            Nat.mod_mod, Nat.div_one, Nat.pow_zero] <;>
         omega)
      | (simp only [GSTOmegaInfiniteBadTrace, GSTOmegaGatePolynomial,
            gstOmega, GSTOmegaState.parentDigit, GSTOmegaState.parentCarry,
            gstDigit, gstCarry, gstNavigationConstant,
            gstAffineMulCarry, Nat.pow_one, Nat.add_mod, Nat.mul_mod,
            Nat.mod_mod, Nat.div_one, Nat.pow_zero,
            Set.mem_setOf_eq] at * <;>
         omega)
      | (first | contradiction | omega)
  ))
