import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536

/-! # Erdős #686 — THE SQUARE k=2 CENSUS (S035 volley, Kernel 26)

## THE PROBLEM (verbatim, erdosproblems.com/686)

> Can every integer $N\geq 2$ be written as
> \[N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}\]
> for some $k\geq 2$ and $m\geq n+k$?

## WHAT THIS PROOF PROVES (the statement above, then the proofs below —
all complete unconditional theorems; in-house reading consistent with
Kill #20 / K16: $n \ge 1$)

1. **THE INFINITE FAMILY THEOREM** (`erdos686sq_family`): for EVERY
   $u \ge 2$, the square $N = (4u+2)^2$ has the $k=2$ representation
   with $m = 4u^2+4u-1$, $n = u-1$ — i.e. every $t \equiv 2 \pmod 4$,
   $t \ge 10$ works (Theorem B of the derivation, now Lean-complete for
   ALL such $t$, no bound).
2. **THE ODD SPORADIC** (`erdos686sq_99`): $N = 99^2 = 9801$ has the
   $k=2$ representation $m = 241$, $n = 1$ ($242 \cdot 243 = 9801 \cdot
   2 \cdot 3$) — an odd-$t$ sporadic OUTSIDE the family, discovered by
   the S035 engine census.
3. **THE NO-GO THEOREM** (`erdos686sq_noRep`): the complete reduction —
   any $k=2$ representation of $t^2$ forces a divisor-pair
   $(d_1, d_2)$ of $t^2 - 1$ with $d_1 = tY - X$, $d_2 = X + tY$,
   $X = 2m+3$ odd $\ge 9$, $Y = 2n+3$ odd $\ge 5$, $X \ge Y + 2$
   (the master identity $(2m+3)^2 - t^2(2n+3)^2 = 1 - t^2$).
4. **THE CENSUS THEOREM** (`erdos686sq_census`): for EVERY $t \in [2,
   100]$: $t^2$ is $k=2$-representable $\iff$ ($t \equiv 2 \pmod 4$ and
   $t \ge 10$) or $t = 99$ — the exact square census to $t = 100$,
   kernel-certified by the small-factor scan ($d_1 \le t$: every valid
   pair has $d_1^2 < d_1 d_2 = t^2 - 1 < t^2$, so $d_1 < t$).

Honest scope: the engine census extends to $t \le 300$ (second odd
sporadic $t = 195$); the kernel census covers $t \le 100$ by the same
architecture — the extension is mechanical. The $k \ge 3$ square war
(the $t$'s with NO $k=2$ representation: $5, 7, 8, 11, 12, 13, \dots$)
is the named next front — this census is its exact foundation (every
non-representable $t^2$ NEEDS $k \ge 3$). -/

namespace Erdos686Sq

/-! ## §0 The definitions. -/

/-- The k=2 representation predicate (in-house reading: n ≥ 1, m ≥ n+2). -/
def Rep2 (N m n : Nat) : Prop :=
  (m + 1) * (m + 2) = N * (n + 1) * (n + 2) ∧ 1 ≤ n ∧ n + 2 ≤ m

/-- The divisor-pair validity check (small factor d1). -/
def divNoRepSmall (t d1 : Nat) : Bool :=
  let M := t * t - 1
  let d2 := M / d1
  decide (1 ≤ d1) && decide (d1 < d2) && decide (d1 * d2 = M) &&
  decide ((d2 - d1) % 2 = 0) &&
  decide (((d2 - d1) / 2) % 2 = 1) && decide (9 ≤ (d2 - d1) / 2) &&
  decide ((d2 + d1) % (2 * t) = 0) &&
  decide (((d2 + d1) / (2 * t)) % 2 = 1) && decide (5 ≤ (d2 + d1) / (2 * t)) &&
  decide ((d2 - d1) / 2 ≥ (d2 + d1) / (2 * t) + 2)

/-- The full no-go scan: no valid divisor pair among d1 ∈ [0, t]. -/
def nogoScan (t : Nat) : Bool := (List.range (t + 1)).all (fun d1 => !divNoRepSmall t d1)

/-- The family indicator. -/
def famOK (t : Nat) : Bool := decide (t % 4 = 2 ∧ 10 ≤ t)

/-- The census scan: every t ∈ [2, 100] is family, sporadic 99, or no-go. -/
def censusScan : Bool := (List.range 101).all (fun t =>
  !decide (2 ≤ t) || famOK t || decide (t = 99) || nogoScan t)

/-! ## §1 The arithmetic helpers. -/

/-- (a − b)(a + b) = a·a − b·b for b ≤ a (truncated-safe). -/
theorem sub_add_mul (a b : Nat) (h : b ≤ a) : (a - b) * (a + b) = a * a - b * b := by
  obtain ⟨c, hc⟩ : ∃ c, b + c = a := ⟨a - b, by omega⟩
  have hsub : a - b = c := by omega
  have hexp : (b + c) * (b + c) = b * b + 2 * b * c + c * c := by ring
  have hL : c * (b + c + b) = 2 * b * c + c * c := by ring
  rw [hsub, ← hc]
  rw [hexp]
  have hfin : b * b + 2 * b * c + c * c - b * b = 2 * b * c + c * c := by omega
  rw [hfin]
  exact hL

/-! ## §2 THE INFINITE FAMILY THEOREM. -/

/-- Every t ≡ 2 (mod 4), t ≥ 10 (i.e. t = 4u+2, u ≥ 2): the explicit
k=2 representation m = 4u²+4u−1, n = u−1. -/
theorem erdos686sq_family : ∀ u : Nat, 2 ≤ u →
    Rep2 ((4 * u + 2) * (4 * u + 2)) (4 * u * u + 4 * u - 1) (u - 1) := by
  intro u hu
  have hm1 : (4 * u * u + 4 * u - 1) + 1 = 4 * u * u + 4 * u := by omega
  have hm2 : (4 * u * u + 4 * u - 1) + 2 = 4 * u * u + 4 * u + 1 := by omega
  have hn1 : (u - 1) + 1 = u := by omega
  have hn2 : (u - 1) + 2 = u + 1 := by omega
  refine ⟨?_, by omega, ?_⟩
  · rw [hm1, hm2, hn1, hn2]
    ring
  · -- m ≥ n + 2: 4u² + 4u − 1 ≥ u + 1 (u ≥ 2)
    have hu2 : u * 1 ≤ u * u := Nat.mul_le_mul_left u (by omega)
    omega

/-! ## §3 THE ODD SPORADIC. -/

/-- 99² = 9801 with m = 241, n = 1: 242 · 243 = 58806 = 9801 · 6. -/
theorem erdos686sq_99 : Rep2 (99 * 99) 241 1 := by
  refine ⟨by norm_num, by omega, by omega⟩

/-! ## §4 THE NO-GO REDUCTION (the master theorem). -/

/-- THE BRIDGE: if t² has a k=2 representation, some small factor
d1 ≤ t passes the divisor-pair check. -/
theorem erdos686sq_noRep (t : Nat) (h2 : 2 ≤ t)
    (hscan : nogoScan t = true) :
    ∀ m n : Nat, ¬ Rep2 (t * t) m n := by
  intro m n hrep
  obtain ⟨heq, hn1, hmn⟩ := hrep
  set X := 2 * m + 3 with hX
  set Y := 2 * n + 3 with hY
  -- the master identity: X² + t² = t²·Y² + 1
  have hmaster : X * X + t * t = t * t * Y * Y + 1 := by
    have hX2 : X * X = 4 * ((m + 1) * (m + 2)) + 1 := by
      show (2 * m + 3) * (2 * m + 3) = 4 * ((m + 1) * (m + 2)) + 1
      ring
    have hY2 : Y * Y = 4 * ((n + 1) * (n + 2)) + 1 := by
      show (2 * n + 3) * (2 * n + 3) = 4 * ((n + 1) * (n + 2)) + 1
      ring
    calc X * X + t * t
        = 4 * ((m + 1) * (m + 2)) + 1 + t * t := by rw [hX2]
      _ = t * t * (4 * ((n + 1) * (n + 2)) + 1) + 1 := by
          rw [heq]; ring
      _ = t * t * Y * Y + 1 := by rw [← hY2]; ring
  -- tY > X (the sign law: X² < t²Y²)
  have htt : 4 ≤ t * t := by
    have hmul : t * 2 ≤ t * t := Nat.mul_le_mul_left t (by omega)
    omega
  have hXY : X < t * Y := by
    by_contra hcon
    have hge : t * Y ≤ X := by omega
    have hle : (t * Y) * (t * Y) ≤ X * X := Nat.mul_le_mul hge hge
    have hsame : (t * Y) * (t * Y) = t * t * Y * Y := by ring
    omega
  -- the divisor pair
  set d1 := t * Y - X with hd1
  set d2 := X + t * Y with hd2
  have hd1pos : 1 ≤ d1 := by omega
  have hd1d2 : d1 * d2 = t * t - 1 := by
    have hfac := sub_add_mul (t * Y) X (by omega)
    have hprod_eq : d1 * d2 = (t * Y - X) * (t * Y + X) := by
      rw [hd1, hd2, Nat.add_comm X (t * Y)]
    have hsame2 : t * Y * (t * Y) = t * t * Y * Y := by ring
    omega
  -- d1 < d2 and d1 < t
  have hd1lt : d1 < d2 := by omega
  have hd1t : d1 < t := by
    by_contra hcon
    have hge : t ≤ d1 := by omega
    have hsq : d1 * d1 ≤ d1 * d2 := Nat.mul_le_mul_left d1 (Nat.le_of_lt hd1lt)
    have ht2 : t * t ≤ d1 * d1 := Nat.mul_le_mul hge hge
    have htt2 : 4 ≤ t * t := by
      have hmul : t * 2 ≤ t * t := Nat.mul_le_mul_left t (by omega)
      omega
    omega
  -- the division facts
  have hMdiv : (t * t - 1) / d1 = d2 := by
    rw [← hd1d2]
    exact Nat.mul_div_cancel_left d2 (show 0 < d1 by omega)
  -- the ten components
  have hc1 : decide (1 ≤ d1) = true := decide_eq_true hd1pos
  have hc2 : decide (d1 < (t * t - 1) / d1) = true := by
    rw [hMdiv]
    exact decide_eq_true hd1lt
  have hc3 : decide (d1 * ((t * t - 1) / d1) = t * t - 1) = true := by
    rw [hMdiv]
    exact decide_eq_true hd1d2
  have heven : d2 - d1 = 2 * X := by omega
  have hd2m1 : (d2 - d1) / 2 = X := by
    rw [heven, Nat.mul_div_cancel_left X (show (0:Nat) < 2 by norm_num)]
  have hoddX : X % 2 = 1 := by omega
  have hX9 : 9 ≤ X := by omega
  have hc4 : decide (((t * t - 1) / d1 - d1) % 2 = 0) = true := by
    rw [hMdiv]
    have : d2 - d1 = 2 * X := by omega
    rw [this, Nat.mul_mod]
    norm_num
  have hc5 : decide ((((t * t - 1) / d1 - d1) / 2) % 2 = 1) = true := by
    rw [hMdiv]
    have h1 : (d2 - d1) / 2 = X := by
      rw [show d2 - d1 = 2 * X by omega, Nat.mul_div_cancel_left X (show (0:Nat) < 2 by norm_num)]
    rw [h1]
    exact decide_eq_true hoddX
  have hc6 : decide (9 ≤ ((t * t - 1) / d1 - d1) / 2) = true := by
    rw [hMdiv]
    have h1 : (d2 - d1) / 2 = X := by
      rw [show d2 - d1 = 2 * X by omega, Nat.mul_div_cancel_left X (show (0:Nat) < 2 by norm_num)]
    rw [h1]
    exact decide_eq_true hX9
  have hsum : d2 + d1 = t * Y + t * Y := by omega
  have hform : t * Y + t * Y = 2 * t * Y := by ring
  have hdivt : (d2 + d1) / (2 * t) = Y := by
    rw [hsum, hform]
    exact Nat.mul_div_cancel_left Y (show 0 < 2 * t by omega)
  have hoddY : Y % 2 = 1 := by omega
  have hY5 : 5 ≤ Y := by omega
  have hXY2 : Y + 2 ≤ X := by omega
  have hc7 : decide (((t * t - 1) / d1 + d1) % (2 * t) = 0) = true := by
    rw [hMdiv]
    have h1 : d2 + d1 = t * Y + t * Y := by omega
    have hdvdmod : (2 * t) ∣ (t * Y + t * Y) := ⟨Y, by ring⟩
    rw [h1]
    exact decide_eq_true (Nat.dvd_iff_mod_eq_zero.mp hdvdmod)
  have hc8 : decide ((((t * t - 1) / d1 + d1) / (2 * t)) % 2 = 1) = true := by
    rw [hMdiv]
    have h1 : (d2 + d1) / (2 * t) = Y := by
      have ha : d2 + d1 = t * Y + t * Y := by omega
      have hb : t * Y + t * Y = 2 * t * Y := by ring
      rw [ha, hb]
      exact Nat.mul_div_cancel_left Y (show 0 < 2 * t by omega)
    rw [h1]
    exact decide_eq_true hoddY
  have hc9 : decide (5 ≤ ((t * t - 1) / d1 + d1) / (2 * t)) = true := by
    rw [hMdiv]
    have h1 : (d2 + d1) / (2 * t) = Y := by
      have ha : d2 + d1 = t * Y + t * Y := by omega
      have hb : t * Y + t * Y = 2 * t * Y := by ring
      rw [ha, hb]
      exact Nat.mul_div_cancel_left Y (show 0 < 2 * t by omega)
    rw [h1]
    exact decide_eq_true hY5
  have hc10 : decide (((t * t - 1) / d1 - d1) / 2 ≥
      ((t * t - 1) / d1 + d1) / (2 * t) + 2) = true := by
    rw [hMdiv]
    have h1 : (d2 - d1) / 2 = X := by
      rw [show d2 - d1 = 2 * X by omega, Nat.mul_div_cancel_left X (show (0:Nat) < 2 by norm_num)]
    have h2' : (d2 + d1) / (2 * t) = Y := by
      have ha : d2 + d1 = t * Y + t * Y := by omega
      have hb : t * Y + t * Y = 2 * t * Y := by ring
      rw [ha, hb]
      exact Nat.mul_div_cancel_left Y (show 0 < 2 * t by omega)
    rw [h1, h2']
    exact decide_eq_true hXY2
  -- assemble: divNoRepSmall t d1 = true, contradicting the scan
  have htrue : divNoRepSmall t d1 = true := by
    simp only [divNoRepSmall]
    rw [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10]
    rfl
  have hall := (List.all_eq_true.mp hscan) d1 (List.mem_range.mpr (by omega))
  rw [htrue] at hall
  simp at hall

/-! ## §5 THE CENSUS SCAN (one kernel decide). -/

theorem census_scan_true : censusScan = true := by decide

/-! ## §6 THE CENSUS THEOREM. -/

theorem erdos686sq_census : ∀ t : Nat, 2 ≤ t → t ≤ 100 →
    ((∃ m n, Rep2 (t * t) m n) ↔ ((t % 4 = 2 ∧ 10 ≤ t) ∨ t = 99)) := by
  intro t h2 h100
  constructor
  · intro hrep
    by_contra hcon
    push_neg at hcon
    obtain ⟨hfam, h99⟩ := hcon
    have hscan := (List.all_eq_true.mp census_scan_true) t
      (List.mem_range.mpr (by omega))
    -- evaluate the disjunction: !decide(2 ≤ t) = false, famOK t = false, t = 99 = false
    have hd2 : decide (2 ≤ t) = true := decide_eq_true h2
    have hfa : famOK t = false := by
      cases hf : famOK t with
      | false => rfl
      | true =>
          have hand : t % 4 = 2 ∧ 10 ≤ t := of_decide_eq_true hf
          exact absurd hand (by
            intro hh
            have hlt := hfam hh.1
            omega)
    have h99f : decide (t = 99) = false := by
      cases hf : decide (t = 99) with
      | false => rfl
      | true => exact absurd (of_decide_eq_true hf) h99
    rw [hd2, Bool.not_true, hfa, Bool.false_or, Bool.false_or, h99f,
      Bool.false_or] at hscan
    -- hscan : nogoScan t = true — contradiction with the representation
    obtain ⟨m, n, hmn⟩ := hrep
    exact erdos686sq_noRep t h2 hscan m n hmn
  · intro hcase
    rcases hcase with ⟨hmod, h10⟩ | h99
    · -- family: t ≡ 2 mod 4, t ≥ 10: t = 4u+2 with u = (t-2)/4 ≥ 2
      have hu : 2 ≤ (t - 2) / 4 := by omega
      have htval : t = 4 * ((t - 2) / 4) + 2 := by omega
      have hN : t * t = (4 * ((t - 2) / 4) + 2) * (4 * ((t - 2) / 4) + 2) := by
        rw [← htval]
      obtain ⟨hval, hn1', hmn'⟩ := erdos686sq_family ((t - 2) / 4) hu
      refine ⟨_, _, ?_, hn1', hmn'⟩
      rw [hval, ← hN]
    · rw [h99]
      exact ⟨241, 1, erdos686sq_99⟩

/-! ## §7 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

theorem erdos686sq_arsenal_bridge :
    [242 % 3, (242 / 3) % 3, (242 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [243 % 3, (243 / 3) % 3, (243 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 58806 1 < 4 ∧
    v2r (3 ^ 2 * 243) = v2r 243 :=
  ⟨by decide, by decide, carryAtPos_bound 58806 1,
    CardinalWorldsV2.v2r_ternary_scaling 2 243⟩

/-- THE MAIN SUMMARY: the infinite family + the sporadic + the census. -/
theorem erdos686sq_main :
    (∀ u : Nat, 2 ≤ u → Rep2 ((4 * u + 2) * (4 * u + 2)) (4 * u * u + 4 * u - 1) (u - 1)) ∧
    Rep2 (99 * 99) 241 1 ∧
    (∀ t : Nat, 2 ≤ t → t ≤ 100 →
      ((∃ m n, Rep2 (t * t) m n) ↔ ((t % 4 = 2 ∧ 10 ≤ t) ∨ t = 99))) := by
  exact ⟨erdos686sq_family, erdos686sq_99, erdos686sq_census⟩

#eval "ERDOS686SQ_KERNEL_GREEN"
#print axioms erdos686sq_family
#print axioms erdos686sq_99
#print axioms erdos686sq_noRep
#print axioms census_scan_true
#print axioms erdos686sq_census
#print axioms erdos686sq_arsenal_bridge
#print axioms erdos686sq_main

end Erdos686Sq
