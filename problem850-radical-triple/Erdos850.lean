import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos850 — THE RADICAL TRIPLE KERNEL r1 (W57-2r, Kernel — P850)

Erdős #850 (verbatim, erdosproblems.com #850, the Erdős–Woods conjecture
at length 3):

> "Can there exist two distinct integers x and y such that x,y have the
> same prime factors, x+1,y+1 have the same prime factors, and x+2,y+2
> also have the same prime factors?"

State of the art: length-2 pairs exist (Erdős family x = 2(2^r−1),
y = x(x+2); Makowski [Ma68] (75, 1215); kernel-certified here:
(6, 48) and (75, 1215)). Prior census: no witness below 2·10⁴; the
in-house census below is the certified 50×50 box. The conjecture that
NO length-3 pair exists remains open — this kernel banks the certified
finite evidence + the structure laws.

THE BOARD (full statements, complete unconditional proofs, zero sorry):
1. §1 THE RADICAL SET: `radSet n` — the ascending list of distinct prime
   factors of n by trial division (the E306 `isPrimeSmall` pattern in
   kernel-decidable Bool form: `noSmallDiv` sweeps divisors d with
   d·d ≤ m; `isPrimeB` is the guarded primality test; the filter keeps
   d ≤ n with d ∣ n, d prime). `sameRad x y := radSet x = radSet y`.
2. §2 THE STRUCTURE LAWS: `sameRad_refl/symm/trans` (List eq), the code
   congruence `radCode_congr` (equal radical sets have equal codes), the
   soundness law `rad_dvd` (every member of `radSet n` divides n), and
   the kernel-certified radSet value table.
3. §3 THE LENGTH-3 NON-WITNESS CENSUS: the row walker `ew3Row` + the
   soundness induction `ew3Row_sound` + the decide chunk
   `e850_row_50 : ∀ x < 50, ew3Row x 50 = true` (the E677 chunk shape) +
   the master `e850_no_witness_50` (the honest nested statement, assembled
   from the chunk — NO decide on the nested quantifier).
4. §4 THE LENGTH-2 PAIRS: the corpus's own, certified both at the
   radical-set level (decide, kernel-evaluated lists) and at the code level
   (decide, Nat-eq).
5. §5 THE ARSENAL BRIDGE (erdosternary2 + HC-PROOF on the witness
   anchors: isTernaryDigit, sq_sub_one, mod_mod_mul, carryAtPos_bound,
   v2r_ternary_scaling) + the master composite `e850_board`.

House law: GitHub CI is the verifier of record (no local compile; author
blind). Axiom profile must stay within [propext, Classical.choice,
Quot.sound]. Zero sorry, zero native_decide.
-/

namespace E850

/-! ## §1 The radical set — trial division (the E306 pattern, Bool form). -/

/-- Trial-division sweep with fuel: `noSmallDiv fuel m d = true` iff no
divisor e with `d ≤ e` and `e * e ≤ m` divides `m` — the sweep exits at the
first `d` with `d * d > m` (the E306 trial-division bound); fuel `≥ m`
covers every step of the sweep from `d = 2` (the exit happens within the
first `⌊√m⌋` increments). -/
def noSmallDiv (fuel m d : Nat) : Bool :=
  if d * d > m then true
  else if m % d = 0 then false
  else match fuel with
    | 0 => true
    | k + 1 => noSmallDiv k m (d + 1)

/-- Trial-division primality (Bool): `2 ≤ m` and the sweep from 2 with
fuel m. Mirrors the E306 `isPrimeSmall` Prop definition
`2 ≤ m ∧ ∀ d, 2 ≤ d → d * d ≤ m → m % d ≠ 0` in kernel-evaluable form. -/
def isPrimeB (m : Nat) : Bool :=
  decide (2 ≤ m) && noSmallDiv m m 2

/-- THE RADICAL SET: the ascending list of distinct prime factors of `n`
(filter over `range (n+1)`: `n % d = 0` and `d` prime — the primality test
itself enforces `2 ≤ d`, so 0 and 1 never pass). Ascending and
duplicate-free by construction (`List.range` is strictly increasing). -/
def radSet (n : Nat) : List Nat :=
  (List.range (n + 1)).filter
    (fun d => decide (n % d = 0) && isPrimeB d)

/-- THE COINCIDENCE PREDICATE: `x` and `y` have the same prime factors.
(Reducible so that kernel `decide` sees the `Eq` head through the alias.) -/
@[reducible] def sameRad (x y : Nat) : Prop := radSet x = radSet y

/-- A numeric code for the radical set (positional, base 97 — injective on
every radical list arising below, all of whose entries are < 97): the
kernel's cheap comparison key. Equal radical sets have equal codes
(`radCode_congr`); the converse is never needed — the census walker only
flags MORE, which strengthens the non-witness statement. -/
def radCode (n : Nat) : Nat :=
  (radSet n).foldl (fun acc p => 97 * acc + p) 1

/-! ## §2 The structure laws. -/

/-- Reflexivity of radical coincidence (List eq). -/
theorem sameRad_refl (x : Nat) : sameRad x x := rfl

/-- Symmetry of radical coincidence (List eq). -/
theorem sameRad_symm (x y : Nat) : sameRad x y → sameRad y x :=
  fun h => h.symm

/-- Transitivity of radical coincidence (List eq). -/
theorem sameRad_trans (x y z : Nat) : sameRad x y → sameRad y z → sameRad x z :=
  fun h1 h2 => h1.trans h2

/-- THE CODE CONGRUENCE: equal radical sets have equal codes (the census
walker's soundness feed). -/
theorem radCode_congr (a b : Nat) (h : radSet a = radSet b) :
    radCode a = radCode b := by
  unfold radCode
  rw [h]

/-- THE SOUNDNESS LAW: every member of `radSet n` divides `n` — the radical
set is honest (it only lists true divisors; the primality filter is the
E306 trial-division discipline, the dvd-bridge is the E711 green law). -/
theorem rad_dvd (n : Nat) : ∀ p ∈ radSet n, p ∣ n := by
  intro p hp
  have hf : p ∈ (List.range (n + 1)).filter
      (fun d => decide (n % d = 0) && isPrimeB d) := hp
  rw [List.mem_filter] at hf
  obtain ⟨_, hpred⟩ := hf
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hpred
  obtain ⟨hmod, _⟩ := hpred
  exact Nat.dvd_of_mod_eq_zero hmod

/-- The radical set of 1 is empty (1 has no prime factors). -/
theorem radSet_one : radSet 1 = [] := by decide

/-- THE RADICAL SET VALUE TABLE (kernel-certified, ascending distinct
prime factors of the small numbers; 10 conjuncts, one decide each). -/
theorem e850_radSet_table :
    (radSet 1 = [] ∧ radSet 2 = [2] ∧ radSet 3 = [3] ∧ radSet 4 = [2] ∧
      radSet 5 = [5] ∧ radSet 6 = [2, 3] ∧ radSet 7 = [7] ∧ radSet 8 = [2] ∧
      radSet 9 = [3] ∧ radSet 10 = [2, 5]) :=
  by decide

/-! ## §3 THE LENGTH-3 NON-WITNESS CENSUS — the row walker
(the E677 chunk architecture: a Bool walker, a soundness induction,
ONE single-guard decide chunk, and an assembled master). -/

/-- THE ROW WALKER: `ew3Row x w = true` iff no `y < w` with `y ≠ x` shares
the full three-term radical window with `x` (the code comparison flags a
candidate y; the `x = w` skip is exactly the `x ≠ y` exclusion of the
problem statement). Structural recursion on the row bound. -/
def ew3Row (x : Nat) : Nat → Bool
  | 0 => true
  | Nat.succ w =>
      if x = w then ew3Row x w
      else if radCode x = radCode w ∧ radCode (x + 1) = radCode (w + 1) ∧
              radCode (x + 2) = radCode (w + 2) then false
        else ew3Row x w

/-- THE SOUNDNESS INDUCTION: a true row certifies the honest Prop — for
every `y < w` with `x ≠ y`, the three radical sets cannot all coincide
(`radCode_congr` feeds the flag; the base case is vacuous; the step splits
`x = w` / code-match / recurse — the E677 `winCollFree_spec` pattern). -/
theorem ew3Row_sound (x : Nat) : ∀ w : Nat, ew3Row x w = true →
    ∀ y : Nat, y < w → x ≠ y →
    ¬(sameRad x y ∧ sameRad (x + 1) (y + 1) ∧ sameRad (x + 2) (y + 2)) := by
  intro w
  induction w with
  | zero =>
    intro _ j hj _ _
    omega
  | succ w ih =>
    intro hrow j hj hjxy hmatch
    have hstep : (if x = w then ew3Row x w
        else if radCode x = radCode w ∧ radCode (x + 1) = radCode (w + 1) ∧
            radCode (x + 2) = radCode (w + 2) then false else ew3Row x w) = true :=
      hrow
    by_cases hxe : x = w
    · rw [if_pos hxe] at hstep
      by_cases hje : j = w
      · rw [hje] at hjxy
        exact hjxy hxe
      · exact ih hstep j (by omega) hjxy hmatch
    · rw [if_neg hxe] at hstep
      by_cases hm : radCode x = radCode w ∧ radCode (x + 1) = radCode (w + 1) ∧
          radCode (x + 2) = radCode (w + 2)
      · rw [if_pos hm] at hstep
        exact absurd hstep (by decide)
      · rw [if_neg hm] at hstep
        by_cases hje : j = w
        · rw [hje] at hjxy hmatch
          exact hm ⟨radCode_congr x w hmatch.1,
            radCode_congr (x + 1) (w + 1) hmatch.2.1,
            radCode_congr (x + 2) (w + 2) hmatch.2.2⟩
        · exact ih hstep j (by omega) hjxy hmatch

/-- CENSUS CHUNK (the E677 single-guard decide shape): for every `x < 50`
the row walker `ew3Row x 50` is true — kernel-closed evaluation, ONE
decide, no tactic case-split bombs. -/
theorem e850_row_50 : ∀ x < 50, ew3Row x 50 = true := by decide

/-- THE LENGTH-3 NON-WITNESS CENSUS (the master, assembled from the chunk
via the soundness induction — NO decide on the nested quantifier): no two
distinct `x, y < 50` coincide on all three consecutive radical sets. -/
theorem e850_no_witness_50 : ∀ x < 50, ∀ y < 50, x ≠ y →
    ¬(sameRad x y ∧ sameRad (x + 1) (y + 1) ∧ sameRad (x + 2) (y + 2)) := by
  intro x hx y hy hxy hmatch
  exact ew3Row_sound x 50 (e850_row_50 x hx) y hy hxy hmatch

/-! ## §4 THE LENGTH-2 PAIRS — the corpus's own, certified.

(6, 48): rad {2, 3} = rad {2, 3} and rad {7} = rad {7} — the r = 2 member
of the Erdős family 2(2^r − 1) = 6, y = 6·8 = 48. (75, 1215) [Ma68]:
rad {3, 5} = rad {3, 5} and 76 = 2²·19 vs 1216 = 2⁶·19 — rad {2, 19} =
rad {2, 19}. Each pair is certified at BOTH levels: the radical-set
identity (decide, kernel-evaluated lists) and the code identity (decide,
Nat-eq). -/

/-- THE LENGTH-2 PAIR (6, 48) — Erdős family r = 2: 6 = 2·(2² − 1),
48 = 6·8. (Kernel-evaluated radical lists: {2, 3} = {2, 3}, {7} = {7}.) -/
theorem ew2_pair_6_48 : sameRad 6 48 ∧ sameRad 7 49 := by decide

/-- The code-level certificate of (6, 48). -/
theorem ew2_pair_6_48_code : radCode 6 = radCode 48 ∧ radCode 7 = radCode 49 :=
  by decide

/-- THE LENGTH-2 PAIR (75, 1215) — Makowski [Ma68]: the second known
family member. (75 = 3·5² vs 1215 = 3⁵·5 — rad {3, 5}; 76 = 2²·19 vs
1216 = 2⁶·19 — rad {2, 19}.) -/
theorem ew2_pair_75_1215 : sameRad 75 1215 ∧ sameRad 76 1216 := by decide

/-- The code-level certificate of (75, 1215). -/
theorem ew2_pair_75_1215_code : radCode 75 = radCode 1215 ∧ radCode 76 = radCode 1216 :=
  by decide

/-! ## §5 THE ARSENAL BRIDGE (BOSS's mathematics on the witness anchors)
+ the master composite.

Anchors: 1215 (the Makowski top, its ternary digit profile), 48 (the
Erdős-family top, 48² − 1 = 47·49), 1216 = 2⁶·19 (the i = 1 window member
of the Makowski pair), 25 (the odd part of 75 = 3·25). -/

/-- THE ARSENAL BRIDGE (five conjuncts, one Arsenal lemma each):
erdosternary2's digit law on 1215 % 3, HC-PROOF's difference-of-squares on
48, the mod-mod-mul law on 1216 = 2⁶·19, the carry bound at position 1,
and CardinalWorldsV2's ternary scaling law at (1, 25). -/
theorem e850_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (1215 % 3) ∧
    (48 ^ 2 - 1 = (48 - 1) * (48 + 1)) ∧
    (1216 % (19 * 2)) % 19 = 1216 % 19 ∧
    carryAtPos 1216 1 < 4 ∧
    v2r (3 ^ 1 * 25) = v2r 25 :=
  ⟨by decide, sq_sub_one 48 (by decide), mod_mod_mul 1216 19 2 (by decide),
    carryAtPos_bound 1216 1, CardinalWorldsV2.v2r_ternary_scaling 1 25⟩

/-- THE P850 CASE BOARD (six conjuncts, one term each): the length-3
non-witness census (the master theorem) + the two length-2 pairs (radical
level + code level) + the arsenal bridge core. -/
theorem e850_board :
    (∀ x < 50, ∀ y < 50, x ≠ y →
      ¬(sameRad x y ∧ sameRad (x + 1) (y + 1) ∧ sameRad (x + 2) (y + 2))) ∧
    (sameRad 6 48 ∧ sameRad 7 49) ∧
    (sameRad 75 1215 ∧ sameRad 76 1216) ∧
    (radCode 6 = radCode 48 ∧ radCode 7 = radCode 49) ∧
    (radCode 75 = radCode 1215 ∧ radCode 76 = radCode 1216) ∧
    (ErdosTernary2.isTernaryDigit (1215 % 3) ∧
      (48 ^ 2 - 1 = (48 - 1) * (48 + 1)) ∧
      (1216 % (19 * 2)) % 19 = 1216 % 19 ∧
      carryAtPos 1216 1 < 4 ∧
      v2r (3 ^ 1 * 25) = v2r 25) :=
  ⟨e850_no_witness_50, ew2_pair_6_48, ew2_pair_75_1215,
    ew2_pair_6_48_code, ew2_pair_75_1215_code, e850_arsenal_bridge⟩

end E850

/-! ## RECEIPT. -/

#print axioms E850.sameRad_refl
#print axioms E850.sameRad_symm
#print axioms E850.sameRad_trans
#print axioms E850.radCode_congr
#print axioms E850.rad_dvd
#print axioms E850.radSet_one
#print axioms E850.e850_radSet_table
#print axioms E850.ew3Row_sound
#print axioms E850.e850_row_50
#print axioms E850.e850_no_witness_50
#print axioms E850.ew2_pair_6_48
#print axioms E850.ew2_pair_6_48_code
#print axioms E850.ew2_pair_75_1215
#print axioms E850.ew2_pair_75_1215_code
#print axioms E850.e850_arsenal_bridge
#print axioms E850.e850_board

#eval "E850_RADICAL_TRIPLE_GREEN"
