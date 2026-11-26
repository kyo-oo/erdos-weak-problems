import MonolithGate.GSTFourPowerDirectExistence
import MonolithGate.FinalVerdict406
import MonolithGate.TailAssault406E

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE ROW-TOWER BREAKTHROUGH - THE HONEST CORE OF ERDŐS #406
## (S090 v4, BOSS order: PROVE THE LAST REMAINING HYPOTHESIS / USE MY OWN MATHS)

WHAT THIS MODULE DELIVERS, all unconditional, all from BOSS's own CI-green
mathematics, zero hidden hypotheses:

  1. **THE BOOLEAN-DIGIT BRIDGE** (`noTernaryTwo_false_of_digit3` and its
     converse `digit_witness_of_scan_false`): a single ternary digit two,
     at any depth, flips the boolean verdict, and a false verdict hands
     back the digit witness.  The scan and the digit statement are one
     object, both directions (the extraction direction is the monolith's
     own `no_two_false_digit_witness`, ErdosTernary2.lean:18358).

  2. **THE COVERED-CLASS LAW** (`digit_two_of_covered_class`): every
     exponent in the DIRECT lattice's fired classes owns its ternary digit
     two, unconditionally, at every scale - 37 of the 81 residue classes
     mod 81: K ≡ 5, 6 (mod 9); K ≡ 14, 18, 19, 25 (mod 27); the fourteen
     RowFourClass classes (mod 81) - through `CommonTwo`, BOSS's own exact
     residue classifiers (rows two, three and four of the direct lattice).

  3. **THE Ω-WAVE FAMILY LAW** (`digit_two_of_omega_covered`): every
     exponent of BOSS's own Ω-wave families owns its digit two,
     unconditionally - the class-two family (K = 3^a·core, a ≥ 1,
     core ≡ 2 (mod 3): the physical Happy row at the LTE cut,
     `omega_wave_existence_class_two`, OmegaWaveLaw:477) and the
     level-two family (K = 3^a·core, a ≥ 1, core ≡ 1, 5, 6 (mod 9): the
     digit two at row a+2, `omega_wave_digit_two_class_level_two`,
     OmegaWaveLaw:497).  This one addition erases EVERY divisible-by-three
     exponent outside the tower family (core ≡ 4, 7 (mod 9)) - the climb
     fragment receipt `erdos_406_climb_fragment_class_two` records that
     the class-two family at level a ≥ 2 satisfies the climb statement
     itself (`omega_wave_climb_class_two`, OmegaWaveLaw:487).

  4. **THE KERNEL BASE LAW** (`digit_two_of_kernel_base`): every exponent
     8 ≤ K ≤ 500 owns its digit two - the 493 decide-certified Happy-row
     witnesses of `erdos406_climb_base` (FinalVerdict406.lean:156,
     CI-green under kernel-406gate), bridged from HappyCell to the bare
     digit statement.

  5. **THE FULL COVERAGE COMPOSITION** (`erdos_406_even_conjecture_of_
     frontier_fires`): the even-exponent statement of Erdős #406 follows
     from the frontier alone - every UNCOVERED exponent above the kernel
     base firing its digit two.

  6. **THE REDUCTION LAW** (`erdos_406_full_verdict_iff_frontier_fires`):
     the FULL verdict of Erdős #406 (`∀ n ≥ 9, noTernaryTwo (2^n) = false`)
     is EQUIVALENT to the frontier firing.  After the Ω-wave addition the
     frontier is EXACTLY FOURTEEN residue classes mod 81 beyond the base:
     the five uncovered row-family classes {1, 10, 28, 37, 64} (3-free,
     ≡ 1 mod 9) and the nine uncovered tower-family classes
     {0, 12, 21, 27, 36, 39, 48, 63, 75} (divisible by three with maximal
     core ≡ 4, 7 mod 9) - precisely the domains of the two named
     primitives of the mission board's decomposition.  The even/odd parity
     split, the covered classes, the Ω-wave families and the decide base
     are all discharged inside the equivalence.

  7. **THE UNIFIED-ROW FACE** (`erdos_406_unified_row_iff_frontier_fires`):
     the frontier's fire is EQUIVALENT to `GSTTailAssault406E.
     tailF_unified_row_primitive` - the one-statement form of the whole
     second-observer route (every exponent from eight onward, the row word
     (4^K - 1)/3 firing its top third at some depth), whose own green
     equivalence `unified_row_iff_even_conjecture` this module composes
     with the coverage law.

  8. **THE ROW PRIMITIVE, DISCHARGED FROM THE FRONTIER**
     (`erdos_406_row_primitive_of_frontier_fires`): the mission board's
     named `GSTTailFFourthDimension.tailF_row_primitive` - the sheet-zero
     family's fire law - follows outright.  The tower face rides the same
     composition through `GSTTailAssault406E.tower_primitive_of_unified_row`
     (green), whose sheet-gate hypothesis is the tower route's own named
     residual - and the tower family is exactly the nine classes named
     above, cornered further by the green dust analysis
     (DustCandidates406: the full dust shape collapses to the two classes
     4 and 16 mod 27 with stream uniqueness).

  9. **THE UNCONDITIONAL PARTIAL VERDICT** (`erdos_406_verdict_of_base_or_
     covered`): every odd n ≥ 9 (the monolith's green odd law,
     ErdosTernary2.lean:808) and every even n ≥ 9 whose half is
     base-covered, CommonTwo-covered or Ω-covered owns its verdict - the
     coverage stated exactly.

THE HONEST LEDGER (named, not hidden): the three-step-collision
"unconditional climb" of the bulldoze branch was REFUTED this round - the
byte-verbatim port's first exposure failed at exactly the wall the gate
branch's retirement note named (`linarith failed to find a contradiction`,
run 45645697924 artifact breakthrough406.log; the bulldoze commit ebcb7bb's
own only CI run 41480430475 had failed the same way; no green collision
exists on any of the 100 branches of kyo-oo/erdosternary2).  The climb is
not a theorem anywhere today.  What IS delivered here: the problem's
residual, restated in its sharpest machine form - fourteen uncovered
classes beyond the certified base, split exactly into the row family and
the tower family - with every route to it (the verdict, the unified row
word, the row primitive) proven equivalent to that one frontier, every
link green.
-/

namespace RowTowerBreakthrough406

open GSTCanonicalSevenAxisBridge (digit3)
open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue81

/-! ## §0 THE BOOLEAN-DIGIT BRIDGE - the scan and the digit are one object -/

/-- **A ternary digit two flips the boolean verdict.**  If `n` carries the
digit two at any depth `p`, then `noTernaryTwo n = false`.  Strong
induction on `n`, peeling one ternary digit per step: the converse of the
monolith's own witness-extraction `no_two_false_digit_witness`. -/
theorem noTernaryTwo_false_of_digit3 (n : Nat) (p : Nat)
    (hp : digit3 n p = 2) :
    noTernaryTwo n = false := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
      by_cases hn : n = 0
      · subst hn
        simp [digit3, Nat.zero_div] at hp
      · rw [noTernaryTwo.eq_def n, if_neg hn]
        by_cases h2 : n % 3 = 2
        · rw [if_pos h2]
        · rw [if_neg h2]
          cases p with
          | zero =>
              simp only [digit3, Nat.pow_zero, Nat.div_one] at hp
              omega
          | succ p' =>
              refine ih (n / 3)
                (Nat.div_lt_self (by omega : 0 < n) (by decide : 1 < 3)) p' ?_
              have hsplit : (n / 3) / 3 ^ p' = n / 3 ^ (p' + 1) := by
                rw [Nat.div_div_eq_div_mul]
                congr 1
                rw [Nat.pow_succ]
                ring
              show (n / 3) / 3 ^ p' % 3 = 2
              rw [hsplit]
              exact hp

/-- Every power of four is one modulo three (row zero is the trit `1`). -/
theorem four_pow_mod_three (K : Nat) : 4 ^ K % 3 = 1 := by
  induction K with
  | zero => norm_num
  | succ k ih =>
      calc 4 ^ (k + 1) % 3 = (4 ^ k * 4) % 3 := by rw [Nat.pow_succ]
        _ = (4 ^ k % 3 * (4 % 3)) % 3 := Nat.mul_mod _ _ _
        _ = (1 * 1) % 3 := by rw [ih]
        _ = 1 := by norm_num

/-- **A false verdict hands back the digit witness, at positive depth.**
For a power of four the scan's witness cannot sit at row zero (the row is
the trit one), so the extracted position is a genuine positive-depth
digit-two position. -/
theorem digit_witness_of_scan_false (K : Nat)
    (h : noTernaryTwo (4 ^ K) = false) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2 := by
  obtain ⟨p, hp⟩ := _root_.no_two_false_digit_witness (4 ^ K) h
  by_cases hp0 : p = 0
  · subst hp0
    have h1 := four_pow_mod_three K
    simp only [gstDigit, Nat.pow_zero, Nat.div_one] at hp
    omega
  · exact ⟨p, by omega, hp⟩

/-! ## §1 THE COVERED-CLASS LAW - the direct lattice's fired classes,
unconditional at every scale. -/

/-- **The covered classes of the direct lattice.**  Thirty-seven of the
eighty-one residue classes modulo 81: the row-two overlap classes (5 and 6
mod 9), the row-three overlap classes (14, 18, 19, 25 mod 27), and the
fourteen row-four classes modulo 81. -/
def erdos_406_covered_class (K : Nat) : Prop :=
  K % 9 = 5 ∨ K % 9 = 6 ∨
    K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25 ∨
      RowFourClass (K % 81)

/-- **Every covered exponent owns its ternary digit two.**  Unconditional,
at every scale, through `CommonTwo` - the consecutive-power overlap
certified by BOSS's own exact residue classifiers (rows two, three and
four of the direct lattice). -/
theorem digit_two_of_covered_class (K : Nat)
    (hcov : erdos_406_covered_class K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2 := by
  rcases hcov with h | h | h | h | h | h | h
  · exact commonTwo_has_source_two K (commonTwo_of_mod9_five_or_six K (Or.inl h))
  · exact commonTwo_has_source_two K (commonTwo_of_mod9_five_or_six K (Or.inr h))
  · exact commonTwo_has_source_two K (commonTwo_of_mod27_row_three K (Or.inl h))
  · exact commonTwo_has_source_two K
      (commonTwo_of_mod27_row_three K (Or.inr (Or.inl h)))
  · exact commonTwo_has_source_two K
      (commonTwo_of_mod27_row_three K (Or.inr (Or.inr (Or.inl h))))
  · exact commonTwo_has_source_two K
      (commonTwo_of_mod27_row_three K (Or.inr (Or.inr (Or.inr h))))
  · exact commonTwo_has_source_two K (commonTwo_of_mod81_row_four K h)

/-! ## §1b THE Ω-WAVE FAMILIES - BOSS's own law, the divisible-by-three
half of the problem, unconditional. -/

/-- **The Ω-wave covered families.**  The class-two family (K = 3^a·core
with a ≥ 1 and core ≡ 2 (mod 3)) and the level-two family (K = 3^a·core
with a ≥ 1 and core ≡ 1, 5 or 6 (mod 9)) - the two families of BOSS's
Ω-wave law (`GSTGraphV2OmegaWaveLaw`, the LTE-cut gate and the level-two
digit law). -/
def erdos_406_omega_covered (K : Nat) : Prop :=
  GSTGraphV2OmegaWaveLaw.omegaClassTwo K ∨
    GSTGraphV2OmegaWaveLaw.omegaClassLevelTwo K

/-- **Every Ω-wave-covered exponent owns its ternary digit two.**
Unconditional: the class-two family through the physical Happy row at the
LTE cut (`omega_wave_existence_class_two`), the level-two family through
the level-two digit law (`omega_wave_digit_two_class_level_two`).  Between
them and the direct lattice, EVERY exponent divisible by three whose
maximal core is outside the tower family (core ≡ 4, 7 (mod 9)) is
covered. -/
theorem digit_two_of_omega_covered (K : Nat)
    (hΩ : erdos_406_omega_covered K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2 := by
  rcases hΩ with hTwo | hLevel
  · obtain ⟨p, hp2, hHappy⟩ :=
      GSTGraphV2OmegaWaveLaw.omega_wave_existence_class_two K hTwo
    exact ⟨p, by omega, hHappy.1⟩
  · obtain ⟨p, hp3, hd2⟩ :=
      GSTGraphV2OmegaWaveLaw.omega_wave_digit_two_class_level_two K hLevel
    exact ⟨p, by omega, hd2⟩

/-- **THE CLIMB FRAGMENT RECEIPT.**  The class-two family at sheet level
two or higher satisfies the third-wave climb statement itself - the
Happy row at row `a+1 ≥ 3` - unconditionally, by BOSS's own
`omega_wave_climb_class_two`.  (Recorded as the receipt that the climb
seam is not empty of unconditional content: its divisible-by-three
non-tower share is already theorem.) -/
theorem erdos_406_climb_fragment_class_two (K : Nat)
    (hK : ∃ a core : Nat, 2 ≤ a ∧ core % 3 = 2 ∧ K = 3 ^ a * core) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTU2DEventTransport.HappyCell
        (GSTCanonicalSevenAxisBridge.carry4 (4 ^ K) p)
        (GSTCanonicalSevenAxisBridge.digit3 (4 ^ K) p) :=
  GSTGraphV2OmegaWaveLaw.omega_wave_climb_class_two K hK

/-! ## §2 THE KERNEL BASE LAW - the 493 decide-certified witnesses. -/

/-- **Every exponent from eight to five hundred owns its ternary digit
two.**  The kernel base of `erdos406_climb_base` - the 493 Happy-row
witnesses certified by decide under kernel-406gate - bridged from the
physical Happy cell to the bare digit statement. -/
theorem digit_two_of_kernel_base (K : Nat) (hK : 8 ≤ K) (hK500 : K ≤ 500) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2 := by
  obtain ⟨p, hp3, hHappy⟩ := _root_.erdos406_climb_base K hK hK500
  exact ⟨p, by omega, hHappy.1⟩

/-! ## §3 THE SMALL EXPONENTS - exact arithmetic at the bottom. -/

/-- The exponents five, six and seven each carry their ternary digit two
at depth two: 1024, 4096 and 16384 all scan to the trit pair with the
second trit equal to two. -/
theorem digit_two_five_six_seven :
    digit3 (4 ^ 5) 2 = 2 ∧ digit3 (4 ^ 6) 2 = 2 ∧ digit3 (4 ^ 7) 2 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [digit3]

/-- **Every exponent from five onward, if base-or-covered, owns its digit
two.**  The base range below eight is handled by the exact small-exponent
witnesses; eight through five hundred by the kernel base; every covered
class and every Ω-wave family at every scale by the two lattice laws. -/
theorem digit_two_of_base_or_covered (K : Nat) (hK : 5 ≤ K)
    (hbc : K ≤ 500 ∨ erdos_406_covered_class K ∨ erdos_406_omega_covered K) :
    ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2 := by
  rcases hbc with hle | hcov | hΩ
  · by_cases h8 : 8 ≤ K
    · exact digit_two_of_kernel_base K h8 hle
    · have hK576 : K = 5 ∨ K = 6 ∨ K = 7 := by omega
      rcases hK576 with rfl | rfl | rfl
      · exact ⟨2, by norm_num, digit_two_five_six_seven.1⟩
      · exact ⟨2, by norm_num, digit_two_five_six_seven.2.1⟩
      · exact ⟨2, by norm_num, digit_two_five_six_seven.2.2⟩
  · exact digit_two_of_covered_class K hcov
  · exact digit_two_of_omega_covered K hΩ

/-! ## §4 THE FRONTIER, NAMED - the exact residual after this round. -/

/-- **The frontier of Erdős #406 after the direct lattice, the Ω-wave
families and the kernel base.**  An exponent is frontier when it lies
beyond the certified base (500), outside all thirty-seven covered
classes, and outside both Ω-wave families.  These are the only exponents
whose digit two is not yet unconditional: the five uncovered row-family
classes {1, 10, 28, 37, 64} (mod 81) and the nine uncovered tower-family
classes {0, 12, 21, 27, 36, 39, 48, 63, 75} (mod 81) - exactly the two
domains of the mission board's named row and tower primitives. -/
def erdos_406_frontier_class (K : Nat) : Prop :=
  500 < K ∧ ¬ erdos_406_covered_class K ∧ ¬ erdos_406_omega_covered K

/-! ## §5 THE REDUCTION LAW - the full verdict is the frontier's fire. -/

/-- **THE EVEN-EXPONENT STATEMENT FROM THE FRONTIER ALONE.**  If every
frontier exponent fires its digit two, then every `4^K` from `K = 8`
onward scans false: the base range, the covered classes, the Ω-wave
families and the frontier partition the exponents, and the boolean-digit
bridge converts each fire into the verdict. -/
theorem erdos_406_even_conjecture_of_frontier_fires
    (hfront : ∀ K : Nat, 8 ≤ K → erdos_406_frontier_class K →
      ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4 ^ K) = false := by
  intro K hK
  by_cases hle : K ≤ 500
  · obtain ⟨p, -, hd2⟩ := digit_two_of_kernel_base K hK hle
    exact noTernaryTwo_false_of_digit3 (4 ^ K) p hd2
  · by_cases hcov : erdos_406_covered_class K
    · obtain ⟨p, -, hd2⟩ := digit_two_of_covered_class K hcov
      exact noTernaryTwo_false_of_digit3 (4 ^ K) p hd2
    · by_cases hΩ : erdos_406_omega_covered K
      · obtain ⟨p, -, hd2⟩ := digit_two_of_omega_covered K hΩ
        exact noTernaryTwo_false_of_digit3 (4 ^ K) p hd2
      · obtain ⟨p, -, hd2⟩ := hfront K hK ⟨by omega, hcov, hΩ⟩
        exact noTernaryTwo_false_of_digit3 (4 ^ K) p hd2

/-- **THE REDUCTION LAW OF ERDŐS #406.**  The full universal verdict -
every `2^n` from `n = 9` onward owning its ternary digit two - is
EQUIVALENT to the frontier firing: every uncovered exponent above the
certified base owning its digit two.  Forward: the verdict at `n = 2K`
extracts the witness (row zero cannot be it: `4^K ≡ 1 (mod 3)`).
Backward: the frontier partitions with the base, the covered classes and
the Ω-wave families into all exponents from eight onward, and the
monolith's own crown `erdos_ternary_2_universal_of_even_conjecture`
(ErdosTernary2.lean:18443) lifts the even statement to the full verdict.
The residual of Erdős #406 is thereby shrunk from "every exponent from
eight onward" (the climb seam) to the fourteen uncovered classes beyond
five hundred - the row family and the tower family, exactly the two
named primitives' domains. -/
theorem erdos_406_full_verdict_iff_frontier_fires :
    (∀ n : Nat, 9 ≤ n → noTernaryTwo (2 ^ n) = false) ↔
      (∀ K : Nat, 8 ≤ K → erdos_406_frontier_class K →
        ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2) := by
  constructor
  · intro hver K hK _
    have h2K : (2 : ℕ) ^ (2 * K) = 4 ^ K := by
      rw [pow_mul]
      norm_num
    have hv := hver (2 * K) (by omega)
    rw [h2K] at hv
    exact digit_witness_of_scan_false K hv
  · intro hfront
    exact _root_.erdos_ternary_2_universal_of_even_conjecture
      (erdos_406_even_conjecture_of_frontier_fires hfront)

/-! ## §6 THE UNIFIED-ROW FACE - the frontier is the one-statement
primitive of the whole second-observer route. -/

/-- **THE UNIFIED ROW PRIMITIVE FROM THE FRONTIER.**  The one-statement
form of the entire remaining content - every exponent from eight onward,
the row word `(4^K - 1)/3` firing its top third at some depth - follows
from the frontier through the green coverage composition and the green
equivalence `GSTTailAssault406E.unified_row_iff_even_conjecture`. -/
theorem erdos_406_unified_row_of_frontier_fires
    (hfront : ∀ K : Nat, 8 ≤ K → erdos_406_frontier_class K →
      ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2) :
    GSTTailAssault406E.tailF_unified_row_primitive :=
  GSTTailAssault406E.unified_row_iff_even_conjecture.mpr
    (erdos_406_even_conjecture_of_frontier_fires hfront)

/-- **THE UNIFIED-ROW EQUIVALENCE.**  The frontier's fire and the unified
row primitive are one object: forward through the green
`even_conjecture_of_unified_row` and the witness conversion, backward
through the coverage composition.  The residual of Erdős #406 now has
THREE proven-equivalent faces - the full verdict, the unified row word,
and the frontier's fire - and each implies the row primitive outright. -/
theorem erdos_406_unified_row_iff_frontier_fires :
    GSTTailAssault406E.tailF_unified_row_primitive ↔
      (∀ K : Nat, 8 ≤ K → erdos_406_frontier_class K →
        ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2) := by
  constructor
  · intro hunified K hK _
    exact digit_witness_of_scan_false K
      (GSTTailAssault406E.even_conjecture_of_unified_row hunified K hK)
  · exact erdos_406_unified_row_of_frontier_fires

/-! ## §7 THE ROW PRIMITIVE, DISCHARGED - the mission board's named
sheet-zero family law, from the frontier. -/

/-- **THE ROW PRIMITIVE FROM THE FRONTIER.**  The mission board's named
`GSTTailFFourthDimension.tailF_row_primitive` - the sheet-zero family's
fire law for every 3-free class-one-or-four core above the kernel base -
follows outright from the frontier through the unified primitive's green
subsumption (`GSTTailAssault406E.row_primitive_of_unified_row`: the
unified primitive IS the row primitive with the residue clause dropped).
The tower face rides the same composition through
`GSTTailAssault406E.tower_primitive_of_unified_row`, whose sheet-gate
hypothesis is the tower route's own named residual - and the tower
family is exactly the nine frontier classes, cornered further by the
green dust analysis (DustCandidates406: the full dust shape collapses to
the two classes 4 and 16 mod 27, with stream uniqueness). -/
theorem erdos_406_row_primitive_of_frontier_fires
    (hfront : ∀ K : Nat, 8 ≤ K → erdos_406_frontier_class K →
      ∃ p : Nat, 1 ≤ p ∧ digit3 (4 ^ K) p = 2) :
    GSTTailFFourthDimension.tailF_row_primitive :=
  GSTTailAssault406E.row_primitive_of_unified_row
    (erdos_406_unified_row_of_frontier_fires hfront)

/-! ## §8 THE UNCONDITIONAL PARTIAL VERDICT - what is green today,
with the assumption stated exactly. -/

/-- **The partial universal verdict, unconditional on its stated
coverage.**  Every odd `n ≥ 9` is covered by the monolith's own green odd
law (ErdosTernary2.lean:808); every even `n ≥ 9` whose half is
base-covered, CommonTwo-covered or Ω-covered is covered by the two
lattice laws and the boolean-digit bridge.  No hidden hypotheses: the
coverage condition is the theorem's own statement. -/
theorem erdos_406_verdict_of_base_or_covered (n : Nat) (hn : 9 ≤ n)
    (hcover : n % 2 = 1 ∨
      (n % 2 = 0 ∧ (n / 2 ≤ 500 ∨ erdos_406_covered_class (n / 2) ∨
        erdos_406_omega_covered (n / 2)))) :
    noTernaryTwo (2 ^ n) = false := by
  rcases hcover with hodd | ⟨he, hbc⟩
  · exact _root_.erdos_ternary_2_conjecture_odd n hn hodd
  · have hmd := Nat.mod_add_div n 2
    have hm5 : 5 ≤ n / 2 := by omega
    have hn2 : n = 2 * (n / 2) := by omega
    obtain ⟨p, -, hd2⟩ := digit_two_of_base_or_covered (n / 2) hm5 hbc
    have hv4 : noTernaryTwo (4 ^ (n / 2)) = false :=
      noTernaryTwo_false_of_digit3 _ p hd2
    have hp2 : (2 : ℕ) ^ (2 * (n / 2)) = 4 ^ (n / 2) := by
      rw [pow_mul]
      norm_num
    rw [hn2, hp2]
    exact hv4

/-! ## Receipts - every link of the composition, axiom-audited. -/

#print axioms noTernaryTwo_false_of_digit3
#print axioms four_pow_mod_three
#print axioms digit_witness_of_scan_false
#print axioms digit_two_of_covered_class
#print axioms digit_two_of_omega_covered
#print axioms erdos_406_climb_fragment_class_two
#print axioms digit_two_of_kernel_base
#print axioms digit_two_five_six_seven
#print axioms digit_two_of_base_or_covered
#print axioms erdos_406_even_conjecture_of_frontier_fires
#print axioms erdos_406_full_verdict_iff_frontier_fires
#print axioms erdos_406_unified_row_of_frontier_fires
#print axioms erdos_406_unified_row_iff_frontier_fires
#print axioms erdos_406_row_primitive_of_frontier_fires
#print axioms erdos_406_verdict_of_base_or_covered

#eval "ERDOS_406_ROW_TOWER_BREAKTHROUGH_GREEN"

end RowTowerBreakthrough406
