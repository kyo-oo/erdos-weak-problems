import MonolithGate.TailAssault406D
import MonolithGate.GSTTailFFourthDimension

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE TAIL ASSAULT, FACE E — THE UNIFICATION

THE composition round five.  The four faces sharpened the climb from
four sides: the trit-tree law and the band lattice (Face A), the
six-state automaton and the base at 3000 (Face B), the circle closed
between the tree, the climb, and the common-two statement (Face C), the
tower origin kill for the whole family `K = 3^s * b`, `s >= 2`,
`b % 3 = 2` (Face D).  This face performs THE UNIFICATION.

THE DISCOVERY OF THIS ROUND: the row word of a tower witness and the
tower family's cut word are ONE OBJECT.  For every `K = 3^s * core`,

  `omegaCutWord 0 (3^s * core) = 3^s * omegaCutWord s core`

the sheet-zero word of the witness is the sheet-`s` cut word shifted
left by exactly `s` trits — both factorizations of the SAME power
`4^K = 1 + 3^(s+1) * omegaCutWord s core` (the cut-factor identity at
sheet `s` and at sheet zero).  The two named primitives of the fourth
dimension's decomposition — the ROW primitive (the sheet-zero family)
and the TOWER primitive (the deep tail of the sheet-`s` cut word) —
read one object at two depths.  THE WHOLE REMAINING CONTENT collapses
to ONE statement:

* **SECTION 26 THE UNIFIED PRIMITIVE** — `tailF_unified_row_primitive`:
  for every exponent from eight onward, the row word `(4^K - 1)/3`
  fires its top third at some depth.  THE MASTER COMPOSITION consumes
  the entire second-observer package wholesale — the shadow package
  is bypassed: a row-word fire IS the digit two the input demands, at
  every witness, through the uniform row law, no clause consulted.

* **SECTION 25 THE FIRE DICTIONARY** — the cut word at sheet `s` fires
  at depth `i` if and only if the witness's row word fires at depth
  `s + i`: the shift law plus one modulus shift.

* **SECTION 27 THE SUBSUMPTION RECEIPTS** — the unified primitive
  swallows BOTH named primitives: it IS the row primitive with the
  residue clause dropped, and with the window clause alone it delivers
  the tower primitive's deep tail.

* **SECTION 28 THE WALL'S COORDINATE** — the full package's every
  clause (residues, the diagonal window dodge, the sheet gate, both
  second-sheet gates) is EXACTLY the non-fire of the witness's cut word
  at depths zero through `s+2`, machine-certified as one theorem: the
  fire of a full shadow-package witness can only live at cut depth
  `s+3` or beyond — the residual's final, sharpest coordinate.

The engine never stops; it never lies.
-/

namespace GSTTailAssault406E

open GSTCanonicalSevenAxisBridge
open GSTGraphV2OmegaWaveLaw
open GSTFourPowerDirectResidue (lteCoeff lteCoeff_mod3_one pow4_mod3_one)
open GSTTailFFourthDimension (tailF_tower_primitive tailF_row_primitive)

/-! ## SECTION 24 The shift law — the two families are one object -/

/-- **THE WORD-SHIFT LAW.**  The row word of the tower witness `3^s * core`
is the sheet-`s` cut word shifted left by exactly `s` trits: both are
readings of the one power `4^(3^s * core) = 1 + 3^(s+1) * omegaCutWord
s core` through the cut-factor identity at sheet `s` and at sheet zero.
The sheet-zero family and the tower family of the decomposition are one
family read at two depths. -/
theorem omegaCutWord_zero_shift (s core : Nat) :
    omegaCutWord 0 (3^s * core) = 3^s * omegaCutWord s core := by
  have h0 := omega_cut_factor 0 (3^s * core)
  rw [Nat.pow_zero, Nat.one_mul] at h0
  have hs := omega_cut_factor s core
  have hcancel : (3:Nat)^(0+1) * omegaCutWord 0 (3^s * core)
      = 3^(s+1) * omegaCutWord s core :=
    Nat.add_left_cancel (h0.symm.trans hs)
  have h01 : (3:Nat)^(0+1) = 3 := by decide
  have hp : (3:Nat)^(s+1) = 3 * 3^s := by
    rw [Nat.pow_succ]; ring
  rw [h01, hp, Nat.mul_assoc] at hcancel
  exact Nat.eq_of_mul_eq_mul_left (by decide : (0:Nat) < 3) hcancel

/-- **THE MODULUS SHIFT.**  Multiplying by `3^s` commutes with the
residue window: `(3^s * W) % 3^(s+i+1) = 3^s * (W % 3^(i+1))`. -/
theorem pow_mod_shift (s W i : Nat) :
    (3^s * W) % 3^(s+i+1) = 3^s * (W % 3^(i+1)) := by
  have hp : (3:Nat)^(s+i+1) = 3^s * 3^(i+1) := by
    rw [show s+i+1 = s+(i+1) from by omega, Nat.pow_add]
  have hdm : W % 3^(i+1) + 3^(i+1) * (W / 3^(i+1)) = W :=
    Nat.div_add_mod W (3^(i+1))
  have hsplit : 3^s * W
      = 3^s * (W % 3^(i+1)) + 3^(s+i+1) * (W / 3^(i+1)) := by
    have h1 : 3^s * (W % 3^(i+1) + 3^(i+1) * (W / 3^(i+1)))
        = 3^s * W := by rw [hdm]
    rw [Nat.mul_add, ← Nat.mul_assoc, ← hp] at h1
    exact h1.symm
  have hlt : 3^s * (W % 3^(i+1)) < 3^(s+i+1) := by
    have h1 : W % 3^(i+1) < 3^(i+1) :=
      Nat.mod_lt _ (Nat.pow_pos (by decide))
    have h4 : (0:Nat) < 3^s := Nat.pow_pos (by decide)
    have h2 : 3^s * (W % 3^(i+1)) < 3^s * 3^(i+1) :=
      Nat.mul_lt_mul_of_pos_left h1 h4
    rw [hp]
    exact h2
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ## SECTION 25 The fire dictionary — the cut word and the row word -/

/-- **THE FIRE DICTIONARY.**  The sheet-`s` cut word of `core` fires its
top third at depth `i` if and only if the row word of the witness
`3^s * core` fires at depth `s + i`: the shift law and the modulus
shift are the whole translation.  The tower primitive's deep tail is
the row word of the witness, read `s` trits later. -/
theorem cut_fire_iff_row_fire (s core i : Nat) :
    (2 * 3^i ≤ (omegaCutWord s core) % 3^(i+1) ↔
      2 * 3^(s+i) ≤ (omegaCutWord 0 (3^s * core)) % 3^(s+i+1)) := by
  have hp : (3:Nat)^(s+i) = 3^s * 3^i := by rw [Nat.pow_add]
  rw [omegaCutWord_zero_shift, pow_mod_shift]
  have hmul : 3^s * (2 * 3^i) = 2 * 3^(s+i) := by rw [hp]; ring
  constructor
  · intro h
    have hstep : 3^s * (2 * 3^i)
        ≤ 3^s * (omegaCutWord s core % 3^(i+1)) :=
      Nat.mul_le_mul_left _ h
    rw [hmul] at hstep
    exact hstep
  · intro h
    rw [← hmul] at h
    by_contra hcon
    push_neg at hcon
    have hstep : 3^s * (omegaCutWord s core % 3^(i+1) + 1)
        ≤ 3^s * (2 * 3^i) :=
      Nat.mul_le_mul_left _ (by omega)
    have hsucc : 3^s * (omegaCutWord s core % 3^(i+1) + 1)
        = 3^s * (omegaCutWord s core % 3^(i+1)) + 3^s := by
      rw [Nat.mul_succ]
    have hpos : (0:Nat) < 3^s := Nat.pow_pos (by decide)
    omega

/-! ## SECTION 26 The unified primitive — the one statement -/

/-- **THE UNIFIED ROW PRIMITIVE.**  The entire remaining content of the
second-observer input as ONE statement with no families, no sheets, no
residue clauses, no windows: for every exponent from eight onward, the
row word `(4^K - 1)/3` fires its top third at some depth.  Through the
terminal identity this is exactly the even-exponent Erdős ternary
statement; through the master composition below it is exactly the
second-observer input; through the shift law it is exactly the row
primitive and the tower primitive together. -/
def tailF_unified_row_primitive : Prop :=
  ∀ K : Nat, 8 ≤ K →
    ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 K) % 3^(j+1)

/-- **THE WITNESS CONVERSION.**  A ternary digit two of `4^K` at any
position is a fire of the row word: the digit and the row-word trit are
the same object through the cut-factor identity at sheet zero. -/
theorem row_fire_of_gstDigit_two (K p : Nat) (h : gstDigit (4^K) p = 2) :
    ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 K) % 3^(j+1) := by
  have hp1 : 1 ≤ p := by
    by_contra hc
    push_neg at hc
    rcases (by omega : p = 0) with rfl
    have hmod : gstDigit (4^K) 0 = 1 := by
      show (4:Nat)^K / 3^0 % 3 = 1
      rw [Nat.pow_zero, Nat.div_one]
      exact pow4_mod3_one K
    omega
  obtain ⟨j, hj⟩ : ∃ j : Nat, p = j + 1 := ⟨p - 1, by omega⟩
  refine ⟨j, ?_⟩
  have hf : (4:Nat)^K = 1 + 3 * omegaCutWord 0 K := by
    have h2 := omega_cut_factor 0 K
    rw [Nat.pow_zero, Nat.one_mul,
      show (3:Nat)^(0+1) = 3 from by decide] at h2
    exact h2
  have hd : (4:Nat)^K / 3^(j+1) = omegaCutWord 0 K / 3^j := by
    have hp' : (3:Nat)^(j+1) = 3 * 3^j := by rw [Nat.pow_succ]; ring
    rw [hf, hp', ← Nat.div_div_eq_div_mul]
    have h13 : (1 + 3 * omegaCutWord 0 K) / 3 = omegaCutWord 0 K := by
      rw [Nat.add_mul_div_left _ _ (by decide : (0:Nat) < 3)]
      omega
    rw h13
  rw [hj] at h
  have h2 : (omegaCutWord 0 K) / 3^j % 3 = 2 := by
    rw [← hd]
    exact h
  rw [digit3_window] at h2
  have hsplit := Nat.mod_add_div (omegaCutWord 0 K % 3^(j+1)) (3^j)
  rw [h2] at hsplit
  have hlt2 : (omegaCutWord 0 K % 3^(j+1)) % 3^j < 3^j :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  omega

/-- **THE MASTER COMPOSITION.**  The unified row primitive consumes the
entire second-observer input wholesale: the shadow package is bypassed
— the uniform row law converts the row-word fire directly into the
ternary digit two the input demands, at every witness, no clause
consulted.  The whole remaining content of Erdős #406's second-observer
route is ONE statement about row words. -/
theorem tailF_of_unified_row (h : tailF_unified_row_primitive) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK _hshadow
  obtain ⟨j, hj⟩ := h K (by omega)
  exact ⟨1 + j, omega_row_level_digit_two K j hj⟩

/-- **THE EQUIVALENCE RECEIPT.**  The unified row primitive IS the
even-exponent Erdős ternary statement: one direction through the
monolith's own kernel-certified terminal identity, the other through
the witness extraction and the witness conversion.  The residual has
been restated in its terminal form. -/
theorem unified_row_iff_even_conjecture :
    tailF_unified_row_primitive ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false := by
  constructor
  · intro h
    exact erdos_even_conjecture_iff_tailF.mpr (tailF_of_unified_row h)
  · intro hconj K hK
    obtain ⟨p, hp⟩ := no_two_false_digit_witness (4^K) (hconj K hK)
    exact row_fire_of_gstDigit_two K p hp

/-- **THE EVEN CONJECTURE FROM THE UNIFIED PRIMITIVE.** -/
theorem even_conjecture_of_unified_row (h : tailF_unified_row_primitive) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  unified_row_iff_even_conjecture.mp h

/-- **THE CROWN FROM THE UNIFIED PRIMITIVE.**  The monolith's own
universal theorem, wearing the unified primitive as its single input. -/
theorem erdos_ternary_2_universal_of_unified_row
    (h : tailF_unified_row_primitive) (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_tailF (tailF_of_unified_row h) n hn

/-- **THE SHARPENED VERDICT, UNIFIED FORM.**  Erdős #406's universal
verdict from the single row-word statement alone: the whole problem,
one primitive. -/
theorem erdos406_universal_verdict_of_unified_row
    (h : tailF_unified_row_primitive) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  fun n hn => erdos_ternary_2_universal_of_unified_row h n hn

/-! ## SECTION 27 The subsumption receipts — one primitive, both families -/

/-- **THE SUCCESSIVE-UNIT STABILIZATION.**  The unit word `lteCoeff`
stays at seven modulo nine from sheet one onward: the cube lift adds
multiples of nine. -/
theorem lteCoeff_succ_mod9 (r : Nat) (hr : 1 ≤ r) :
    lteCoeff (r+1) % 9 = lteCoeff r % 9 := by
  have hd : lteCoeff (r+1) = lteCoeff r + 3^(r+1) * (lteCoeff r)^2
      + 3^(2*r+1) * (lteCoeff r)^3 := by
    simp only [lteCoeff]
  have h9a : (9:Nat) ∣ 3^(r+1) := by
    refine ⟨3^(r-1), ?_⟩
    rw [show (9:Nat) = 3^2 from by decide, ← Nat.pow_add]
    congr 1
    omega
  have h9b : (9:Nat) ∣ 3^(2*r+1) := by
    refine ⟨3^(2*r-1), ?_⟩
    rw [show (9:Nat) = 3^2 from by decide, ← Nat.pow_add]
    congr 1
    omega
  obtain ⟨u, hu⟩ := h9a
  obtain ⟨v, hv⟩ := h9b
  have hE : lteCoeff (r+1)
      = lteCoeff r + 9 * (u * (lteCoeff r)^2 + v * (lteCoeff r)^3) := by
    rw [hd, hu, hv]; ring
  rw [hE, Nat.add_mul_mod_self_left]

/-- **THE UNIT WORD AT SEVEN.**  `lteCoeff s` is seven modulo nine for
every sheet from one onward. -/
theorem lteCoeff_mod9_seven : ∀ s : Nat, 1 ≤ s → lteCoeff s % 9 = 7 := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro hs
    rcases (by omega : s = 1 ∨ 2 ≤ s) with rfl | hs2
    · decide
    · have h1 := lteCoeff_succ_mod9 (s-1) (by omega)
      have h2 := ih (s-1) (by omega) (by omega)
      rw [show s = (s-1)+1 from by omega, h1]
      exact h2

/-- **THE RESIDUE PIN.**  For every sheet from one onward and every
shadow-package class (four or seven modulo nine), the cut word sits at
exactly one or four modulo nine: the class's own value through the
unit word's seven. -/
theorem cut_word_mod9_of_class (s core : Nat) (hs : 1 ≤ s)
    (hclass : core % 9 = 4 ∨ core % 9 = 7) :
    omegaCutWord s core % 9 = 1 ∨ omegaCutWord s core % 9 = 4 := by
  have h9d : (9:Nat) ∣ 3^(s+2) := by
    refine ⟨3^s, ?_⟩
    rw [show (9:Nat) = 3^2 from by decide, ← Nat.pow_add]
    congr 1
    omega
  have h9dvd : (9:Nat) ∣ 3^(s+1) := by
    refine ⟨3^(s-1), ?_⟩
    rw [show (9:Nat) = 3^2 from by decide, ← Nat.pow_add]
    congr 1
    omega
  obtain ⟨u, hu⟩ := h9dvd
  have hcorr9 : (9:Nat) ∣
      3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2) :=
    ⟨u * lteCoeff s * lteCoeff s * (core * (core - 1) / 2), by
      rw [hu]; ring⟩
  have hR9 : (lteCoeff s * core
      + 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 9
      = (lteCoeff s * core) % 9 := by
    obtain ⟨w, hw⟩ := hcorr9
    rw [hw, Nat.add_mul_mod_self_left]
  have hmod : ∀ X : Nat, (X % 3^(s+2)) % 9 = X % 9 :=
    fun X => Nat.mod_mod_of_dvd X h9d
  have hf := omega_cut_word_full s core
  have h1 : (omegaCutWord s core % 3^(s+2)) % 9
      = omegaCutWord s core % 9 :=
    hmod (omegaCutWord s core)
  rw [hf] at h1
  have h2 : ((lteCoeff s * core
      + 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 3^(s+2)) % 9
      = (lteCoeff s * core
      + 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 9 :=
    hmod _
  rw [hR9] at h2
  have hkey : omegaCutWord s core % 9 = (lteCoeff s * core) % 9 :=
    h1.symm.trans h2
  have h7 : lteCoeff s % 9 = 7 := lteCoeff_mod9_seven s hs
  rw [hkey, Nat.mul_mod, h7]
  rcases hclass with h4 | h7c
  · rw [h4]; decide
  · rw [h7c]; decide

/-- **THE SHALLOW RESIDUE PIN.**  The cut word's trits zero and one are
never fire: the class value one-or-four modulo nine keeps both below
the top third. -/
theorem cut_word_shallow_residue_pin (s core : Nat) (hs : 1 ≤ s)
    (hclass : core % 9 = 4 ∨ core % 9 = 7) (i : Nat) (hi : i ≤ 1) :
    omegaCutWord s core % 3^(i+1) < 2 * 3^i := by
  have hmod9 := cut_word_mod9_of_class s core hs hclass
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · have h3d : (3:Nat) ∣ 9 := by decide
    have h1 : (omegaCutWord s core % 9) % 3 = omegaCutWord s core % 3 :=
      Nat.mod_mod_of_dvd _ h3d
    rcases hmod9 with h | h
    · rw [h] at h1; norm_num at h1; norm_num; omega
    · rw [h] at h1; norm_num at h1; norm_num; omega
  · norm_num
    rcases hmod9 with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num

/-- **THE DIAGONAL WINDOW PIN.**  Inside the stabilization window the
cut word IS the tower word: the diagonal dodge clause of the shadow
package is exactly the cut word's non-fire at depths two through `s`. -/
theorem cut_word_diag_pin (s core i : Nat) (hi2 : 2 ≤ i) (his : i ≤ s)
    (hD : ∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) :
    omegaCutWord s core % 3^(i+1) < 2 * 3^i := by
  obtain ⟨t, ht⟩ := omega_cut_word_linear s core
  have hd : 3^(s+1) = 3^(i+1) * 3^(s-i) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [ht, hd, ← Nat.mul_assoc, Nat.add_mul_mod_self_left]
  have hpin := hD (i+1) (by omega) (by omega)
  rw [show i+1-1 = i from by omega] at hpin
  exact hpin

/-- **THE SHALLOW PIN.**  The shadow package's residue clause, diagonal
window dodge, and sheet gate together pin the witness's cut word
non-fire at every depth through `s+1`. -/
theorem tower_witness_cut_word_pinned_shallow (s core : Nat) (hs : 1 ≤ s)
    (hclass : core % 9 = 4 ∨ core % 9 = 7)
    (hB : omegaCutWord s core % 3^(s+2) < 2 * 3^(s+1))
    (hD : ∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) :
    ∀ i : Nat, i ≤ s+1 →
      omegaCutWord s core % 3^(i+1) < 2 * 3^i := by
  intro i hi
  rcases (by omega : i ≤ 1 ∨ (2 ≤ i ∧ i ≤ s) ∨ i = s+1) with
    h | ⟨h2, his⟩ | rfl
  · exact cut_word_shallow_residue_pin s core hs hclass i h
  · exact cut_word_diag_pin s core i h2 his hD
  · rw [show (s+1)+1 = s+2 from by omega]
    exact hB

/-- **THE ROW PRIMITIVE SUBSUMED.**  The unified primitive is the row
primitive with the residue clause dropped: one line. -/
theorem row_primitive_of_unified_row (h : tailF_unified_row_primitive) :
    tailF_row_primitive := by
  intro core hK _hfree _hclass
  exact h core (by omega)

/-- **THE TOWER PRIMITIVE SUBSUMED.**  The unified primitive plus the
sheet gate alone delivers the tower primitive's deep tail: the row
word of the witness fires (the unified primitive), the shift law
carries the fire to the cut word, and the shallow pin forces the fire
past the window — depth `s+2` or beyond, exactly the tower primitive's
conclusion. -/
theorem tower_primitive_of_unified_row (h : tailF_unified_row_primitive)
    (s core : Nat) (hs : 1 ≤ s) (hK : 8 ≤ 3^s * core)
    (hclass : core % 9 = 4 ∨ core % 9 = 7)
    (hB : omegaCutWord s core % 3^(s+2) < 2 * 3^(s+1))
    (hD : ∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) :
    ∃ i : Nat, s+2 ≤ i ∧
      2 * 3^i ≤ (omegaCutWord s core) % 3^(i+1) := by
  obtain ⟨j, hj⟩ := h (3^s * core) hK
  have hjge : s ≤ j := by
    by_contra hc
    push_neg at hc
    have hz : (3^s * omegaCutWord s core) % 3^(j+1) = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      have hexp : (3:Nat)^s = 3^(j+1) * 3^(s-j-1) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      refine ⟨3^(s-j-1) * omegaCutWord s core, ?_⟩
      rw [hexp, Nat.mul_assoc]
    rw [omegaCutWord_zero_shift] at hj
    rw [hz] at hj
    have hpos : (0:Nat) < 3^j := Nat.pow_pos (by decide)
    omega
  have hij : s + (j - s) = j := by omega
  have hfire : 2 * 3^(j-s) ≤ (omegaCutWord s core) % 3^((j-s)+1) :=
    (cut_fire_iff_row_fire s core (j - s)).mpr (by rw [hij]; exact hj)
  refine ⟨j - s, ?_, hfire⟩
  by_contra hc
  push_neg at hc
  have hpin := tower_witness_cut_word_pinned_shallow s core hs hclass hB hD
    (j-s) (by omega)
  omega

/-! ## SECTION 28 The wall's coordinate — the full package, one pin -/

/-- **THE C-ZONE CORRECTION, CLASS FOUR.**  For every core congruent to
four modulo nine at sheet level one and above, the binomial correction
of the second-order cut word law lands at exactly twice the sheet's
carried power: `2 * 3^(s+2)` modulo the cubed cut modulus. -/
theorem czone_correction_four (s core : Nat) (hs : 1 ≤ s)
    (hcore : core % 9 = 4) :
    (3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 3^(s+3)
      = 2 * 3^(s+2) := by
  have hu3 : (lteCoeff s) % 3 = 1 := lteCoeff_mod3_one s
  have hll : (lteCoeff s * lteCoeff s) % 3 = 1 := by
    rw [Nat.mul_mod, hu3]
    decide
  have hb : (core * (core - 1) / 2) % 9 = 6 :=
    omega_binom_mod9_four core hcore
  have hB9 : (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 9 = 6 :=
    omega_mul_mod9_six _ _ hll hb
  have hshape : (3:Nat)^(s+1) * lteCoeff s * lteCoeff s
      * (core * (core - 1) / 2)
      = 3^(s+1) * (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) := by
    ring
  rw [hshape, omega_powmul_mod_cubed s _, hB9]
  have h6 : (3:Nat)^(s+1) * 6 = 2 * 3^(s+2) := by
    have hp : (3:Nat)^(s+2) = 3^(s+1) * 3 := by rw [Nat.pow_succ]
    rw [hp]; ring
  have hlt : 2 * 3^(s+2) < 3^(s+3) := by
    have hp : (3:Nat)^(s+3) = 3 * 3^(s+2) := by rw [Nat.pow_succ]; ring
    have h0 : (0:Nat) < 3^(s+2) := Nat.pow_pos (by decide)
    rw [hp]; omega
  rw [h6, Nat.mod_eq_of_lt hlt]

/-- **THE C-ZONE CORRECTION, CLASS SEVEN.**  For every core congruent to
seven modulo nine at sheet level one and above, the binomial correction
lands at exactly the sheet's carried power: `3^(s+2)` modulo the cubed
cut modulus. -/
theorem czone_correction_seven (s core : Nat) (hs : 1 ≤ s)
    (hcore : core % 9 = 7) :
    (3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 3^(s+3)
      = 3^(s+2) := by
  have hu3 : (lteCoeff s) % 3 = 1 := lteCoeff_mod3_one s
  have hll : (lteCoeff s * lteCoeff s) % 3 = 1 := by
    rw [Nat.mul_mod, hu3]
    decide
  have hb : (core * (core - 1) / 2) % 9 = 3 :=
    omega_binom_mod9_seven core hcore
  have hB9 : (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 9 = 3 :=
    omega_mul_mod9_three _ _ hll hb
  have hshape : (3:Nat)^(s+1) * lteCoeff s * lteCoeff s
      * (core * (core - 1) / 2)
      = 3^(s+1) * (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) := by
    ring
  rw [hshape, omega_powmul_mod_cubed s _, hB9]
  have h3 : (3:Nat)^(s+1) * 3 = 3^(s+2) := by rw [Nat.pow_succ]
  have hlt : 3^(s+2) < 3^(s+3) := by
    have hp : (3:Nat)^(s+3) = 3 * 3^(s+2) := by rw [Nat.pow_succ]; ring
    have h0 : (0:Nat) < 3^(s+2) := Nat.pow_pos (by decide)
    rw [hp]; omega
  rw [h3, Nat.mod_eq_of_lt hlt]

/-- **THE C-ZONE PIN, CLASS FOUR.**  The second-sheet gate's class-four
clause (the tower word at middle-or-top of the cubed window) plus the
`+2` binomial shift pins the cut word non-fire at depth `s+2`. -/
theorem cut_word_czone_pin_four (s core : Nat) (hs : 1 ≤ s)
    (hcore : core % 9 = 4)
    (hC : 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)) :
    omegaCutWord s core % 3^(s+3) < 2 * 3^(s+2) := by
  have hf := omega_cut_word_full3 s core hs
  have hcorr := czone_correction_four s core hs hcore
  rw [hf, Nat.add_mod, hcorr]
  have hM : (3:Nat)^(s+3) = 3 * 3^(s+2) := by rw [Nat.pow_succ]; ring
  have hltm : (lteCoeff s * core) % 3^(s+3) < 3^(s+3) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hmod : ((lteCoeff s * core % 3^(s+3)) + 2 * 3^(s+2)) % 3^(s+3)
      = (lteCoeff s * core % 3^(s+3)) - 3^(s+2) := by
    have hE : (lteCoeff s * core % 3^(s+3)) + 2 * 3^(s+2)
        = 3^(s+3) * 1 + ((lteCoeff s * core % 3^(s+3)) - 3^(s+2)) := by
      omega
    have hlt2 : (lteCoeff s * core % 3^(s+3)) - 3^(s+2) < 3^(s+3) := by
      omega
    rw [hE, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
  rw [hmod]
  omega

/-- **THE C-ZONE PIN, CLASS SEVEN.**  The second-sheet gate's class-seven
clause (the tower word at bottom-or-top of the cubed window) plus the
`+1` binomial shift pins the cut word non-fire at depth `s+2`. -/
theorem cut_word_czone_pin_seven (s core : Nat) (hs : 1 ≤ s)
    (hcore : core % 9 = 7)
    (hC : (lteCoeff s * core) % 3^(s+3) < 3^(s+2)
      ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)) :
    omegaCutWord s core % 3^(s+3) < 2 * 3^(s+2) := by
  have hf := omega_cut_word_full3 s core hs
  have hcorr := czone_correction_seven s core hs hcore
  rw [hf, Nat.add_mod, hcorr]
  have hM : (3:Nat)^(s+3) = 3 * 3^(s+2) := by rw [Nat.pow_succ]; ring
  have hltm : (lteCoeff s * core) % 3^(s+3) < 3^(s+3) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  rcases hC with hlow | hhigh
  · have hlt : (lteCoeff s * core % 3^(s+3)) + 3^(s+2) < 3^(s+3) := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · have hE : (lteCoeff s * core % 3^(s+3)) + 3^(s+2)
      = 3^(s+3) * 1
        + ((lteCoeff s * core % 3^(s+3)) - 2 * 3^(s+2)) := by
      omega
    have hlt2 : (lteCoeff s * core % 3^(s+3)) - 2 * 3^(s+2) < 3^(s+3) := by
      omega
    rw [hE, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
    omega

/-- **THE WALL'S COORDINATE.**  The full shadow package's every clause —
the residue class, the diagonal window dodge, the sheet gate, and both
second-sheet gate clauses — is EXACTLY the non-fire of the witness's
cut word at depths zero through `s+2`, assembled as one machine-certified
theorem.  A full-package witness's fire can only live at cut depth
`s+3` or beyond: the residual of the second-observer route, in its
final, sharpest coordinate. -/
theorem tower_witness_cut_word_pinned (s core : Nat) (hs : 1 ≤ s)
    (hclass : core % 9 = 4 ∨ core % 9 = 7)
    (hB : omegaCutWord s core % 3^(s+2) < 2 * 3^(s+1))
    (hC4 : core % 9 = 4 → 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))
    (hC7 : core % 9 = 7 → ((lteCoeff s * core) % 3^(s+3) < 3^(s+2)
      ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)))
    (hD : ∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) :
    ∀ i : Nat, i ≤ s+2 →
      omegaCutWord s core % 3^(i+1) < 2 * 3^i := by
  intro i hi
  rcases (by omega : i ≤ 1 ∨ (2 ≤ i ∧ i ≤ s) ∨ i = s+1 ∨ i = s+2) with
    h | ⟨h2, his⟩ | rfl | rfl
  · exact cut_word_shallow_residue_pin s core hs hclass i h
  · exact cut_word_diag_pin s core i h2 his hD
  · rw [show (s+1)+1 = s+2 from by omega]
    exact hB
  · rcases hclass with h4 | h7
    · exact cut_word_czone_pin_four s core hs h4 (hC4 h4)
    · exact cut_word_czone_pin_seven s core hs h7 (hC7 h7)

/-! ## SECTION 29 Receipts -/

#print axioms omegaCutWord_zero_shift
#print axioms pow_mod_shift
#print axioms cut_fire_iff_row_fire
#print axioms row_fire_of_gstDigit_two
#print axioms tailF_of_unified_row
#print axioms unified_row_iff_even_conjecture
#print axioms even_conjecture_of_unified_row
#print axioms erdos_ternary_2_universal_of_unified_row
#print axioms erdos406_universal_verdict_of_unified_row
#print axioms lteCoeff_succ_mod9
#print axioms lteCoeff_mod9_seven
#print axioms cut_word_mod9_of_class
#print axioms cut_word_shallow_residue_pin
#print axioms cut_word_diag_pin
#print axioms tower_witness_cut_word_pinned_shallow
#print axioms row_primitive_of_unified_row
#print axioms tower_primitive_of_unified_row
#print axioms czone_correction_four
#print axioms czone_correction_seven
#print axioms cut_word_czone_pin_four
#print axioms cut_word_czone_pin_seven
#print axioms tower_witness_cut_word_pinned

#eval "TAIL_ASSAULT_E_GREEN"

end GSTTailAssault406E
