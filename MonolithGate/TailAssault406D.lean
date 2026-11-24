import MonolithGate.TailAssault406B

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE TAIL ASSAULT, FACE D — the tower origin kill

THE composition BOSS ordered, round four.  The monolith's own origin
law (`gst_navigation_origin`, CI-green in the vendored ErdosTernary2):
for every tower `4^(3^s * b)` with `s >= 1` and `b` not divisible by
three, the GST graph's origin vertex at row `s+1` carries carry NULL
and digit exactly `b % 3`.

THE KILL: when `b % 3 = 2` and `s >= 2`, the origin IS a quiet digit
two — carry zero, digit two — and the addition-carry chamber's digit
law hands the same digit two to the successor power `4^(K+1)`.  The
provider's green bridge converts the pair into the climb's physical
Happy row.  THE ENTIRE TOWER FAMILY `K = 3^s * b` (s >= 2, b % 3 = 2)
IS DEAD ABOVE EVERY BASE — unconditionally, at row `s+1` itself.

This family lies BEYOND the band lattice's horizon: every `K` with
`3^6 | K` sits in the survivor class `0` mod 729, which the level-six
table cannot kill.  The origin law kills it at every depth at once.

* **SECTION 20 THE DEFEQ BRIDGES** — the monolith's `gstCarry`/`gstDigit`
  are the carry chamber's `directCarry4`/`digit3` verbatim.
* **SECTION 21 THE TOWER ORIGIN KILL** — `climb_of_tower_origin`: the
  whole family, one row, three green theorems.
* **SECTION 22 THE SHARPENED VERDICT** — Erdos #406's universal verdict
  from the tail above the kernel base 3000, restricted to the non-tower
  exponents: the remaining hypothesis no longer quantifies over the
  tower family at all.

The engine never stops; it never lies.
-/

namespace GSTTailAssault406D

open GSTFourPowerDirectAdditionCarry

/-! ## SECTION 20 The defeq bridges -/

/-- **THE CARRY BRIDGE.**  The monolith's `gstCarry` is the addition-carry
chamber's `directCarry4` verbatim — one formula, two names, one world. -/
theorem gstCarry_eq_directCarry4 (R p : Nat) :
    gstCarry R p = GSTFourPowerDirectAdditionCarry.directCarry4 R p := rfl

/-- **THE DIGIT BRIDGE.**  The monolith's `gstDigit` is the residue
chamber's `digit3` verbatim. -/
theorem gstDigit_eq_digit3 (R p : Nat) :
    gstDigit R p = GSTFourPowerDirectResidue.digit3 R p := rfl

/-! ## SECTION 21 The tower origin kill -/

/-- **THE TOWER ORIGIN KILL.**  Every tower exponent `K = 3^s * b` with
`s >= 2` and cofactor `b ≡ 2 (mod 3)` owns its physical Happy row at
row `s+1` outright: the origin law's NULL-carry digit two, the
addition-carry chamber's digit law for the successor power, and the
provider's green bridge — three green theorems, one dead family.  This
family includes every `K` divisible by 729 (the survivor class zero of
the level-six band table), killed at every tower depth at once. -/
theorem climb_of_tower_origin (s b : Nat) (hs : 2 ≤ s) (hb : 1 ≤ b)
    (hb2 : b % 3 = 2) :
    ∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(3^s * b)) p)
        (GSTCanonicalTailStateIso.digit3 (4^(3^s * b)) p) := by
  have hb3 : b % 3 ≠ 0 := by
    rw [hb2]
    decide
  have horig := gst_navigation_origin s b (by omega) hb hb3
  have hd : GSTFourPowerDirectResidue.digit3 (4^(3^s * b)) (s+1) = 2 := by
    rw [← gstDigit_eq_digit3, horig.1, hb2]
  have hcarry :
      GSTFourPowerDirectAdditionCarry.directCarry4 (4^(3^s * b)) (s+1) = 0 := by
    rw [← gstCarry_eq_directCarry4, horig.2]
  have hmul := GSTFourPowerDirectAdditionCarry.digit3_four_mul
    (4^(3^s * b)) (s+1)
  rw [hd, hcarry] at hmul
  have hd' : GSTFourPowerDirectResidue.digit3 (4^((3^s * b)+1)) (s+1) = 2 := by
    simpa [pow_succ, Nat.mul_comm] using hmul
  exact ⟨s+1, by omega,
    GSTFourPowerHappyProvider.commonTwoAt_ge_three_to_physical_happy
      (3^s * b) (s+1) (by omega) hd hd'⟩

/-! ## SECTION 22 The sharpened verdict — the tower family is out -/

/-- **THE THREE-ADIC SHAPE.**  Every natural number factors as `3^s * b`
with `b` either zero or not divisible by three — the tower
decomposition, by strong recursion (the monolith's own green idiom). -/
theorem exists_three_shape (K : Nat) :
    ∃ s b, K = 3^s * b ∧ (b = 0 ∨ ¬ 3 ∣ b) := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
    rcases Nat.eq_zero_or_pos K with hK0 | hK1
    · exact ⟨0, 0, by rw [hK0, Nat.pow_zero], Or.inl rfl⟩
    · by_cases h3 : 3 ∣ K
      · obtain ⟨m, hm⟩ := h3
        have hmlt : m < K := by omega
        obtain ⟨s, b, hsb, hbshape⟩ := ih m hmlt
        refine ⟨s+1, b, ?_, hbshape⟩
        rw [hm, hsb, Nat.pow_succ]
        ring
      · exact ⟨0, K, by simp, Or.inr h3⟩

/-- **THE SHARPENED VERDICT, TOWER-FREE.**  Erdos #406's universal
verdict from the tail above the kernel base 3000, quantified only over
the NON-TOWER exponents: every exponent whose three-adic shape is a
tower of height at least two with cofactor two mod three is already
dead by the origin kill.  The remaining hypothesis — the single named
content of the problem — no longer sees the tower family at all. -/
theorem erdos406_universal_verdict_of_tail_3000_non_tower
    (htail : ∀ K : Nat, 3000 < K →
      ¬ (∃ s b, 2 ≤ s ∧ 1 ≤ b ∧ b % 3 = 2 ∧ K = 3^s * b) →
      ∃ p : Nat, 3 ≤ p ∧
        GSTCanonicalTailStateIso.HappyCell
          (GSTCanonicalTailStateIso.carry4 (4^K) p)
          (GSTCanonicalTailStateIso.digit3 (4^K) p)) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  refine erdos406_universal_verdict_of_climb (fun K hK8 => ?_)
  rcases Nat.lt_or_ge K 3001 with hbase | hK
  · exact GSTTailAssault406B.erdos406_climb_base_3000 K hK8 (by omega)
  · by_cases hT : ∃ s b, 2 ≤ s ∧ 1 ≤ b ∧ b % 3 = 2 ∧ K = 3^s * b
    · obtain ⟨s, b, hs, hb1, hb2, hKsb⟩ := hT
      rw [hKsb]
      exact climb_of_tower_origin s b hs hb1 hb2
    · exact htail K (by omega) hT

/-! ## SECTION 23 Receipts -/

#print axioms gstCarry_eq_directCarry4
#print axioms gstDigit_eq_digit3
#print axioms climb_of_tower_origin
#print axioms exists_three_shape
#print axioms erdos406_universal_verdict_of_tail_3000_non_tower

#eval "TAIL_ASSAULT_D_GREEN"

end GSTTailAssault406D
