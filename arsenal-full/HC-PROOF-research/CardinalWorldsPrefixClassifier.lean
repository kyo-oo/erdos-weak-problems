import Mathlib
import CardinalWorldsV2
import GSTFourPowerExponentTritObstruction

/-!
# CARDINAL WORLDS PREFIX CLASSIFIER

The old Cardinal Worlds proof contains separate mod-9, mod-27 and mod-81
signature certificates.  The direct exponent-trit machinery proves a much
stronger local law at every ternary exponent position.

This file lifts that local law to an exact global classifier for the
presence of a ternary digit 2 in 4^K.

Thus the finite congruence ladder becomes a collection of shallow
certificates for one arbitrary-depth prefix theorem.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace CardinalWorldsPrefixClassifier

open CardinalWorldsV2
open GSTFourPowerDirectResidue
open GSTFourPowerExponentTritObstruction

/-- The least ternary digit of every power of four is 1, so a digit-two
witness always occurs strictly above row zero. -/
theorem four_pow_digit_zero (K : Nat) :
    digit3 (4^K) 0 = 1 := by
  unfold digit3
  simp only [Nat.pow_zero, Nat.div_one]
  rw [Nat.pow_mod]
  norm_num

/-- Root-level Cardinal Worlds digit reading is definitionally the direct
ternary digit reader. -/
theorem gstDigit_eq_digit3 (R p : Nat) :
    gstDigit R p = digit3 R p := by
  rfl

/-- Exact witness form of the Boolean signature scan for powers of four. -/
theorem four_pow_has_two_iff_digit_witness (K : Nat) :
    hasTernaryTwo (4^K) = true ↔
      ∃ q : Nat, digit3 (4^K) q = 2 := by
  constructor
  · intro h
    obtain ⟨q,hq⟩ := hasTernaryTwo_pos (4^K) h
    exact ⟨q, hq⟩
  · rintro ⟨q,hq⟩
    exact hasTernaryTwo_of_digit (4^K) q hq

/-- **ARBITRARY-DEPTH EXPONENT-PREFIX CLASSIFIER.**

A power 4^K contains a ternary digit 2 iff at some exponent position p,
the p-th exponent trit shifts the row-(p+1) digit of the low exponent
prefix into 2.

There is no fixed modulus and no finite list of exponent classes. -/
theorem four_pow_has_two_iff_prefix_trit (K : Nat) :
    hasTernaryTwo (4^K) = true ↔
      ∃ p : Nat,
        (digit3 (4^(exponentPrefix K p)) (p+1)
          + exponentTrit K p) % 3 = 2 := by
  constructor
  · intro h
    obtain ⟨q,hq⟩ :=
      (four_pow_has_two_iff_digit_witness K).mp h
    have hqpos : 0 < q := by
      by_contra h0
      have hq0 : q = 0 := by omega
      subst q
      rw [four_pow_digit_zero K] at hq
      omega
    let p := q - 1
    have hqeq : q = p + 1 := by
      dsimp [p]
      omega
    refine ⟨p, ?_⟩
    rw [← pow4_digit_from_exponent_trit K p]
    simpa [hqeq] using hq
  · rintro ⟨p,hp⟩
    apply (four_pow_has_two_iff_digit_witness K).2
    refine ⟨p+1, ?_⟩
    rw [pow4_digit_from_exponent_trit K p]
    exact hp

/-- One chosen prefix fire is sufficient to trigger the global signature. -/
theorem prefix_fire_implies_has_two
    (K p : Nat)
    (hfire :
      (digit3 (4^(exponentPrefix K p)) (p+1)
        + exponentTrit K p) % 3 = 2) :
    hasTernaryTwo (4^K) = true := by
  exact (four_pow_has_two_iff_prefix_trit K).2 ⟨p,hfire⟩

/-- Every global signature exposes at least one firing exponent prefix. -/
theorem has_two_exposes_prefix_fire
    (K : Nat) (h : hasTernaryTwo (4^K) = true) :
    ∃ p : Nat,
      (digit3 (4^(exponentPrefix K p)) (p+1)
        + exponentTrit K p) % 3 = 2 := by
  exact (four_pow_has_two_iff_prefix_trit K).1 h

/-- The signature-free condition is an all-prefix obstruction. -/
theorem four_pow_signature_free_iff_all_prefixes_avoid
    (K : Nat) :
    hasTernaryTwo (4^K) = false ↔
      ∀ p : Nat,
        (digit3 (4^(exponentPrefix K p)) (p+1)
          + exponentTrit K p) % 3 ≠ 2 := by
  constructor
  · intro h p hp
    have htrue : hasTernaryTwo (4^K) = true :=
      prefix_fire_implies_has_two K p hp
    rw [h] at htrue
    contradiction
  · intro hall
    cases hscan : hasTernaryTwo (4^K) with
    | false => rfl
    | true =>
        obtain ⟨p,hp⟩ :=
          has_two_exposes_prefix_fire K hscan
        exact absurd hp (hall p)

/-- The old finite congruence cases now sit below one exact all-depth
classifier rather than defining the architecture. -/
theorem prefix_classifier_crown (K : Nat) :
    (hasTernaryTwo (4^K) = true ↔
      ∃ p : Nat,
        (digit3 (4^(exponentPrefix K p)) (p+1)
          + exponentTrit K p) % 3 = 2)
    ∧
    (hasTernaryTwo (4^K) = false ↔
      ∀ p : Nat,
        (digit3 (4^(exponentPrefix K p)) (p+1)
          + exponentTrit K p) % 3 ≠ 2) :=
  ⟨four_pow_has_two_iff_prefix_trit K,
    four_pow_signature_free_iff_all_prefixes_avoid K⟩

#check four_pow_digit_zero
#check four_pow_has_two_iff_digit_witness
#check four_pow_has_two_iff_prefix_trit
#check prefix_fire_implies_has_two
#check has_two_exposes_prefix_fire
#check four_pow_signature_free_iff_all_prefixes_avoid
#check prefix_classifier_crown

#print axioms four_pow_has_two_iff_prefix_trit
#print axioms four_pow_signature_free_iff_all_prefixes_avoid
#print axioms prefix_classifier_crown

end CardinalWorldsPrefixClassifier
