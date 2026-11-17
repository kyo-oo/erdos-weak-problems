import Mathlib
import CardinalWorlds

/-!
# CARDINAL WORLDS V2 — EXACT READER DUALITY AND COMPOSITION

This layer strengthens the core Cardinal Worlds interfaces without altering
their finite arithmetic content.  Separate case lemmas are compressed into
exact equivalences and compositional parent laws.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace CardinalWorldsV2


/-- The positive signature reader and the negative Cantor verdict are exact
Boolean complements at the true/false level. -/
theorem has_two_iff_no_two_false (n : Nat) :
    hasTernaryTwo n = true ↔ noTernaryTwo n = false := by
  constructor
  · exact has_two_imp_not_no_two n
  · intro h
    obtain ⟨p,hp⟩ := no_two_false_digit_witness n h
    exact hasTernaryTwo_of_digit n p hp

/-- The scan is true exactly when a first digit-two position exists with
minimality. -/
theorem has_two_iff_first_signature (n : Nat) :
    hasTernaryTwo n = true ↔
      ∃ q : Nat,
        n / 3^q % 3 = 2 ∧
        ∀ p, p < q → n / 3^p % 3 ≠ 2 := by
  constructor
  · exact hasTernaryTwo_first_pos n
  · rintro ⟨q,hq,hmin⟩
    exact hasTernaryTwo_of_digit n q hq

/-- The failed Cantor verdict is exactly the existence of a digit-two
position. -/
theorem no_two_false_iff_digit_witness (n : Nat) :
    noTernaryTwo n = false ↔
      ∃ p : Nat, gstDigit n p = 2 := by
  constructor
  · exact no_two_false_digit_witness n
  · rintro ⟨p,hp⟩
    exact (has_two_iff_no_two_false n).mp
      (hasTernaryTwo_of_digit n p hp)

/-- The three separate residue-one carry lemmas collapse to one exact law:
the first carry is the least ternary digit itself. -/
theorem carryAtPos_one_exact (R : Nat) :
    carryAtPos R 1 = R % 3 := by
  have hr : R % 3 = 0 ∨ R % 3 = 1 ∨ R % 3 = 2 := by
    have hlt := Nat.mod_lt R (by decide : 0 < 3)
    omega
  rcases hr with h0 | h1 | h2
  · rw [carryAtPos_one_mod3_0 R h0, h0]
  · rw [carryAtPos_one_mod3_1 R h1, h1]
  · rw [carryAtPos_one_mod3_2 R h2, h2]

/-- Survival at the first carry layer is therefore an exact residue
classification. -/
theorem first_carry_two_iff (R : Nat) :
    carryAtPos R 1 = 2 ↔ R % 3 = 2 := by
  rw [carryAtPos_one_exact]

/-- Multiplication by any ternary power preserves the 2-adic depth reader;
the old one-step invariance is the a=1 specialization. -/
theorem v2r_ternary_scaling (a c : Nat) :
    v2r (3^a * c) = v2r c :=
  v2r_mul_three_pow a c

/-- Exact packet product, coordinatewise. -/
def packetMul
    (A B : GSTThreeWorldExponentialPacketS) :
    GSTThreeWorldExponentialPacketS :=
  ⟨A.binary * B.binary, A.ternary * B.ternary, A.mixed * B.mixed⟩

/-- Zero information depth is the multiplicative identity packet. -/
theorem packet_zero :
    gstThreeWorldExponentialPacketS 0 = ⟨1,1,1⟩ := by
  rfl

/-- **THREE-WORLD COMPOSITION LAW.**  Concatenating information depths is
literally coordinatewise packet multiplication. -/
theorem packet_add (j k : Nat) :
    gstThreeWorldExponentialPacketS (j+k) =
      packetMul (gstThreeWorldExponentialPacketS j)
        (gstThreeWorldExponentialPacketS k) := by
  change
    GSTThreeWorldExponentialPacketS.mk
      (2^(j+k)) (3^(j+k)) (6^(j+k)) =
    GSTThreeWorldExponentialPacketS.mk
      (2^j * 2^k) (3^j * 3^k) (6^j * 6^k)
  rw [pow_add, pow_add, pow_add]

/-- Packet multiplication is associative. -/
theorem packetMul_assoc
    (A B C : GSTThreeWorldExponentialPacketS) :
    packetMul (packetMul A B) C = packetMul A (packetMul B C) := by
  cases A with
  | mk Ab At Am =>
    cases B with
    | mk Bb Bt Bm =>
      cases C with
      | mk Cb Ct Cm =>
        simp [packetMul, Nat.mul_assoc]

/-- The mixed coordinate is determined by the two primitive world
coordinates at every depth. -/
theorem packet_mixed_reconstruct (j : Nat) :
    (gstThreeWorldExponentialPacketS j).mixed =
      (gstThreeWorldExponentialPacketS j).binary *
      (gstThreeWorldExponentialPacketS j).ternary := by
  exact gst_three_world_mixed_factor_exactS j

/-- The closed joined-prefix law has an exact one-step recurrence. -/
theorem joined_prefix_succ (K : Nat) :
    gstHandwrittenThreeWorldJoinedPrefixS (K+1) =
      gstHandwrittenThreeWorldJoinedPrefixS K + 5 * 6^K := by
  unfold gstHandwrittenThreeWorldJoinedPrefixS
  rw [Finset.sum_range_succ, Nat.mul_add]
  unfold gstBinaryWorldFactorS gstTernaryWorldFactorS
  rw [← gst_three_world_factor_rawS K]

/-- Exact reader/packet crown. -/
theorem cardinal_worlds_v2_crown :
    (∀ n, hasTernaryTwo n = true ↔ noTernaryTwo n = false)
    ∧ (∀ R, carryAtPos R 1 = R % 3)
    ∧ (∀ a c, v2r (3^a * c) = v2r c)
    ∧ (∀ j k,
      gstThreeWorldExponentialPacketS (j+k) =
        packetMul (gstThreeWorldExponentialPacketS j)
          (gstThreeWorldExponentialPacketS k)) :=
  ⟨has_two_iff_no_two_false, carryAtPos_one_exact,
    v2r_ternary_scaling, packet_add⟩

#check has_two_iff_no_two_false
#check has_two_iff_first_signature
#check no_two_false_iff_digit_witness
#check carryAtPos_one_exact
#check first_carry_two_iff
#check v2r_ternary_scaling
#check packet_add
#check packetMul_assoc
#check packet_mixed_reconstruct
#check joined_prefix_succ
#check cardinal_worlds_v2_crown

#print axioms has_two_iff_no_two_false
#print axioms has_two_iff_first_signature
#print axioms carryAtPos_one_exact
#print axioms packet_add
#print axioms cardinal_worlds_v2_crown

end CardinalWorldsV2
