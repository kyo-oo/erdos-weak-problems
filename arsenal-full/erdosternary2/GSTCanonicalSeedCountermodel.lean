import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST exact canonical seed/offset countermodel (not a perfect-power origin)

At s=1, k=1, the TRUE origin-affine channel has
  A=4^(3^1)=64, c_1=7, seed=4*(c_1%3)/3=1, offset=c_1/3=2.
An arbitrary child T=46 has a Navigation Happy Gate at position 2,
while the whole parent seeded word X=2+64*46=2946 is BAD at ALL
natural positions.

So power multiplier, correct carry seed, exact offset and all-depth
bad preservation still do not force parent exit from the bad space.
The perfect-power child-source fingerprint is the essential remaining
hypothesis. No claim about Erdos conjecture follows from this example.
-/

namespace GSTCanonicalSeedCountermodel

theorem canonical_origin_coeff_one : c 1 = 7 := by decide

/-- Even the three-free normalized origin residue matches the genuine
GST child at the first three coefficient trits for m=13. -/
theorem three_free_core_and_correct_low_residue :
    46 % 3 = 1 ∧ 46 % 27 = (13 * 16) % 27 := by decide

theorem child_46_navigation : GSTNavigationWitness 46 := by
  refine ⟨2, ?_, ?_⟩
  · norm_num [gstDigit]
  · right
    norm_num [gstSpaceAt, gstCarry]

theorem seeded_parent_2946_bad : GSTSeededAffineBadTrace 1 2946 := by
  intro j
  change GSTBadPair (gstAffineMulCarry 4 1 2946 j) (gstDigit 2946 j)
  by_cases hj : j < 8
  · interval_cases j <;>
      norm_num [GSTBadPair, gstAffineMulCarry, gstDigit]
  · have hp : 3^8 ≤ 3^j :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    have hshort : 1+4*2946 < 3^j := by
      have h8 : 1+4*2946 < 3^8 := by decide
      omega
    have htail : 2946 < 3^j := by omega
    have hd0 : 2946 / 3^j = 0 := Nat.div_eq_of_lt htail
    have hcarry : (1+4*(2946 % 3^j))/3^j=0 := by
      have hmod : 2946 % 3^j ≤ 2946 := Nat.mod_le _ _
      have hnum : 1+4*(2946%3^j) < 3^j := by omega
      exact Nat.div_eq_of_lt hnum
    simp [GSTBadPair, gstAffineMulCarry, gstDigit, hd0, hcarry]

/-- Critical negative theorem for any unrestricted prefix-one lift:
the exact source-form affine channel is not sufficient by itself. -/
theorem canonical_seed_affine_transport_can_fail :
    ∃ T : Nat,
      GSTNavigationWitness T ∧
      GSTSeededAffineBadTrace
        ((4*(c 1 % 3))/3)
        (c 1/3 + 4^(3^1)*T) := by
  refine ⟨46, child_46_navigation, ?_⟩
  have hc := canonical_origin_coeff_one
  simpa [hc] using seeded_parent_2946_bad

#print axioms child_46_navigation
#print axioms seeded_parent_2946_bad
#print axioms canonical_seed_affine_transport_can_fail

end GSTCanonicalSeedCountermodel
