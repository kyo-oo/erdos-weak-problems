import KernelChamber406.PinsCensus

-- KernelChamber406 split (S089): olean-cached part of the monolith kernel
-- Pins part 4/4: the two-grant crown + receipts (§8, §9)
-- Pure module surgery: every declaration byte-identical to the monolith.

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace PiCollapse406

/-! ## §8 The two-grant crown -/
#print axioms PiCollapse406.cantorian_base  -- CK74 SECTION BOUNDARY

/-- The Cantorian power predicate: every ternary digit from position
one on avoids two (position zero is always one). -/
def CantorianPower (K : Nat) : Prop :=
  ∀ p : Nat, 1 ≤ p → digit3 (4^K) p ≠ 2

/-- Every positive natural decomposes as `3^s * u` with `u` three-free
(the green fuel pattern). -/
theorem exists_three_free_decomp :
    ∀ (fuel K : Nat), 1 ≤ K → K ≤ fuel →
      ∃ s u : Nat, K = 3^s * u ∧ ¬ (3:Nat) ∣ u := by
  intro fuel
  induction fuel with
  | zero => intro K hK hKF; omega
  | succ fuel ih =>
      intro K hK hKF
      by_cases h3 : (3:Nat) ∣ K
      · obtain ⟨K', hK'⟩ := h3
        have hK'1 : 1 ≤ K' := by
          by_cases hK0 : K' = 0
          · omega
          · omega
        have hlt : K' ≤ fuel := by omega
        obtain ⟨s, u, hsu, hu⟩ := ih K' hK'1 hlt
        refine ⟨s+1, u, ?_, hu⟩
        calc K = 3 * K' := hK'
          _ = 3 * (3^s * u) := by rw [hsu]
          _ = 3^(s+1) * u := by rw [Nat.pow_succ]; ring
      · exact ⟨0, K, by simp, h3⟩

theorem pow4_mod3 (r : Nat) : 4^r % 3 = 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem digit3_pow4_zero (K : Nat) : digit3 (4^K) 0 = 1 := by
  unfold digit3
  rw [Nat.pow_zero, Nat.div_one, pow4_mod3]

theorem two_pow_two_mul (K : Nat) : 2^(2*K) = 4^K := by
  rw [show (4:Nat) = 2^2 from rfl, ← Nat.pow_mul]

/-- A ternary digit two at any position certifies the Arsenal's
has-reader, by induction on the position (the `.eq_def` idiom). -/
theorem hasTwo_of_digit : ∀ (n p : Nat), digit3 n p = 2 →
    hasTernaryTwo n = true :=
  fun n p hp => hasTernaryTwo_of_digit n p hp

/-- **THE TWO-GRANT CROWN.**  The FULL Erdős #406 statement follows from
exactly two named grants: (G1) ghost extinction — no core carries the
full shadow package; (G2) residual ghost compression — every Cantorian
power above the kernel base has a ghost-ray core.  Everything else is
unconditional and machine-checked: the finite base (§7), the odd wing,
the three paid small cases, and the digit-to-verdict bridge. -/
theorem erdos406_crown_of_ghost_extinction
    (hNoGhost : ∀ u : Nat, ¬ GhostRay u)
    (hComp : ∀ (K σ u : Nat), 500 < K → K = 3^σ * u → ¬ (3:Nat) ∣ u →
      CantorianPower K → GhostRay u) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  -- Step 1: no Cantorian power above eight
  have hnoCant : ∀ K : Nat, 8 ≤ K → ¬ CantorianPower K := by
    intro K hK8 hCant
    rcases Nat.lt_or_ge K 501 with hle | hgt
    · obtain ⟨p, hp⟩ := cantorian_base K hK8 (by omega)
      refine hCant p ?_ hp
      rcases Nat.eq_zero_or_pos p with h0 | hp1
      · rw [h0, digit3_pow4_zero] at hp
        exact absurd hp (by decide)
      · exact hp1
    · obtain ⟨σ, u, hKu, hu⟩ :=
        exists_three_free_decomp K K (by omega) (by omega)
      exact hNoGhost u (hComp K σ u (by omega) hKu hu hCant)
  -- Step 2: every 4^m, m ≥ 5, owns a digit two
  have hfire : ∀ m : Nat, 5 ≤ m → ∃ p : Nat, digit3 (4^m) p = 2 := by
    intro m hm
    rcases Nat.lt_or_ge m 8 with hlt | hge
    · have hm567 : m = 5 ∨ m = 6 ∨ m = 7 := by omega
      rcases hm567 with rfl | rfl | rfl
      · exact ⟨2, by decide⟩
      · exact ⟨2, by decide⟩
      · exact ⟨8, by decide⟩
    · have hnc := hnoCant m hge
      by_contra hclean
      exact hnc (fun p hp hdirty => hclean ⟨p, hdirty⟩)
  -- Step 3: the final assembly, odd and even wings
  intro n hn
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have hm : n = 2 * (n / 2) := by omega
    have hm5 : 5 ≤ n / 2 := by omega
    obtain ⟨p, hp⟩ := hfire (n / 2) hm5
    have hhas : hasTernaryTwo (4^(n / 2)) = true :=
      hasTwo_of_digit (4^(n / 2)) p hp
    have h2n : 2^n = 4^(n / 2) := by
      rw [hm, two_pow_two_mul]
    rw [h2n]
    exact has_two_imp_not_no_two (4^(n / 2)) hhas
  · have hnodd : n = 2 * (n / 2) + 1 := by omega
    have hmod : (2^n) % 3 = 2 := by
      rw [hnodd, Nat.pow_succ]
      have h2m : (2:Nat)^(2 * (n / 2)) % 3 = 1 := by
        rw [two_pow_two_mul]
        exact pow4_mod3 _
      rw [Nat.mul_mod, h2m]
      decide
    have hdig : digit3 (2^n) 0 = 2 := by
      unfold digit3
      rw [Nat.pow_zero, Nat.div_one, hmod]
    have hhas : hasTernaryTwo (2^n) = true :=
      hasTwo_of_digit (2^n) 0 hdig
    exact has_two_imp_not_no_two (2^n) hhas

/-! ## §9 Receipts -/
#print axioms PiCollapse406.erdos406_crown_of_ghost_extinction  -- CK74 SECTION BOUNDARY

#check PiCollapse406.ghost_residue_shape
#check PiCollapse406.ghost_congruence
#check PiCollapse406.ghost_congruent_all_depths
#check PiCollapse406.every_ghost_is_its_pi_point_fam4
#check PiCollapse406.every_ghost_is_its_pi_point_fam7
#check PiCollapse406.every_ghost_is_its_pi_point_fam1
#check PiCollapse406.cantorian_base
#check PiCollapse406.erdos406_crown_of_ghost_extinction

#print axioms PiCollapse406.pow4_three_power_lte_exact
#print axioms PiCollapse406.lteCoeff_mod3_one
#print axioms PiCollapse406.lteCoeff_stable
#print axioms PiCollapse406.ghost_residue_shape
#print axioms PiCollapse406.ghost_congruence
#print axioms PiCollapse406.dvd_mul_cancel_three
#print axioms PiCollapse406.dvd_of_unit_mul_cancel
#print axioms PiCollapse406.cancel_engine
#print axioms PiCollapse406.ghost_congruent_ge_three
#print axioms PiCollapse406.ghost_congruent_all_depths
#print axioms PiCollapse406.ghost_head_not_three
#print axioms PiCollapse406.ghost_head_lt_nine
#print axioms PiCollapse406.cMod_eq
#print axioms PiCollapse406.W61_receipt
#print axioms PiCollapse406.W61_mod_nine
#print axioms PiCollapse406.W61_mod_three
#print axioms PiCollapse406.pi_fam4_receipt
#print axioms PiCollapse406.pi_fam7_receipt
#print axioms PiCollapse406.pi_fam1_receipt
#print axioms PiCollapse406.pi_fam4_trit3
#print axioms PiCollapse406.pi_fam4_trit14
#print axioms PiCollapse406.pi_fam7_trit1
#print axioms PiCollapse406.pi_fam7_trit6
#print axioms PiCollapse406.pi_fam1_trit8
#print axioms PiCollapse406.pi_fam1_trit13
#print axioms PiCollapse406.hasTwoScan_iff
#print axioms PiCollapse406.cantorian_base
#print axioms PiCollapse406.hasTwo_of_digit
#print axioms PiCollapse406.erdos406_crown_of_ghost_extinction

#eval "ERDOS406_PICOLLAPSE_KERNEL_GREEN"



#print axioms PiCollapse406.cMod_eq
#print axioms PiCollapse406.every_ghost_is_its_pi_point_fam4
#print axioms PiCollapse406.every_ghost_is_its_pi_point_fam7
#print axioms PiCollapse406.every_ghost_is_its_pi_point_fam1
#print axioms PiCollapse406.cantorian_base
#print axioms PiCollapse406.erdos406_crown_of_ghost_extinction

#eval "ERDOS406_PICOLLAPSE_PINS_GREEN"

end PiCollapse406

#print axioms PiCollapse406.cMod_eq
#print axioms PiCollapse406.every_ghost_is_its_pi_point_fam4
#print axioms PiCollapse406.every_ghost_is_its_pi_point_fam7
#print axioms PiCollapse406.every_ghost_is_its_pi_point_fam1
#print axioms PiCollapse406.cantorian_base
#print axioms PiCollapse406.erdos406_crown_of_ghost_extinction

#eval "ERDOS406_PICOLLAPSE_KERNEL_GREEN"
