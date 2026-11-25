import KernelChamber406.PinsWord

-- KernelChamber406 split (S089k, the split-of-the-split): olean-cached part
-- of the monolith kernel Pins 2b/5: THE PIN ENGINE (§6b) — pin_of_W_
-- congruence, the ghost-to-W congruences, and the three PIN theorems.
-- Pure module surgery: every declaration byte-identical to the monolith
-- (PiCollapse406Pins.lean §6b).

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace PiCollapse406

/-! ## §6b The pin — every ghost ray IS its π-point -/

/-- **THE PIN ENGINE.**  If both a core `u` and a fixed point `π < 3^61`
solve the same W-form congruence `2·W61·x + D ≡ 0 [MOD 3^61]`, then
`u ≡ π [MOD 3^61]`. -/
theorem pin_of_W_congruence (u π D : Nat)
    (hu : 3^61 ∣ 2 * W61 * u + D)
    (hπ : 3^61 ∣ 2 * W61 * π + D)
    (hπlt : π < 3^61) :
    u % 3^61 = π := by
  have hunit : ¬ (3:Nat) ∣ 2 * W61 := by
    intro hd
    have h0 : (2 * W61) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [Nat.mul_mod, W61_mod_three] at h0
    norm_num at h0
  by_cases hle : π ≤ u
  · have hE : (2 * W61 * u + D) - (2 * W61 * π + D)
        = 2 * W61 * (u - π) := by
      rw [Nat.mul_sub]
      omega
    have hsub : 3^61 ∣ 2 * W61 * (u - π) := by
      obtain ⟨b, hb⟩ := hu
      obtain ⟨a, ha⟩ := hπ
      refine ⟨b - a, ?_⟩
      rw [Nat.mul_sub, Nat.mul_sub]
      omega
    have hcancel := dvd_of_unit_mul_cancel 61 (2 * W61) (u - π) hunit hsub
    obtain ⟨t, ht⟩ := hcancel
    have huπ : u = π + 3^61 * t := by omega
    rw [huπ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hπlt]
  · have hgt : u < π := by omega
    have hE : (2 * W61 * π + D) - (2 * W61 * u + D)
        = 2 * W61 * (π - u) := by
      rw [Nat.mul_sub]
      omega
    have hsub : 3^61 ∣ 2 * W61 * (π - u) := by
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hπ
      refine ⟨a - b, ?_⟩
      rw [Nat.mul_sub, Nat.mul_sub]
      omega
    have hcancel := dvd_of_unit_mul_cancel 61 (2 * W61) (π - u) hunit hsub
    obtain ⟨t, ht⟩ := hcancel
    have hπu : π = u + 3^61 * t := by omega
    have hmod : u % 3^61 = π % 3^61 := by
      rw [hπu, Nat.add_mul_mod_self_left]
    rw [hmod, Nat.mod_eq_of_lt hπlt]

/-- The ghost-to-W congruence, family four: head one, `D = 7`. -/
theorem ghost_W_congruence_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) :
    3^61 ∣ 2 * W61 * u + 7 := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 61 (by omega)
  rw [hhead] at hm
  rw [coeff_split u] at hm
  have hring : 3^61 * (2 * ((lteCoeff 60 / 3^61) * u))
      = 2 * (3^61 * ((lteCoeff 60 / 3^61) * u)) := by ring
  refine ⟨m - 2 * ((lteCoeff 60 / 3^61) * u), ?_⟩
  rw [Nat.mul_sub, hring]
  omega

/-- The ghost-to-W congruence, family seven: head four, `D = 1`. -/
theorem ghost_W_congruence_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) :
    3^61 ∣ 2 * W61 * u + 1 := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 61 (by omega)
  rw [hhead] at hm
  rw [coeff_split u] at hm
  have hring : 3^61 * (2 * ((lteCoeff 60 / 3^61) * u))
      = 2 * (3^61 * ((lteCoeff 60 / 3^61) * u)) := by ring
  refine ⟨m - 2 * ((lteCoeff 60 / 3^61) * u), ?_⟩
  rw [Nat.mul_sub, hring]
  omega

/-- The ghost-to-W congruence, family one: head seven, `D = 3^61 - 5`. -/
theorem ghost_W_congruence_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) :
    3^61 ∣ 2 * W61 * u + (3^61 - 5) := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 61 (by omega)
  rw [hhead] at hm
  rw [coeff_split u] at hm
  have hring : 3^61 * (2 * ((lteCoeff 60 / 3^61) * u))
      = 2 * (3^61 * ((lteCoeff 60 / 3^61) * u)) := by ring
  refine ⟨m + 1 - 2 * ((lteCoeff 60 / 3^61) * u), ?_⟩
  have hdistrib : 3^61 * (m + 1 - 2 * ((lteCoeff 60 / 3^61) * u))
      = 3^61 * m + 3^61 * 1 - 3^61 * (2 * ((lteCoeff 60 / 3^61) * u)) := by
    rw [Nat.mul_sub, Nat.mul_add, Nat.mul_one]
  rw [hdistrib, hring, Nat.mul_one]
  omega

/-- **THE PIN, FAMILY FOUR.**  Every ghost ray with head one is the
fixed point `pi_fam4` modulo `3^61`. -/
theorem every_ghost_is_its_pi_point_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) : u % 3^61 = pi_fam4 :=
  pin_of_W_congruence u pi_fam4 7
    (ghost_W_congruence_fam4 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi_fam4_receipt) pi_fam4_lt

/-- **THE PIN, FAMILY SEVEN.**  Every ghost ray with head four is the
fixed point `pi_fam7` modulo `3^61`. -/
theorem every_ghost_is_its_pi_point_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) : u % 3^61 = pi_fam7 :=
  pin_of_W_congruence u pi_fam7 1
    (ghost_W_congruence_fam7 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi_fam7_receipt) pi_fam7_lt

/-- **THE PIN, FAMILY ONE.**  Every ghost ray with head seven is the
fixed point `pi_fam1` modulo `3^61`. -/
theorem every_ghost_is_its_pi_point_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) : u % 3^61 = pi_fam1 :=
  pin_of_W_congruence u pi_fam1 (3^61 - 5)
    (ghost_W_congruence_fam1 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi_fam1_receipt) pi_fam1_lt

#print axioms PiCollapse406.every_ghost_is_its_pi_point_fam4  -- CK74 pins layer receipt
end PiCollapse406
