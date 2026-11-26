import KernelChamber406.GhostWordR

-- KernelChamber406 split (S089k, the split-of-the-split): olean-cached part
-- of the monolith kernel Ghost 2b/5: THE PIN ENGINE AT DEPTH 100 —
-- pin100_of_W_congruence, the ghost-to-W congruences, and the three PIN
-- theorems.
-- Pure module surgery: every declaration byte-identical to the monolith
-- (GhostExtinction406.lean §6 pin engine).

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace GhostExtinction406

/-- **THE PIN ENGINE AT DEPTH 100.**  If both a core `u` and a fixed
point `π < 3^100` solve the same W-form congruence, then
`u ≡ π [MOD 3^100]`. -/
theorem pin100_of_W_congruence (u π D : Nat)
    (hu : 3^100 ∣ 2 * W100 * u + D)
    (hπ : 3^100 ∣ 2 * W100 * π + D)
    (hπlt : π < 3^100) :
    u % 3^100 = π := by
  have hunit : ¬ (3:Nat) ∣ 2 * W100 := by
    intro hd
    have h0 : (2 * W100) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    rw [Nat.mul_mod, W100_mod_three] at h0
    norm_num at h0
  by_cases hle : π ≤ u
  · have hE : (2 * W100 * u + D) - (2 * W100 * π + D)
        = 2 * W100 * (u - π) := by
      rw [Nat.mul_sub]
      omega
    have hsub : 3^100 ∣ 2 * W100 * (u - π) := by
      obtain ⟨b, hb⟩ := hu
      obtain ⟨a, ha⟩ := hπ
      refine ⟨b - a, ?_⟩
      rw [Nat.mul_sub, Nat.mul_sub]
      omega
    have hcancel := dvd_of_unit_mul_cancel 100 (2 * W100) (u - π) hunit hsub
    obtain ⟨t, ht⟩ := hcancel
    have huπ : u = π + 3^100 * t := by omega
    rw [huπ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hπlt]
  · have hgt : u < π := by omega
    have hE : (2 * W100 * π + D) - (2 * W100 * u + D)
        = 2 * W100 * (π - u) := by
      rw [Nat.mul_sub]
      omega
    have hsub : 3^100 ∣ 2 * W100 * (π - u) := by
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hπ
      refine ⟨a - b, ?_⟩
      rw [Nat.mul_sub, Nat.mul_sub]
      omega
    have hcancel := dvd_of_unit_mul_cancel 100 (2 * W100) (π - u) hunit hsub
    obtain ⟨t, ht⟩ := hcancel
    have hπu : π = u + 3^100 * t := by omega
    have hmod : u % 3^100 = π % 3^100 := by
      rw [hπu, Nat.add_mul_mod_self_left]
    rw [hmod, Nat.mod_eq_of_lt hπlt]

/-- The ghost-to-W congruence at depth 100, family four (head one). -/
theorem ghost_W100_congruence_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) :
    3^100 ∣ 2 * W100 * u + 7 := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 100 (by omega)
  rw [hhead] at hm
  rw [coeff_split100 u] at hm
  have hring : 3^100 * (2 * ((lteCoeff 99 / 3^100) * u))
      = 2 * (3^100 * ((lteCoeff 99 / 3^100) * u)) := by ring
  refine ⟨m - 2 * ((lteCoeff 99 / 3^100) * u), ?_⟩
  rw [Nat.mul_sub, hring]
  omega

/-- The ghost-to-W congruence at depth 100, family seven (head four). -/
theorem ghost_W100_congruence_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) :
    3^100 ∣ 2 * W100 * u + 1 := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 100 (by omega)
  rw [hhead] at hm
  rw [coeff_split100 u] at hm
  have hring : 3^100 * (2 * ((lteCoeff 99 / 3^100) * u))
      = 2 * (3^100 * ((lteCoeff 99 / 3^100) * u)) := by ring
  refine ⟨m - 2 * ((lteCoeff 99 / 3^100) * u), ?_⟩
  rw [Nat.mul_sub, hring]
  omega

/-- The ghost-to-W congruence at depth 100, family one (head seven). -/
theorem ghost_W100_congruence_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) :
    3^100 ∣ 2 * W100 * u + (3^100 - 5) := by
  obtain ⟨m, hm⟩ := ghost_congruence u hg 100 (by omega)
  rw [hhead] at hm
  rw [coeff_split100 u] at hm
  have hring : 3^100 * (2 * ((lteCoeff 99 / 3^100) * u))
      = 2 * (3^100 * ((lteCoeff 99 / 3^100) * u)) := by ring
  refine ⟨m + 1 - 2 * ((lteCoeff 99 / 3^100) * u), ?_⟩
  have hdistrib : 3^100 * (m + 1 - 2 * ((lteCoeff 99 / 3^100) * u))
      = 3^100 * m + 3^100 * 1 - 3^100 * (2 * ((lteCoeff 99 / 3^100) * u)) := by
    rw [Nat.mul_sub, Nat.mul_add, Nat.mul_one]
  rw [hdistrib, hring, Nat.mul_one]
  omega

/-- **THE PIN AT DEPTH 100, FAMILY FOUR.** -/
theorem every_ghost_is_its_pi100_point_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) : u % 3^100 = pi100_fam4 :=
  pin100_of_W_congruence u pi100_fam4 7
    (ghost_W100_congruence_fam4 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi100_fam4_receipt) pi100_fam4_lt

/-- **THE PIN AT DEPTH 100, FAMILY SEVEN.** -/
theorem every_ghost_is_its_pi100_point_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) : u % 3^100 = pi100_fam7 :=
  pin100_of_W_congruence u pi100_fam7 1
    (ghost_W100_congruence_fam7 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi100_fam7_receipt) pi100_fam7_lt

/-- **THE PIN AT DEPTH 100, FAMILY ONE.** -/
theorem every_ghost_is_its_pi100_point_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) : u % 3^100 = pi100_fam1 :=
  pin100_of_W_congruence u pi100_fam1 (3^100 - 5)
    (ghost_W100_congruence_fam1 u hg hhead)
    (Nat.dvd_of_mod_eq_zero pi100_fam1_receipt) pi100_fam1_lt

#print axioms GhostExtinction406.every_ghost_is_its_pi100_point_fam4  -- CK75 pins layer receipt
end GhostExtinction406
