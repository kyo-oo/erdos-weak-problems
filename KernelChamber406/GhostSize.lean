import KernelChamber406.GhostHalf

-- KernelChamber406 split (S089): olean-cached part of the monolith kernel
-- Ghost part 3/4: the size law (§7)
-- Pure module surgery: every declaration byte-identical to the monolith.

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace GhostExtinction406

/-! ## §7 THE SIZE LAW — every ghost on the rider sheet is astronomical -/
#print axioms GhostExtinction406.every_ghost_is_its_pi100_point_fam1  -- CK75 SECTION BOUNDARY

theorem pi100_fam4_gt : 3^99 < pi100_fam4 := by decide
theorem pi100_fam7_gt : 3^99 < pi100_fam7 := by decide
theorem pi100_fam1_gt : 3^98 < pi100_fam1 := by decide

/-- **THE SIZE LAW, FAMILY FOUR (NEW).**  Every ghost ray with head one
exceeds `3^99`. -/
theorem ghost_size_fam4 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 1) : 3^99 < u := by
  have hpin := every_ghost_is_its_pi100_point_fam4 u hg hhead
  have hdm := Nat.div_add_mod u (3^100)
  have hgt := pi100_fam4_gt
  omega

/-- **THE SIZE LAW, FAMILY SEVEN (NEW).**  Every ghost ray with head
four exceeds `3^99`. -/
theorem ghost_size_fam7 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 4) : 3^99 < u := by
  have hpin := every_ghost_is_its_pi100_point_fam7 u hg hhead
  have hdm := Nat.div_add_mod u (3^100)
  have hgt := pi100_fam7_gt
  omega

/-- **THE SIZE LAW, FAMILY ONE (NEW).**  Every ghost ray with head seven
exceeds `3^98`. -/
theorem ghost_size_fam1 (u : Nat) (hg : GhostRay u)
    (hhead : ghostHead u = 7) : 3^98 < u := by
  have hpin := every_ghost_is_its_pi100_point_fam1 u hg hhead
  have hdm := Nat.div_add_mod u (3^100)
  have hgt := pi100_fam1_gt
  omega

/-- **THE UNIFORM SIZE LAW (NEW).**  Every ghost ray on the rider sheet
(`u ≡ 1 mod 3`) exceeds `3^98`. -/
theorem ghost_size_rider_sheet (u : Nat) (hg : GhostRay u)
    (hu3 : u % 3 = 1) : 3^98 < u := by
  rcases ghost_head_split u hg hu3 with h | h | h
  · have h4 := ghost_size_fam4 u hg h
    have hle : 3^98 ≤ 3^99 := three_pow_le_of_le 98 99 (by omega)
    omega
  · have h7 := ghost_size_fam7 u hg h
    have hle : 3^98 ≤ 3^99 := three_pow_le_of_le 98 99 (by omega)
    omega
  · exact ghost_size_fam1 u hg h
end GhostExtinction406
