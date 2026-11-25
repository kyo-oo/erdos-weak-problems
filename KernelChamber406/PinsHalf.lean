import KernelChamber406.PinsSpine

-- KernelChamber406 split (S089): olean-cached part of the monolith kernel
-- Pins part 2/4: the pi-points + THE PIN (§6, §6b)
-- Pure module surgery: every declaration byte-identical to the monolith.

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace PiCollapse406

/-! ## §6 The π-points, kernel-decided -/
#print axioms PiCollapse406.ghost_congruent_all_depths  -- CK74 SECTION BOUNDARY

/-- The certified mod-recursion: `cMod k s = lteCoeff s % 3^k`, computed
without ever forming the astronomically large tower coefficient. -/
def cMod : Nat → Nat → Nat
  | k, 0 => 1 % 3^k
  | k, s+1 =>
      let c := cMod k s
      (c + 3^(s+1) * c^2 + 3^(2*s+1) * c^3) % 3^k

/-- Congruence respects addition (hardened S083: explicit lemma
applications — the double-rw form re-matches the outer term under the
W82 Mathlib and left double-mods). -/
theorem mod_add_congr (k a b c d : Nat) (h1 : a % k = b % k)
    (h2 : c % k = d % k) : (a + c) % k = (b + d) % k := by
  calc (a + c) % k = ((a % k) + (c % k)) % k := Nat.add_mod a c k
    _ = ((b % k) + (d % k)) % k := by rw [h1, h2]
    _ = (b + d) % k := (Nat.add_mod b d k).symm

/-- Congruence respects multiplication (hardened the same way). -/
theorem mod_mul_congr (k a b c d : Nat) (h1 : a % k = b % k)
    (h2 : c % k = d % k) : (a * c) % k = (b * d) % k := by
  calc (a * c) % k = ((a % k) * (c % k)) % k := Nat.mul_mod a c k
    _ = ((b % k) * (d % k)) % k := by rw [h1, h2]
    _ = (b * d) % k := (Nat.mul_mod b d k).symm

/-- Congruence respects powers (hardened: explicit pow_succ shapes). -/
theorem mod_pow_congr (k : Nat) : ∀ (n a b : Nat), a % k = b % k →
    (a^n) % k = (b^n) % k
  | 0, a, b, _ => by simp
  | n+1, a, b, h => by
      have ih := mod_pow_congr k n a b h
      have pa : a^(n+1) = a * a^n := Nat.pow_succ a n
      have pb : b^(n+1) = b * b^n := Nat.pow_succ b n
      rw [pa, pb]
      exact mod_mul_congr k (a * a^n) (b * b^n) a b ih h

theorem cMod_eq (k : Nat) : ∀ s : Nat, cMod k s = lteCoeff s % 3^k
  | 0 => by
      simp only [cMod, lteCoeff]
  | s+1 => by
      have ih := cMod_eq k s
      simp only [cMod, lteCoeff]
      have e2 : (3^(s+1) * (lteCoeff s)^2) % 3^k
          = (3^(s+1) * (cMod k s)^2) % 3^k :=
        mod_mul_congr k _ _ _ _ rfl (mod_pow_congr k 2 _ _ ih)
      have e3 : (3^(2*s+1) * (lteCoeff s)^3) % 3^k
          = (3^(2*s+1) * (cMod k s)^3) % 3^k :=
        mod_mul_congr k _ _ _ _ rfl (mod_pow_congr k 3 _ _ ih)
      have eL : ((lteCoeff s + 3^(s+1) * (lteCoeff s)^2)
          + 3^(2*s+1) * (lteCoeff s)^3) % 3^k
          = ((cMod k s + 3^(s+1) * (cMod k s)^2)
          + 3^(2*s+1) * (cMod k s)^3) % 3^k :=
        mod_add_congr k _ _ _ _
          (mod_add_congr k _ _ _ _ ih e2) e3
      calc (cMod k s + 3^(s+1) * (cMod k s)^2 + 3^(2*s+1) * (cMod k s)^3) % 3^k
          = ((cMod k s + 3^(s+1) * (cMod k s)^2)
              + 3^(2*s+1) * (cMod k s)^3) % 3^k := rfl
        _ = ((lteCoeff s + 3^(s+1) * (lteCoeff s)^2)
              + 3^(2*s+1) * (lteCoeff s)^3) % 3^k := eL.symm
        _ = (lteCoeff s + 3^(s+1) * (lteCoeff s)^2
              + 3^(2*s+1) * (lteCoeff s)^3) % 3^k := rfl

/-- **THE UNIT WORD MOD 3^61** — the stabilized tower coefficient at
depth 60, computed by the certified recursion (dual-verified against
the independent S078 Hensel lift: `W ≡ 7 (mod 9)`, `W ≡ 16 (mod 27)`). -/
def W61 : Nat := 60776643992856088575557123854

theorem W61_receipt : cMod 61 60 = W61 := by decide

theorem W61_mod_nine : W61 % 9 = 7 := by decide

theorem W61_mod_three : W61 % 3 = 1 := by decide

theorem W61_lt : W61 < 3^61 := by decide

theorem lteCoeff_sixty_mod : lteCoeff 60 % 3^61 = W61 := by
  rw [← W61_receipt]
  exact (cMod_eq 61 60).symm

theorem three_pow_61_pos : 5 ≤ 3^61 := by decide

/-- The coefficient split at depth 61 (the congrArg idiom — no rw loop). -/
theorem coeff_split (u : Nat) :
    lteCoeff 60 * u
      = 3^61 * ((lteCoeff 60 / 3^61) * u) + W61 * u := by
  have hc := Nat.div_add_mod (lteCoeff 60) (3^61)
  rw [lteCoeff_sixty_mod] at hc
  calc lteCoeff 60 * u
      = (3^61 * (lteCoeff 60 / 3^61) + W61) * u := by
        conv_lhs => rw [hc]
    _ = 3^61 * ((lteCoeff 60 / 3^61) * u) + W61 * u := by ring

/-- **THE THREE FIXED POINTS** (the assault engine's `π₄, π₇, π₁`,
dual-verified against the independent Hensel lift of `2·W·π = T` for
`T ∈ {-7, -1, +5}` in `ℤ₃`; all three carry scattered 2-trits through
60 positions — 13, 20 and 18 respectively). -/
def pi_fam4 : Nat := 68350949682967876566738142093  -- head 1, T = -7
def pi_fam7 : Nat := 64267339165701958313626862986  -- head 4, T = -1
def pi_fam1 : Nat := 60183728648436040060515583879  -- head 7, T = +5

theorem pi_fam4_lt : pi_fam4 < 3^61 := by decide
theorem pi_fam7_lt : pi_fam7 < 3^61 := by decide
theorem pi_fam1_lt : pi_fam1 < 3^61 := by decide

theorem pi_fam4_receipt :
    (2 * W61 * pi_fam4 + 7) % 3^61 = 0 := by decide

theorem pi_fam7_receipt :
    (2 * W61 * pi_fam7 + 1) % 3^61 = 0 := by decide

theorem pi_fam1_receipt :
    (2 * W61 * pi_fam1 + (3^61 - 5)) % 3^61 = 0 := by decide

/-- **THE 2-TRIT RECEIPTS** — the three fixed points are not eventually
zero: each carries ternary digit twos deep in its expansion
(kernel-decided positions from the assault engine's certified list). -/
theorem pi_fam4_trit3 : digit3 pi_fam4 3 = 2 := by decide
theorem pi_fam4_trit14 : digit3 pi_fam4 14 = 2 := by decide
theorem pi_fam7_trit1 : digit3 pi_fam7 1 = 2 := by decide
theorem pi_fam7_trit6 : digit3 pi_fam7 6 = 2 := by decide
theorem pi_fam1_trit8 : digit3 pi_fam1 8 = 2 := by decide
theorem pi_fam1_trit13 : digit3 pi_fam1 13 = 2 := by decide

/-! ## §6b The pin — every ghost ray IS its π-point -/
#print axioms PiCollapse406.W61  -- CK74 SECTION BOUNDARY

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
end PiCollapse406
