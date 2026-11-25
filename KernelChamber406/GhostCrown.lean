import KernelChamber406.GhostSize

-- KernelChamber406 split (S089): olean-cached part of the monolith kernel
-- Ghost part 4/4: census + crown v2 + receipts (§8, §9, §10)
-- Pure module surgery: every declaration byte-identical to the monolith.

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace GhostExtinction406

/-! ## §8 The finite base — every exponent 8..500 fires -/

/-- The digit-two scan: `hasTwoScan n B = true` iff some ternary digit
of `n` at a position `< B` equals two. -/
def hasTwoScan : Nat → Nat → Bool
  | _, 0 => false
  | n, B+1 => (n % 3 == 2) || hasTwoScan (n / 3) B

theorem hasTwoScan_iff : ∀ (B n : Nat),
    hasTwoScan n B = true ↔ ∃ p : Nat, p < B ∧ digit3 n p = 2 := by
  intro B
  induction B with
  | zero =>
      intro n
      constructor
      · intro h; exact absurd h (by decide)
      · intro ⟨p, hp, _⟩; exact absurd hp (by omega)
  | succ B ih =>
      intro n
      have h0 : digit3 n 0 = n % 3 := by
        unfold digit3
        rw [Nat.pow_zero, Nat.div_one]
      have hsh : ∀ p : Nat, digit3 n (p + 1) = digit3 (n / 3) p := by
        intro p
        unfold digit3
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm (3^p) (3:Nat)]
      by_cases hb : n % 3 = 2
      · have hbeq : (n % 3 == 2) = true := by rw [hb]; rfl
        simp only [hasTwoScan, hbeq, Bool.true_or]
        constructor
        · intro _
          exact ⟨0, by omega, by rw [h0, hb]⟩
        · intro _
          rfl
      · have hbeq : (n % 3 == 2) = false := by
          cases hbb : (n % 3 == 2) with
          | true => exact absurd (Nat.eq_of_beq_eq_true hbb) hb
          | false => rfl
        simp only [hasTwoScan, hbeq, Bool.false_or]
        constructor
        · intro h
          obtain ⟨p, hp, hd⟩ := (ih (n / 3)).mp h
          exact ⟨p + 1, by omega, by rw [hsh p]; exact hd⟩
        · intro ⟨p, hp, hd⟩
          cases p with
          | zero =>
              rw [h0] at hd
              exact absurd hd hb
          | succ q =>
              rw [hsh q] at hd
              exact (ih (n / 3)).mpr ⟨q, by omega, hd⟩

/-- The census case: the exact digit scan of `4^(8+i)` at fuel 632. -/
def baseCaseB (i : Nat) : Bool := hasTwoScan (4^(8+i)) 632

theorem base_chunk_one : (List.range 251).all
    (fun i => baseCaseB i) = true := by decide

theorem base_chunk_two : (List.range 242).all
    (fun i => baseCaseB (251 + i)) = true := by decide

/-- **THE FINITE BASE.**  Every exponent `8 ≤ K ≤ 500` owns a ternary
digit two: the kernel-decided census, both chunks, the full scan. -/
theorem cantorian_base (K : Nat) (hK8 : 8 ≤ K) (hK500 : K ≤ 500) :
    ∃ p : Nat, digit3 (4^K) p = 2 := by
  rcases Nat.lt_or_ge K (8 + 251) with hlt | hge
  · have hc := (List.all_eq_true.mp base_chunk_one) (K - 8)
      (List.mem_range.mpr (by omega))
    exact (hasTwoScan_iff 632 _).mp hc
  · have hc := (List.all_eq_true.mp base_chunk_two) (K - 8 - 251)
      (List.mem_range.mpr (by omega))
    have hsplit : 4^(8 + (251 + (K - 8 - 251))) = 4^K := by
      congr 1
      omega
    rw [hsplit] at hc
    exact (hasTwoScan_iff 632 _).mp hc

/-! ## §9 THE CROWN V2 — one-and-a-half grants -/
#print axioms GhostExtinction406.cantorian_base  -- CK75 SECTION BOUNDARY

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
has-reader. -/
theorem hasTwo_of_digit : ∀ (n p : Nat), digit3 n p = 2 →
    hasTernaryTwo n = true := by
  intro n p
  induction p generalizing n with
  | zero =>
      intro h
      have h0 : digit3 n 0 = n % 3 := by
        unfold digit3
        rw [Nat.pow_zero, Nat.div_one]
      rw [h0] at h
      have hn0 : n ≠ 0 := by
        intro hne
        rw [hne, Nat.zero_mod] at h
        exact absurd h (by decide)
      rw [hasTernaryTwo.eq_def n, if_neg hn0, if_pos h]
  | succ p ih =>
      intro h
      have hsh : digit3 n (p+1) = digit3 (n / 3) p := by
        unfold digit3
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm (3^p) (3:Nat)]
      rw [hsh] at h
      have hne : n ≠ 0 := by
        intro h0
        rw [h0, Nat.zero_div] at h
        unfold digit3 at h
        rw [Nat.zero_div, Nat.zero_mod] at h
        exact absurd h (by decide)
      rw [hasTernaryTwo.eq_def n, if_neg hne]
      by_cases h2 : n % 3 = 2
      · rw [if_pos h2]
      · rw [if_neg h2]
        exact ih _ h

/-- **THE CROWN V2 (NEW).**  The FULL Erdős #406 statement —
`∀ n ≥ 9, noTernaryTwo (2^n) = false` — follows from the WEAKENED
grant pair:
* (G1') **ghost extinction on the rider sheet only**: no `u ≡ 1 mod 3`
  is a ghost ray (the `u ≡ 2` sheet is irrelevant — by the rider's
  core law, riders ride only the `u ≡ 1` sheet);
* (G2) **residual ghost compression** (unchanged).
Everything else is unconditional and machine-checked here. -/
theorem erdos406_crown_v2
    (hNoGhostOne : ∀ u : Nat, u % 3 = 1 → ¬ GhostRay u)
    (hComp : ∀ (K σ u : Nat), 500 < K → K = 3^σ * u → ¬ (3:Nat) ∣ u →
      CantorianPower K → GhostRay u) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  -- Step 1: no Cantorian power above eight
  have hnoCant : ∀ K : Nat, 8 ≤ K → ¬ CantorianPower K := by
    intro K hK8 hCant
    rcases Nat.lt_or_ge K 501 with hle | hgt
    · obtain ⟨p, hp⟩ := cantorian_base K hK8 (by omega)
      rcases Nat.eq_zero_or_pos p with h0 | hp1
      · rw [h0, digit3_pow4_zero] at hp
        exact absurd hp (by decide)
      · exact hCant p hp1 hp
    · obtain ⟨σ, u, hKu, hufree, hu1⟩ :=
        rider_core_one K (by omega) hCant
      exact hNoGhostOne u hu1 (hComp K σ u (by omega) hKu hufree hCant)
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
      congr 1
      omega
    exact has_two_imp_not_no_two (4^(n / 2)) hhas
  · have hnodd : n = 2 * (n / 2) + 1 := by omega
    have hmod : (2^n) % 3 = 2 := by
      rw [hnodd, Nat.pow_succ]
      have h2m : (2:Nat)^(2 * (n / 2)) % 3 = 1 := by
        rw [two_pow_two_mul]
        exact pow4_mod3 _
      rw [Nat.mul_mod, h2m]
    have hdig : digit3 (2^n) 0 = 2 := by
      unfold digit3
      rw [Nat.pow_zero, Nat.div_one, hmod]
    have hhas : hasTernaryTwo (2^n) = true :=
      hasTwo_of_digit (2^n) 0 hdig
    exact has_two_imp_not_no_two (2^n) hhas

/-- **THE COMPOSED WALL (NEW).**  Under the single grant (G2), every
Cantorian power above 500 exceeds `3^98` — the remaining content of
Erdős #406 is at most THREE astronomically large exponents, one per
π-family (at most one each, by the uniqueness collapse). -/
theorem rider_wall_v2
    (hComp : ∀ (K σ u : Nat), 500 < K → K = 3^σ * u → ¬ (3:Nat) ∣ u →
      CantorianPower K → GhostRay u)
    (K : Nat) (hK : 500 < K) (hCant : CantorianPower K) :
    3^98 < K := by
  obtain ⟨σ, u, hKu, hufree, hu1⟩ := rider_core_one K (by omega) hCant
  have hghost := hComp K σ u hK hKu hufree hCant
  have hsize := ghost_size_rider_sheet u hghost hu1
  have hmul : u ≤ 3^σ * u := by
    have hle : u ≤ u * 3^σ := Nat.le_mul_of_pos_right u (Nat.pow_pos (by decide))
    rw [Nat.mul_comm] at hle
    exact hle
  omega

/-! ## §10 Receipts -/

#check GhostExtinction406.rider_core_one
#check GhostExtinction406.ghost_head_split
#check GhostExtinction406.ghost_uniqueness
#check GhostExtinction406.W100_receipt
#check GhostExtinction406.pi100_fam4_receipt
#check GhostExtinction406.pi100_fam7_receipt
#check GhostExtinction406.pi100_fam1_receipt
#check GhostExtinction406.every_ghost_is_its_pi100_point_fam4
#check GhostExtinction406.every_ghost_is_its_pi100_point_fam7
#check GhostExtinction406.every_ghost_is_its_pi100_point_fam1
#check GhostExtinction406.ghost_size_rider_sheet
#check GhostExtinction406.cantorian_base
#check GhostExtinction406.erdos406_crown_v2
#check GhostExtinction406.rider_wall_v2

#print axioms GhostExtinction406.rider_core_one
#print axioms GhostExtinction406.ghost_head_split
#print axioms GhostExtinction406.ghost_uniqueness
#print axioms GhostExtinction406.W100_receipt
#print axioms GhostExtinction406.pi100_fam4_receipt
#print axioms GhostExtinction406.pi100_fam7_receipt
#print axioms GhostExtinction406.pi100_fam1_receipt
#print axioms GhostExtinction406.pi100_fam4_trit99
#print axioms GhostExtinction406.pi100_fam7_trit97
#print axioms GhostExtinction406.pi100_fam1_trit98
#print axioms GhostExtinction406.every_ghost_is_its_pi100_point_fam4
#print axioms GhostExtinction406.every_ghost_is_its_pi100_point_fam7
#print axioms GhostExtinction406.every_ghost_is_its_pi100_point_fam1
#print axioms GhostExtinction406.ghost_size_fam4
#print axioms GhostExtinction406.ghost_size_fam7
#print axioms GhostExtinction406.ghost_size_fam1
#print axioms GhostExtinction406.ghost_size_rider_sheet
#print axioms GhostExtinction406.cantorian_base
#print axioms GhostExtinction406.erdos406_crown_v2
#print axioms GhostExtinction406.rider_wall_v2

#eval "ERDOS406_GHOSTEXTINCTION_KERNEL_GREEN"

end GhostExtinction406
