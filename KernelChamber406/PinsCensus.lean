import KernelChamber406.PinsPins

-- KernelChamber406 split (S089): olean-cached part of the monolith kernel
-- Pins part 3/4: the finite base census (§7)
-- Pure module surgery: every declaration byte-identical to the monolith.

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

namespace PiCollapse406

/-! ## §7 The finite base — every exponent 8..500 fires -/
#print axioms PiCollapse406.every_ghost_is_its_pi_point_fam1  -- CK74 SECTION BOUNDARY

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
      · intro h; exact absurd h (by simp [hasTwoScan])
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
          simp [hasTwoScan, hbeq]
      · have hbeq : (n % 3 == 2) = false := by
          cases hbb : (n % 3 == 2) with
          | true =>
              have h22 : n % 3 = 2 := by simpa using hbb
              exact absurd h22 hb
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

/-- The census case: the exact digit scan of `4^(8+i)` at fuel 632
(every exponent in range has at most 631 ternary digits). -/
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
    have hc := (List.all_eq_true.mp base_chunk_one) (K - 8)
      (List.mem_range.mpr (by omega))
    unfold baseCaseB at hc
    rw [show 8 + (K - 8) = K from by omega] at hc
    obtain ⟨p, _, hd⟩ := (hasTwoScan_iff 632 _).mp hc
    exact ⟨p, hd⟩
    have hc := (List.all_eq_true.mp base_chunk_two) (K - 8 - 251)
      (List.mem_range.mpr (by omega))
    unfold baseCaseB at hc
    rw [show 8 + (251 + (K - 8 - 251)) = K from by omega] at hc
    obtain ⟨p, _, hd⟩ := (hasTwoScan_iff 632 _).mp hc
    exact ⟨p, hd⟩
end PiCollapse406
