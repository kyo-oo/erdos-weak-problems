/-- CENSUS CHUNK 0: rows a ∈ [0, 500) — no coprime 4-powerful sum in the
first block (ONE decide, ≤ 500 rows — the 501 law). -/
theorem e939_sweep_block0 :
    (List.range 1500).all (fun a => e939Block 0 a) = true := by decide

/-- CENSUS CHUNK 1: rows a ∈ [500, 1000) — no coprime 4-powerful sum in
the second block (ONE decide, ≤ 500 rows). -/
theorem e939_sweep_block1 :
    (List.range 1500).all (fun a => e939Block 500 a) = true := by decide

/-- CENSUS CHUNK 2: rows a ∈ [1000, 1500) — no coprime 4-powerful sum in
the third block (ONE decide, ≤ 500 rows). -/
theorem e939_sweep_block2 :
    (List.range 1500).all (fun a => e939Block 1000 a) = true := by decide

/-- THE BLOCK-GUARD DECODE: a true block row inside its block forces the
row walker true (the E850 hstep restatement pattern). -/
theorem e939Block_decode (lo a : Nat) (hlo : lo ≤ a) (hhi : a < lo + 500)
    (h : e939Block lo a = true) : e939Row a = true := by
  have h' : (if lo ≤ a ∧ a < lo + 500 then e939Row a else true) = true := h
  rw [if_pos ⟨hlo, hhi⟩] at h'
  exact h'

/-- THE ROW-WALKER DECODE: a true row plus a genuine coprime
both-4-powerful pair with a 4-powerful sum is absurd. -/
theorem e939Row_decode (a b : Nat) (hrow : e939Row a = true)
    (hpa : rpow 4 a = true) (hb : b < 1500) (hpb : rpow 4 b = true)
    (hg : Nat.gcd a b = 1) (hsum : rpow 4 (a + b) = true) : False := by
  have h3 : (if rpow 4 a = true then
      (List.range 1500).all (fun b =>
        if rpow 4 b = true then
          (if Nat.gcd a b = 1 then (if rpow 4 (a + b) = true then false else true)
          else true)
        else true)
      else true) = true := hrow
  rw [if_pos hpa] at h3
  have h4 : (fun b => if rpow 4 b = true then
        (if Nat.gcd a b = 1 then (if rpow 4 (a + b) = true then false else true)
        else true)
        else true) b = true :=
    (List.all_eq_true.mp h3) b (List.mem_range.mpr (by omega))
  have h5 : (if rpow 4 b = true then
        (if Nat.gcd a b = 1 then (if rpow 4 (a + b) = true then false else true)
        else true)
        else true) = true := h4
  rw [if_pos hpb, if_pos hg, if_pos hsum] at h5
  exact Bool.noConfusion h5

/-- THE BOUNDED COPRIME NO-SOLUTION MASTER (the mini-hunt's zero at the
decide-safe 1500-box, assembled from the three chunks via the decodes —
NO decide on the nested quantifier): no coprime pair a, b < 1500 with all
three of rpow 4 a, rpow 4 b, rpow 4 (a + b) true (a + b < 3000 ≤ 10^4, so this
window sits inside the battery's certified zero). -/
theorem e939_no_small_sum_1500 :
    ∀ a < 1500, ∀ b < 1500, rpow 4 a = true → rpow 4 b = true →
    Nat.gcd a b = 1 → rpow 4 (a + b) = false := by
  intro a ha b hb hpa hpb hg hsum
  rcases Nat.lt_or_ge a 500 with h1 | h1
  · have hr := (List.all_eq_true.mp e939_sweep_block0) a
      (List.mem_range.mpr (by omega))
    exact (e939Row_decode a b (e939Block_decode 0 a (by omega) h1 hr)
      hpa hb hpb hg hsum).elim
  · rcases Nat.lt_or_ge a 1000 with h2 | h2
    · have hr := (List.all_eq_true.mp e939_sweep_block1) a
        (List.mem_range.mpr (by omega))
      exact (e939Row_decode a b (e939Block_decode 500 a h1 h2 hr)
        hpa hb hpb hg hsum).elim
    · have hr := (List.all_eq_true.mp e939_sweep_block2) a
        (List.mem_range.mpr (by omega))
      exact (e939Row_decode a b (e939Block_decode 1000 a h2 (by omega) hr)
        hpa hb hpb hg hsum).elim

end E939
