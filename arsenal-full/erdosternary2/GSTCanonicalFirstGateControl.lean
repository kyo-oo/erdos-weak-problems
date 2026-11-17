import GSTHandwrittenChildFirstBig1
import GSTGraphV2InfiniteControlScratch
import GSTGraphV2InfiniteBigNDichotomyScratch
import GSTGraphV2PhysicalSignedKernelTelescopeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-!
# Earliest canonical Happy-Gate control

An arbitrary Happy Gate need not have a short physical BIG1 chord.  The
earliest gate does: every lower row is a bad prefix, so the all-scale U
potential controls the lower ternary residue.  In the carry-three case this
gives the sharp inequality needed by the first three binary columns.
-/

/-- Exact quotient split for multiplying a natural while keeping its lower
ternary residue and upper digit word separate. -/
theorem gpt56_mul_ternary_quotient_split
    (k R p : Nat) :
    (k * R) / 3^p =
      (k * (R % 3^p)) / 3^p + k * (R / 3^p) := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : R = 3^p * (R / 3^p) + R % 3^p :=
    (Nat.div_add_mod R (3^p)).symm
  calc
    (k*R) / 3^p =
        (k * (3^p * (R / 3^p) + R % 3^p)) / 3^p := by rw [← hsplit]
    _ = (k * (R % 3^p) + 3^p * (k * (R / 3^p))) / 3^p := by
      congr 1
      rw [Nat.mul_add]
      ac_rfl
    _ = (k * (R % 3^p)) / 3^p + k * (R / 3^p) := by
      rw [Nat.add_mul_div_left _ _ hp]

/-- A Navigation witness has an earliest digit-two gate.  Below it the exact
four-state bad language holds, and a carry-three earliest gate has lower
residue strictly below seven eighths of its ternary place. -/
theorem gpt56_first_navigation_gate_u_control
    (R : Nat) (hnav : GSTNavigationWitness R) :
    ∃ q,
      gstDigit R q = 2 ∧
      (gstCarry R q = 0 ∨ gstCarry R q = 3) ∧
      (∀ j, j < q →
        GSTBadPairS (gstAffineCarryS 0 R j) (gstDigitS R j)) ∧
      (gstCarry R q = 3 → 8 * (R % 3^q) < 7 * 3^q) := by
  have hex : ∃ j,
      gstDigit R j = 2 ∧
        (gstCarry R j = 0 ∨ gstCarry R j = 3) := by
    obtain ⟨j, hd2, hspace⟩ := hnav
    have hCmod : gstCarry R j % 3 = 0 :=
      gstGoodSpace_carry_mod3_zero R j hspace
    have hClt : gstCarry R j < 4 := by
      cases j with
      | zero =>
          simp only [gstCarry, Nat.pow_zero, Nat.mod_one, Nat.mul_zero,
            Nat.zero_div]
          decide
      | succ k => exact gstCarry_lt_four R (k+1) (by omega)
    have hC : gstCarry R j = 0 ∨ gstCarry R j = 3 := by omega
    exact ⟨j, hd2, hC⟩
  let q := Nat.find hex
  have hgate := Nat.find_spec hex
  have hbad : ∀ j, j < q →
      GSTBadPairS (gstAffineCarryS 0 R j) (gstDigitS R j) := by
    intro j hj hhappy
    have hgood :
        gstDigit R j = 2 ∧
          (gstCarry R j = 0 ∨ gstCarry R j = 3) := by
      simpa [GSTHappyPairS, gstAffineCarryS, gstDigitS, gstDigit, gstCarry]
        using hhappy
    have hqle : q ≤ j := by
      dsimp [q]
      exact Nat.find_min' hex hgood
    omega
  refine ⟨q, hgate.1, hgate.2, hbad, ?_⟩
  intro hC3
  have hU := gst_bad_prefix_u_potential_boundS 0 R q (by decide) hbad
  have hcarryS : gstAffineCarryS 0 R q = 3 := by
    simpa [gstAffineCarryS, gstCarry] using hC3
  rw [hcarryS] at hU
  have hU' :
      24 * (R % 3^q) + 5 ≤ 3^q * 21 := by
    simpa [gstHandwrittenUChargeS] using hU
  omega

/-- At the earliest Navigation gate, the two possible Happy spaces determine
the complete short physical chord: NULL reaches its first BIG1 after one x2
column, while GST+ reaches its first BIG1 after three.  The carry/chord
correlation is retained rather than projected to two independent disjunctions. -/
theorem gpt56_first_navigation_gate_exact_binary_chord
    (R : Nat) (hnav : GSTNavigationWitness R) :
    ∃ q,
      (gstDigit R q = 2 ∧
        gstCarry R q = 0 ∧
        GSTFirstBig1AtS
          (fun r => GSTPhysicalKernel.binaryColumnDigit R q r) 1) ∨
      (gstDigit R q = 2 ∧
        gstCarry R q = 3 ∧
        GSTFirstBig1AtS
          (fun r => GSTPhysicalKernel.binaryColumnDigit R q r) 3) := by
  obtain ⟨q, hd2, hC, _hbad, hbound⟩ :=
    gpt56_first_navigation_gate_u_control R hnav
  have hp : 0 < 3^q := Nat.pow_pos (by decide)
  have hres : R % 3^q < 3^q := Nat.mod_lt _ hp
  have hd2raw : R / 3^q % 3 = 2 := by
    simpa [gstDigit] using hd2
  have hd0 : GSTPhysicalKernel.binaryColumnDigit R q 0 = 2 := by
    simpa [GSTPhysicalKernel.binaryColumnDigit, gstDigit] using hd2
  rcases hC with hC0 | hC3
  · have hC0' : (4 * (R % 3^q)) / 3^q = 0 := by
      simpa [gstCarry] using hC0
    have hrem4 : (4 * (R % 3^q)) % 3^q < 3^q := Nat.mod_lt _ hp
    have hsplit4 :
        4 * (R % 3^q) =
          3^q * ((4 * (R % 3^q)) / 3^q) +
            (4 * (R % 3^q)) % 3^q :=
      (Nat.div_add_mod (4 * (R % 3^q)) (3^q)).symm
    rw [hC0'] at hsplit4
    have h2lt : 2 * (R % 3^q) < 3^q := by omega
    have hdiv2 : (2 * (R % 3^q)) / 3^q = 0 :=
      Nat.div_eq_of_lt h2lt
    have hq2 := gpt56_mul_ternary_quotient_split 2 R q
    have hd1 : GSTPhysicalKernel.binaryColumnDigit R q 1 = 1 := by
      unfold GSTPhysicalKernel.binaryColumnDigit
      norm_num
      rw [hq2, Nat.add_mod, Nat.mul_mod, hdiv2, hd2raw]
    have hfirst : GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit R q r) 1 := by
      constructor
      · exact hd1
      · intro j hj
        have hj0 : j = 0 := by omega
        subst j
        change GSTPhysicalKernel.binaryColumnDigit R q 0 ≠ 1
        omega
    exact ⟨q, Or.inl ⟨hd2, hC0, hfirst⟩⟩
  · have hC3' : (4 * (R % 3^q)) / 3^q = 3 := by
      simpa [gstCarry] using hC3
    have hrem4 : (4 * (R % 3^q)) % 3^q < 3^q := Nat.mod_lt _ hp
    have hsplit4 :
        4 * (R % 3^q) =
          3^q * ((4 * (R % 3^q)) / 3^q) +
            (4 * (R % 3^q)) % 3^q :=
      (Nat.div_add_mod (4 * (R % 3^q)) (3^q)).symm
    rw [hC3'] at hsplit4
    have h4lo : 3 * 3^q ≤ 4 * (R % 3^q) := by omega
    have h2lo : 3^q ≤ 2 * (R % 3^q) := by omega
    have h2hi : 2 * (R % 3^q) < 2 * 3^q := by omega
    have hdiv2lo : 1 ≤ (2 * (R % 3^q)) / 3^q :=
      (Nat.le_div_iff_mul_le hp).2 (by simpa using h2lo)
    have hdiv2hi : (2 * (R % 3^q)) / 3^q < 2 :=
      (Nat.div_lt_iff_lt_mul hp).2 (by simpa using h2hi)
    have hdiv2 : (2 * (R % 3^q)) / 3^q = 1 := by omega
    have hq2 := gpt56_mul_ternary_quotient_split 2 R q
    have hq4 := gpt56_mul_ternary_quotient_split 4 R q
    have hq8 := gpt56_mul_ternary_quotient_split 8 R q
    have hd1 : GSTPhysicalKernel.binaryColumnDigit R q 1 = 2 := by
      unfold GSTPhysicalKernel.binaryColumnDigit
      norm_num
      rw [hq2, Nat.add_mod, Nat.mul_mod, hdiv2, hd2raw]
    have hd2col : GSTPhysicalKernel.binaryColumnDigit R q 2 = 2 := by
      unfold GSTPhysicalKernel.binaryColumnDigit
      norm_num
      rw [hq4, Nat.add_mod, Nat.mul_mod, hC3', hd2raw]
    have h8lo : 6 * 3^q ≤ 8 * (R % 3^q) := by omega
    have h8hi : 8 * (R % 3^q) < 7 * 3^q := hbound hC3
    have hdiv8lo : 6 ≤ (8 * (R % 3^q)) / 3^q :=
      (Nat.le_div_iff_mul_le hp).2 (by simpa using h8lo)
    have hdiv8hi : (8 * (R % 3^q)) / 3^q < 7 :=
      (Nat.div_lt_iff_lt_mul hp).2 (by simpa using h8hi)
    have hdiv8 : (8 * (R % 3^q)) / 3^q = 6 := by omega
    have hd3 : GSTPhysicalKernel.binaryColumnDigit R q 3 = 1 := by
      unfold GSTPhysicalKernel.binaryColumnDigit
      norm_num
      rw [hq8, Nat.add_mod, Nat.mul_mod, hdiv8, hd2raw]
    have hfirst : GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit R q r) 3 := by
      constructor
      · exact hd3
      · intro j hj
        have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases hjcases with h0 | h1 | h2
        · subst j
          change GSTPhysicalKernel.binaryColumnDigit R q 0 ≠ 1
          omega
        · subst j
          change GSTPhysicalKernel.binaryColumnDigit R q 1 ≠ 1
          omega
        · subst j
          change GSTPhysicalKernel.binaryColumnDigit R q 2 ≠ 1
          omega
    exact ⟨q, Or.inr ⟨hd2, hC3, hfirst⟩⟩

/-- Projected short-BIG1 form used by the canonical energy packet. -/
theorem gpt56_first_navigation_gate_short_big1
    (R : Nat) (hnav : GSTNavigationWitness R) :
    ∃ q N,
      gstDigit R q = 2 ∧
      (gstCarry R q = 0 ∨ gstCarry R q = 3) ∧
      (N = 1 ∨ N = 3) ∧
      GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit R q r) N := by
  obtain ⟨q, hnull | hplus⟩ :=
    gpt56_first_navigation_gate_exact_binary_chord R hnav
  · exact ⟨q, 1, hnull.1, Or.inl hnull.2.1, Or.inl rfl, hnull.2.2⟩
  · exact ⟨q, 3, hplus.1, Or.inr hplus.2.1, Or.inr rfl, hplus.2.2⟩

#check gpt56_first_navigation_gate_u_control
#check gpt56_first_navigation_gate_exact_binary_chord
#check gpt56_first_navigation_gate_short_big1
#print axioms gpt56_first_navigation_gate_u_control
#print axioms gpt56_first_navigation_gate_exact_binary_chord
#print axioms gpt56_first_navigation_gate_short_big1
