import GSTGraphV2InfiniteControlScratch
import GSTGraphV2InfiniteBigNDichotomyScratch
import GSTGraphV2PhysicalSignedKernelTelescopeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-!
# Standalone earliest seed-zero Happy-gate chord

This is the production-facing form of the already-proved earliest-gate
argument.  It deliberately takes the physical seed-zero gate existence
itself, rather than the monolith-era `GSTNavigationWitness` wrapper, so the
final compositor remains independent of `ErdosTernary2.lean`.
-/

/-- Exact quotient split used by the physical x2 columns. -/
theorem gpt56_mul_ternary_quotient_split_standalone
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

/-- The earliest seed-zero Happy gate has a bad lower prefix, and in the
carry-three branch that prefix gives the sharp seven-eighths residue bound. -/
theorem gpt56_first_seedzero_gate_u_control
    (R : Nat)
    (hex : ∃ j,
      GSTInfiniteV2.gstDigitS R j = 2 ∧
        (GSTInfiniteV2.gstCarryS R j = 0 ∨
         GSTInfiniteV2.gstCarryS R j = 3)) :
    ∃ q,
      GSTInfiniteV2.gstDigitS R q = 2 ∧
      (GSTInfiniteV2.gstCarryS R q = 0 ∨
       GSTInfiniteV2.gstCarryS R q = 3) ∧
      (∀ j, j < q →
        GSTInfiniteV2.GSTBadPairS
          (GSTInfiniteV2.gstAffineCarryS 0 R j)
          (GSTInfiniteV2.gstDigitS R j)) ∧
      (GSTInfiniteV2.gstCarryS R q = 3 →
        8 * (R % 3^q) < 7 * 3^q) := by
  let q := Nat.find hex
  have hgate := Nat.find_spec hex
  have hbad : ∀ j, j < q →
      GSTInfiniteV2.GSTBadPairS
        (GSTInfiniteV2.gstAffineCarryS 0 R j)
        (GSTInfiniteV2.gstDigitS R j) := by
    intro j hj hhappy
    have hcarry :
        GSTInfiniteV2.gstCarryS R j = 0 ∨
        GSTInfiniteV2.gstCarryS R j = 3 := by
      simpa [GSTInfiniteV2.gstCarryS, GSTInfiniteV2.gstAffineCarryS]
        using hhappy.2
    have hqle : q ≤ j := by
      dsimp [q]
      exact Nat.find_min' hex ⟨hhappy.1, hcarry⟩
    omega
  refine ⟨q, hgate.1, hgate.2, hbad, ?_⟩
  intro hC3
  have hU := GSTInfiniteV2.gst_bad_prefix_u_potential_boundS
    0 R q (by decide) hbad
  have hcarryS : GSTInfiniteV2.gstAffineCarryS 0 R q = 3 := by
    simpa [GSTInfiniteV2.gstCarryS, GSTInfiniteV2.gstAffineCarryS] using hC3
  rw [hcarryS] at hU
  have hU' :
      24 * (R % 3^q) + 5 ≤ 3^q * 21 := by
    simpa [GSTInfiniteV2.gstHandwrittenUChargeS] using hU
  omega

/-- Production form of the short physical chord theorem.
At the earliest seed-zero Happy gate, NULL reaches its first BIG1 after one
x2 column and GST+ reaches it after three. -/
theorem gpt56_first_seedzero_gate_exact_binary_chord
    (R : Nat)
    (hex : ∃ j,
      GSTInfiniteV2.gstDigitS R j = 2 ∧
        (GSTInfiniteV2.gstCarryS R j = 0 ∨
         GSTInfiniteV2.gstCarryS R j = 3)) :
    ∃ q,
      (GSTInfiniteV2.gstDigitS R q = 2 ∧
        GSTInfiniteV2.gstCarryS R q = 0 ∧
        GSTFirstBig1AtS
          (fun r => GSTPhysicalKernel.binaryColumnDigit R q r) 1) ∨
      (GSTInfiniteV2.gstDigitS R q = 2 ∧
        GSTInfiniteV2.gstCarryS R q = 3 ∧
        GSTFirstBig1AtS
          (fun r => GSTPhysicalKernel.binaryColumnDigit R q r) 3) := by
  obtain ⟨q, hd2, hC, _hbad, hbound⟩ :=
    gpt56_first_seedzero_gate_u_control R hex
  have hp : 0 < 3^q := Nat.pow_pos (by decide)
  have hres : R % 3^q < 3^q := Nat.mod_lt _ hp
  have hd2raw : R / 3^q % 3 = 2 := by
    simpa [GSTInfiniteV2.gstDigitS] using hd2
  have hd0 : GSTPhysicalKernel.binaryColumnDigit R q 0 = 2 := by
    simpa [GSTPhysicalKernel.binaryColumnDigit, GSTInfiniteV2.gstDigitS] using hd2
  rcases hC with hC0 | hC3
  · have hC0' : (4 * (R % 3^q)) / 3^q = 0 := by
      simpa [GSTInfiniteV2.gstCarryS] using hC0
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
    have hq2 := gpt56_mul_ternary_quotient_split_standalone 2 R q
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
      simpa [GSTInfiniteV2.gstCarryS] using hC3
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
    have hq2 := gpt56_mul_ternary_quotient_split_standalone 2 R q
    have hq4 := gpt56_mul_ternary_quotient_split_standalone 4 R q
    have hq8 := gpt56_mul_ternary_quotient_split_standalone 8 R q
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

#check gpt56_first_seedzero_gate_u_control
#check gpt56_first_seedzero_gate_exact_binary_chord
#print axioms gpt56_first_seedzero_gate_u_control
#print axioms gpt56_first_seedzero_gate_exact_binary_chord
