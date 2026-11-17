import GSTHandwrittenBigNSignedKernel
import GSTCanonicalFirstGateControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-!
# Canonical energy retained at the live BIG-N boundary

The former collision packet remembered the child gate, its first BIG1
coordinate, the three-world code, the signed kernel, and the parent bad trace.
It did not retain the equation that distinguishes the canonical child from an
arbitrary natural.  That omission is mathematically material: the corresponding
affine child-to-parent transport is false for arbitrary naturals.

This packet keeps the exact perfect-power energy in the same theorem object.
It asserts no transport conclusion and introduces no interface assumption.
-/

/-- The live BIG-N packet together with the exact perfect-power equation for
the child Navigation Constant. -/
theorem gpt56_prefix_one_live_bigN_full_energy_packet
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let X := c s / 3 + A*T
    (∃ q N,
      gstDigit T q = 2 ∧
      (gstCarry T q = 0 ∨ gstCarry T q = 3) ∧
      1 ≤ N ∧
      GSTInformationEqualsBigNS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N ∧
      gstBig1ProjectedPathCodeS
        (fun r => GSTPhysicalKernel.binaryColumnCarry T q r)
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N =
          5 * Finset.sum (Finset.range (N-1)) (fun j => 2^j * 3^j) +
            4 * (2^(N-1) * 3^(N-1)) ∧
      Finset.sum (Finset.range N)
        (fun r => GSTPhysicalKernel.signedKernelTwice
          (GSTPhysicalKernel.binaryColumnCarry T q r)
          (GSTPhysicalKernel.binaryColumnDigit T q r)) =
            7 * ((N : Int) - 3) ∧
      GSTSeededAffineBadTrace 1 X) ∧
    4^(3^(s+1) * n) = 1 + 3^(s+2) * T := by
  dsimp only
  constructor
  · simpa only using
      gpt56_prefix_one_live_bigN_full_equation_packet
        s n hs hn hchild hBad
  · exact gst_navigation_decomposition (s+1) n (by omega)

/-- The canonical earliest gate, its exact short BIG-N chord, the complete
three-world and signed-kernel equations, the parent bad trace, and the original
perfect-power energy are retained together.  In particular BIG-N is always
inside the full horizontal parent multiplier when `s ≥ 1`. -/
theorem gpt56_prefix_one_live_short_bigN_energy_packet
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let X := c s / 3 + A*T
    ∃ q N,
      gstDigit T q = 2 ∧
      (gstCarry T q = 0 ∨ gstCarry T q = 3) ∧
      (N = 1 ∨ N = 3) ∧
      1 ≤ N ∧
      GSTInformationEqualsBigNS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N ∧
      N ≤ 2 * 3^s ∧
      gstBig1ProjectedPathCodeS
        (fun r => GSTPhysicalKernel.binaryColumnCarry T q r)
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N =
          5 * Finset.sum (Finset.range (N-1)) (fun j => 2^j * 3^j) +
            4 * (2^(N-1) * 3^(N-1)) ∧
      Finset.sum (Finset.range N)
        (fun r => GSTPhysicalKernel.signedKernelTwice
          (GSTPhysicalKernel.binaryColumnCarry T q r)
          (GSTPhysicalKernel.binaryColumnDigit T q r)) =
            7 * ((N : Int) - 3) ∧
      GSTSeededAffineBadTrace 1 X ∧
      4^(3^(s+1) * n) = 1 + 3^(s+2) * T := by
  dsimp only
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let X := c s / 3 + A*T
  obtain ⟨q, N, hd2, hC, hNcases, hfirst⟩ :=
    gpt56_first_navigation_gate_short_big1 T hchild
  have hN : 1 ≤ N := by
    rcases hNcases with h1 | h3 <;> omega
  have h3pow : 3 ≤ 3^s :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hs
  have hwidth : N ≤ 2 * 3^s := by
    rcases hNcases with h1 | h3 <;> omega
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_binary_row_path T q
  have hd0eq : d 0 = 2 := by
    dsimp [d]
    simpa [GSTPhysicalKernel.binaryColumnDigit, gstDigit] using hd2
  have hd0 : d 0 ≠ 0 := by omega
  have hbig : GSTInformationEqualsBigNS d N := by
    simpa [GSTInformationEqualsBigNS, d] using hfirst
  have hcode := gst_information_eq_bigN_exact_sum_equationS
    a d hpath hd0 N hN hbig
  have hkernel := gpt56_information_bigN_signed_kernel_exact
    T q N hd2 hN (by simpa [d] using hbig)
  have hseeded : GSTSeededAffineBadTrace 1 X := by
    have h := (gst_omega_infiniteBadTrace_iff_seededAffine s 1 n).1 hBad
    have hseed : (4 * (c s % 3^1)) / 3^1 = 1 := by
      rw [Nat.pow_one, c_mod3 s hs]
    rw [hseed] at h
    simpa [T, A, X] using h
  have henergy : 4^(3^(s+1) * n) = 1 + 3^(s+2) * T := by
    dsimp [T]
    exact gst_navigation_decomposition (s+1) n (by omega)
  exact ⟨q, N, hd2, hC, hNcases, hN, hbig, hwidth,
    by simpa [a, d] using hcode, hkernel, hseeded, henergy⟩

/-- Fully resolved earliest-chord packet.  The NULL and GST+ alternatives
retain their correlated first-BIG1 coordinate, exact three-world code, and
signed kernel, so the downstream incidence argument has no symbolic BIG-N
case left to reconstruct. -/
theorem gpt56_prefix_one_live_exact_chord_energy_packet
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let X := c s / 3 + A*T
    ∃ q,
      ((gstDigit T q = 2 ∧
        gstCarry T q = 0 ∧
        GSTFirstBig1AtS
          (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) 1 ∧
        gstBig1ProjectedPathCodeS
          (fun r => GSTPhysicalKernel.binaryColumnCarry T q r)
          (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) 1 = 4 ∧
        Finset.sum (Finset.range 1)
          (fun r => GSTPhysicalKernel.signedKernelTwice
            (GSTPhysicalKernel.binaryColumnCarry T q r)
            (GSTPhysicalKernel.binaryColumnDigit T q r)) = (-14 : Int)) ∨
       (gstDigit T q = 2 ∧
        gstCarry T q = 3 ∧
        GSTFirstBig1AtS
          (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) 3 ∧
        gstBig1ProjectedPathCodeS
          (fun r => GSTPhysicalKernel.binaryColumnCarry T q r)
          (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) 3 = 179 ∧
        Finset.sum (Finset.range 3)
          (fun r => GSTPhysicalKernel.signedKernelTwice
            (GSTPhysicalKernel.binaryColumnCarry T q r)
            (GSTPhysicalKernel.binaryColumnDigit T q r)) = 0)) ∧
      GSTSeededAffineBadTrace 1 X ∧
      4^(3^(s+1) * n) = 1 + 3^(s+2) * T := by
  dsimp only
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let X := c s / 3 + A*T
  obtain ⟨q, hchord⟩ :=
    gpt56_first_navigation_gate_exact_binary_chord T hchild
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_binary_row_path T q
  have hseeded : GSTSeededAffineBadTrace 1 X := by
    have h := (gst_omega_infiniteBadTrace_iff_seededAffine s 1 n).1 hBad
    have hseed : (4 * (c s % 3^1)) / 3^1 = 1 := by
      rw [Nat.pow_one, c_mod3 s hs]
    rw [hseed] at h
    simpa [T, A, X] using h
  have henergy : 4^(3^(s+1) * n) = 1 + 3^(s+2) * T := by
    dsimp [T]
    exact gst_navigation_decomposition (s+1) n (by omega)
  rcases hchord with hnull | hplus
  · have hd0 : d 0 ≠ 0 := by
      have hd0eq : d 0 = 2 := by
        dsimp [d]
        simpa [GSTPhysicalKernel.binaryColumnDigit, gstDigit] using hnull.1
      omega
    have hbig : GSTInformationEqualsBigNS d 1 := by
      simpa [GSTInformationEqualsBigNS, d] using hnull.2.2
    have hcode := gst_information_eq_bigN_exact_sum_equationS
      a d hpath hd0 1 (by decide) hbig
    have hkernel := gpt56_information_bigN_signed_kernel_exact
      T q 1 hnull.1 (by decide) (by simpa [d] using hbig)
    norm_num at hcode hkernel
    refine ⟨q, Or.inl ⟨hnull.1, hnull.2.1, hnull.2.2, ?_, ?_⟩,
      hseeded, henergy⟩
    · simpa [a, d] using hcode
    · simpa [T] using hkernel
  · have hd0 : d 0 ≠ 0 := by
      have hd0eq : d 0 = 2 := by
        dsimp [d]
        simpa [GSTPhysicalKernel.binaryColumnDigit, gstDigit] using hplus.1
      omega
    have hbig : GSTInformationEqualsBigNS d 3 := by
      simpa [GSTInformationEqualsBigNS, d] using hplus.2.2
    have hcode := gst_information_eq_bigN_exact_sum_equationS
      a d hpath hd0 3 (by decide) hbig
    have hkernel := gpt56_information_bigN_signed_kernel_exact
      T q 3 hplus.1 (by decide) (by simpa [d] using hbig)
    norm_num at hcode hkernel
    refine ⟨q, Or.inr ⟨hplus.1, hplus.2.1, hplus.2.2, ?_, ?_⟩,
      hseeded, henergy⟩
    · simpa [a, d] using hcode
    · simpa [T] using hkernel

#check gpt56_prefix_one_live_bigN_full_energy_packet
#check gpt56_prefix_one_live_short_bigN_energy_packet
#check gpt56_prefix_one_live_exact_chord_energy_packet
#print axioms gpt56_prefix_one_live_bigN_full_energy_packet
#print axioms gpt56_prefix_one_live_short_bigN_energy_packet
#print axioms gpt56_prefix_one_live_exact_chord_energy_packet
