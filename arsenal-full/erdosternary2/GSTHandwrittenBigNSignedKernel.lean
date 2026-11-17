import GSTHandwrittenBigNThreeWorldFactors

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-- At literal `I = BIG-N`, the handwritten signed seven-kernel has a closed
physical value.  Every edge before the final boundary is BIG2->BIG2 SURVIVE;
the last edge is BIG2->BIG1 DESTROY.  Hence the exact telescope is

    7 * (N - 3)

in the integer chart used by the signed kernel. -/
theorem gpt56_information_bigN_signed_kernel_exact
    (R p N : Nat)
    (hd2 : gstDigit R p = 2)
    (hN : 1 ≤ N)
    (hbig : GSTInformationEqualsBigNS
      (fun r => GSTPhysicalKernel.binaryColumnDigit R p r) N) :
    Finset.sum (Finset.range N)
      (fun r => GSTPhysicalKernel.signedKernelTwice
        (GSTPhysicalKernel.binaryColumnCarry R p r)
        (GSTPhysicalKernel.binaryColumnDigit R p r)) =
      7 * ((N : Int) - 3) := by
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry R p r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit R p r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_binary_row_path R p
  have hd0eq : d 0 = 2 := by
    dsimp [d]
    simpa [GSTPhysicalKernel.binaryColumnDigit, gstDigit] using hd2
  have hd0 : d 0 ≠ 0 := by omega
  have hshape := gst_information_eq_bigN_exact_path_shapeS
    a d hpath hd0 N hN (by simpa [d] using hbig)
  have hdN : d N = 1 := hshape.1
  cases N with
  | zero => omega
  | succ K =>
      have hpre : ∀ j, j < K+1 → d j = 2 := by
        simpa using hshape.2
      have hsum :
          Finset.sum (Finset.range (K+1))
            (fun r => GSTPhysicalKernel.twoIndicator (d r) *
              GSTPhysicalKernel.twoIndicator (d (r+1))) = (K : Int) := by
        rw [Finset.sum_range_succ]
        have hdK : d K = 2 := hpre K (by omega)
        have hdKN : d (K+1) = 1 := by simpa using hdN
        have hlast :
            GSTPhysicalKernel.twoIndicator (d K) *
              GSTPhysicalKernel.twoIndicator (d (K+1)) = 0 := by
          simp [GSTPhysicalKernel.twoIndicator, hdK, hdKN]
        rw [hlast, add_zero]
        calc
          Finset.sum (Finset.range K)
              (fun r => GSTPhysicalKernel.twoIndicator (d r) *
                GSTPhysicalKernel.twoIndicator (d (r+1))) =
              Finset.sum (Finset.range K) (fun _ => (1 : Int)) := by
                apply Finset.sum_congr rfl
                intro r hr
                have hrK : r < K := Finset.mem_range.mp hr
                have hdr : d r = 2 := hpre r (by omega)
                have hdr1 : d (r+1) = 2 := hpre (r+1) (by omega)
                simp [GSTPhysicalKernel.twoIndicator, hdr, hdr1]
          _ = (K : Int) := by simp
      rw [GSTPhysicalKernel.signedKernelTwice_physical_telescope]
      change
        14 * (GSTPhysicalKernel.twoIndicator (d (K+1)) -
          GSTPhysicalKernel.twoIndicator (d 0)) +
          7 * Finset.sum (Finset.range (K+1))
            (fun r => GSTPhysicalKernel.twoIndicator (d r) *
              GSTPhysicalKernel.twoIndicator (d (r+1))) =
        7 * (((K+1 : Nat) : Int) - 3)
      rw [hsum]
      have hd0' : d 0 = 2 := hd0eq
      have hdN' : d (K+1) = 1 := by simpa using hdN
      simp [GSTPhysicalKernel.twoIndicator, hd0', hdN']
      push_cast
      ring

/-- Live prefix-one specialization: the child Navigation gate, its literal
BIG-N coordinate, the exact `2^j/3^j/6^j` word, and the signed seven-kernel are
all one physical packet. -/
theorem gpt56_prefix_one_live_bigN_full_equation_packet
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let X := c s / 3 + A*T
    ∃ q N,
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
      GSTSeededAffineBadTrace 1 X := by
  dsimp only
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let X := c s / 3 + A*T
  obtain ⟨q, N, hd2, hC, hN, hbig, heq, hseeded⟩ :=
    gpt56_prefix_one_live_information_bigN_sum_equation
      s n hs hn hchild hBad
  have hkernel := gpt56_information_bigN_signed_kernel_exact
    T q N hd2 hN hbig
  exact ⟨q, N, hd2, hC, hN, hbig, heq, hkernel,
    by simpa [T, A, X] using hseeded⟩

#check gpt56_information_bigN_signed_kernel_exact
#check gpt56_prefix_one_live_bigN_full_equation_packet
#print axioms gpt56_information_bigN_signed_kernel_exact
#print axioms gpt56_prefix_one_live_bigN_full_equation_packet
