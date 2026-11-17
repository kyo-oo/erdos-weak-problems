import GSTHandwrittenPrefixOneLivePackage

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-!
# Handwritten I = BIG-N and 2^j / 3^j / 6^j factor surgery

The handwritten BIG-N branch already had its operational content in
`GSTFirstBig1AtS`: N is the first natural information coordinate at which the
physical bridge reaches BIG1.  This file exposes that content under the literal
`I = BIG-N` name and couples it to the three exponential worlds appearing in
the handwritten operator.
-/

/-- Literal handwritten `I = BIG-N`: the information path first reaches BIG1
at coordinate N. -/
def GSTInformationEqualsBigNS (d : Nat → Nat) (N : Nat) : Prop :=
  GSTFirstBig1AtS d N

/-- Binary-world exponential factor. -/
def gstBinaryWorldFactorS (j : Nat) : Nat := 2^j

/-- Ternary-world exponential factor. -/
def gstTernaryWorldFactorS (j : Nat) : Nat := 3^j

/-- Mixed six-state-world exponential factor. -/
def gstMixedWorldFactorS (j : Nat) : Nat := 6^j

/-- Exact packet of the three handwritten exponential worlds at one depth. -/
structure GSTThreeWorldExponentialPacketS where
  binary : Nat
  ternary : Nat
  mixed : Nat
  deriving Repr, DecidableEq

def gstThreeWorldExponentialPacketS (j : Nat) : GSTThreeWorldExponentialPacketS :=
  ⟨gstBinaryWorldFactorS j, gstTernaryWorldFactorS j, gstMixedWorldFactorS j⟩

/-- `I = BIG-N` is exactly the existing first-BIG1 condition. -/
theorem gst_information_eq_bigN_iffS
    (d : Nat → Nat) (N : Nat) :
    GSTInformationEqualsBigNS d N ↔
      d N = 1 ∧ ∀ j, j < N → d j ≠ 1 := by
  rfl

/-- The mixed world is not an independent scale: at every natural depth it is
exactly the product of the binary and ternary exponential factors. -/
theorem gst_three_world_factor_rawS (j : Nat) :
    6^j = 2^j * 3^j := by
  have h6 : (6 : Nat) = 2 * 3 := by decide
  rw [h6, mul_pow]

/-- Named-factor form of the same exact three-world identity. -/
theorem gst_three_world_mixed_factor_exactS (j : Nat) :
    gstMixedWorldFactorS j =
      gstBinaryWorldFactorS j * gstTernaryWorldFactorS j := by
  unfold gstMixedWorldFactorS gstBinaryWorldFactorS gstTernaryWorldFactorS
  exact gst_three_world_factor_rawS j

/-- All three exponential worlds respect concatenation of information depth. -/
theorem gst_three_world_factor_addS (j k : Nat) :
    gstBinaryWorldFactorS (j+k) =
        gstBinaryWorldFactorS j * gstBinaryWorldFactorS k ∧
    gstTernaryWorldFactorS (j+k) =
        gstTernaryWorldFactorS j * gstTernaryWorldFactorS k ∧
    gstMixedWorldFactorS (j+k) =
        gstMixedWorldFactorS j * gstMixedWorldFactorS k := by
  simp [gstBinaryWorldFactorS, gstTernaryWorldFactorS,
    gstMixedWorldFactorS, pow_add]

/-- Before literal `I = BIG-N`, every information vertex of a nonzero physical
bridge is BIG2, while coordinate N itself is BIG1. -/
theorem gst_information_eq_bigN_exact_path_shapeS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hbig : GSTInformationEqualsBigNS d N) :
    d N = 1 ∧ ∀ j, j < N → d j = 2 := by
  change GSTFirstBig1AtS d N at hbig
  exact ⟨hbig.1,
    gst_before_first_big1_all_big2S a d hpath h0 N hN hbig⟩

/-- Exact BIG-N projected code written simultaneously in all three worlds.
The old `5*6^(N-1)-1` code is now explicitly
`5*(2^(N-1)*3^(N-1))-1`. -/
theorem gst_information_eq_bigN_exact_three_world_codeS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hbig : GSTInformationEqualsBigNS d N) :
    gstBig1ProjectedPathCodeS a d N =
      5 * (gstBinaryWorldFactorS (N-1) *
        gstTernaryWorldFactorS (N-1)) - 1 := by
  change GSTFirstBig1AtS d N at hbig
  calc
    gstBig1ProjectedPathCodeS a d N = 5 * 6^(N-1) - 1 :=
      gst_first_big1_exact_bigN_codeS a d hpath h0 N hN hbig
    _ = 5 * (2^(N-1) * 3^(N-1)) - 1 := by
      rw [gst_three_world_factor_rawS (N-1)]
    _ = 5 * (gstBinaryWorldFactorS (N-1) *
        gstTernaryWorldFactorS (N-1)) - 1 := by
      rfl

/-- Literal joined prefix from the handwritten equation.  Every completed
microscopic world before BIG-N contributes the aligned factor `2^j * 3^j`,
weighted by the five-unit full SURVIVE mass. -/
def gstHandwrittenThreeWorldJoinedPrefixS (K : Nat) : Nat :=
  5 * Finset.sum (Finset.range K)
    (fun j => gstBinaryWorldFactorS j * gstTernaryWorldFactorS j)

/-- The three exponent worlds collapse exactly to the mixed six-world geometric
prefix.  This is the finite equation-level `2^j ∪ 3^j ∪ 6^j` identity. -/
theorem gst_handwritten_three_world_joined_prefix_closedS (K : Nat) :
    gstHandwrittenThreeWorldJoinedPrefixS K = 6^K - 1 := by
  unfold gstHandwrittenThreeWorldJoinedPrefixS
  unfold gstBinaryWorldFactorS gstTernaryWorldFactorS
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      rw [← gst_three_world_factor_rawS K, Nat.pow_succ]
      have hp : 0 < 6^K := Nat.pow_pos (by decide)
      omega

/-- The exact finite `I = BIG-N` equation.  The first-BIG1 physical word is
not merely `5*6^(N-1)-1`: it is literally the joined three-world prefix

  5 * Σ_{j<N-1} (2^j * 3^j)

plus the terminal DESTROY mass `4 * 2^(N-1) * 3^(N-1)` at the first-BIG1
boundary.  Thus the binary, ternary, and mixed worlds are all present in the
same equality. -/
theorem gst_information_eq_bigN_exact_joined_equationS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hbig : GSTInformationEqualsBigNS d N) :
    gstBig1ProjectedPathCodeS a d N =
      gstHandwrittenThreeWorldJoinedPrefixS (N-1) +
        4 * (gstBinaryWorldFactorS (N-1) *
          gstTernaryWorldFactorS (N-1)) := by
  rw [gst_information_eq_bigN_exact_three_world_codeS
    a d hpath h0 N hN hbig]
  rw [gst_handwritten_three_world_joined_prefix_closedS]
  unfold gstBinaryWorldFactorS gstTernaryWorldFactorS
  rw [← gst_three_world_factor_rawS (N-1)]
  have hp : 0 < 6^(N-1) := Nat.pow_pos (by decide)
  omega

/-- Fully expanded form of the handwritten three-world equation at BIG-N. -/
theorem gst_information_eq_bigN_exact_sum_equationS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hbig : GSTInformationEqualsBigNS d N) :
    gstBig1ProjectedPathCodeS a d N =
      5 * Finset.sum (Finset.range (N-1)) (fun j => 2^j * 3^j) +
        4 * (2^(N-1) * 3^(N-1)) := by
  simpa [gstHandwrittenThreeWorldJoinedPrefixS,
    gstBinaryWorldFactorS, gstTernaryWorldFactorS] using
    gst_information_eq_bigN_exact_joined_equationS
      a d hpath h0 N hN hbig

/-- The canonical horizontal parent segment itself closes the same three-world
exponential triangle: its binary length is `2*3^s`, and multiplying by the
aligned ternary factor gives the mixed six-state factor. -/
theorem gpt56_parent_segment_three_world_factorS (s : Nat) :
    4^(3^s) * 3^(2 * 3^s) = 6^(2 * 3^s) := by
  rw [gpt56_parent_multiplier_is_binary_bridge]
  exact (gst_three_world_factor_rawS (2 * 3^s)).symm

/-- `I = BIG-N` is now compared directly with the complete binary length of
the canonical parent multiplier.  Either BIG-N occurs inside that physical
segment, or the segment ends before BIG-N and its endpoint information is
forced to remain BIG2. -/
theorem gpt56_information_bigN_vs_parent_segmentS
    (s T q N : Nat)
    (hd2 : gstDigit T q = 2)
    (hbig : GSTInformationEqualsBigNS
      (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N) :
    N ≤ 2 * 3^s ∨
      (2 * 3^s < N ∧ gstDigitS (4^(3^s) * T) q = 2) := by
  by_cases hinside : N ≤ 2 * 3^s
  · exact Or.inl hinside
  · right
    have hafter : 2 * 3^s < N := by omega
    have hno : ∀ r, r ≤ 2 * 3^s →
        GSTPhysicalKernel.binaryColumnDigit T q r ≠ 1 := by
      intro r hr
      change GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N at hbig
      exact hbig.2 r (by omega)
    exact ⟨hafter,
      gpt56_no_big1_before_parent_endpoint_digit_two s T q hd2 hno⟩

/-- Live prefix-one package with literal `I = BIG-N` and its exact three-world
code attached to the real child Navigation gate. -/
theorem gpt56_prefix_one_live_information_bigN_three_world
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
          5 * (gstBinaryWorldFactorS (N-1) *
            gstTernaryWorldFactorS (N-1)) - 1 ∧
      GSTSeededAffineBadTrace 1 X := by
  dsimp only
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let X := c s / 3 + A*T
  obtain ⟨q, N, hd2, hC, hN, hfirst, hseeded⟩ :=
    gpt56_prefix_one_live_handwritten_package s n hs hn hchild hBad
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_binary_row_path T q
  have hd0eq : d 0 = 2 := by
    dsimp [d]
    simpa [GSTPhysicalKernel.binaryColumnDigit, gstDigit] using hd2
  have hd0 : d 0 ≠ 0 := by omega
  have hcode :
      gstBig1ProjectedPathCodeS a d N =
        5 * (gstBinaryWorldFactorS (N-1) *
          gstTernaryWorldFactorS (N-1)) - 1 := by
    apply gst_information_eq_bigN_exact_three_world_codeS
      a d hpath hd0 N hN
    exact hfirst
  exact ⟨q, N, hd2, hC, hN, hfirst,
    by simpa [a, d] using hcode,
    by simpa [T, A, X] using hseeded⟩

/-- Live equation package: the actual child Navigation witness now carries the
fully expanded three-world BIG-N equality used by the handwritten operator. -/
theorem gpt56_prefix_one_live_information_bigN_sum_equation
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
      GSTSeededAffineBadTrace 1 X := by
  dsimp only
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let X := c s / 3 + A*T
  obtain ⟨q, N, hd2, hC, hN, hbig, _hcode, hseeded⟩ :=
    gpt56_prefix_one_live_information_bigN_three_world s n hs hn hchild hBad
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_binary_row_path T q
  have hd0eq : d 0 = 2 := by
    dsimp [d]
    simpa [GSTPhysicalKernel.binaryColumnDigit, gstDigit] using hd2
  have hd0 : d 0 ≠ 0 := by omega
  have heq := gst_information_eq_bigN_exact_sum_equationS
    a d hpath hd0 N hN (by simpa [d] using hbig)
  exact ⟨q, N, hd2, hC, hN, hbig,
    by simpa [a, d] using heq,
    by simpa [T, A, X] using hseeded⟩

/-- Same live package, but with the BIG-N/parent-segment collision split already
performed.  This is the exact branch object consumed by the next surgery. -/
theorem gpt56_prefix_one_live_bigN_parent_segment_split
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let T := gstNavigationConstant (s+1) n
    let A := 4^(3^s)
    let X := c s / 3 + A*T
    ∃ q N,
      gstDigit T q = 2 ∧
      (gstCarry T q = 0 ∨ gstCarry T q = 3) ∧
      GSTInformationEqualsBigNS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N ∧
      (N ≤ 2 * 3^s ∨
        (2 * 3^s < N ∧ gstDigitS (A*T) q = 2)) ∧
      GSTSeededAffineBadTrace 1 X := by
  dsimp only
  let T := gstNavigationConstant (s+1) n
  let A := 4^(3^s)
  let X := c s / 3 + A*T
  obtain ⟨q, N, hd2, hC, _hN, hbig, _hcode, hseeded⟩ :=
    gpt56_prefix_one_live_information_bigN_three_world s n hs hn hchild hBad
  have hsplit := gpt56_information_bigN_vs_parent_segmentS s T q N hd2 hbig
  exact ⟨q, N, hd2, hC, hbig,
    by simpa [A] using hsplit,
    by simpa [T, A, X] using hseeded⟩

#check GSTInformationEqualsBigNS
#check gst_three_world_factor_rawS
#check gst_three_world_mixed_factor_exactS
#check gst_handwritten_three_world_joined_prefix_closedS
#check gst_information_eq_bigN_exact_three_world_codeS
#check gst_information_eq_bigN_exact_joined_equationS
#check gst_information_eq_bigN_exact_sum_equationS
#check gpt56_parent_segment_three_world_factorS
#check gpt56_information_bigN_vs_parent_segmentS
#check gpt56_prefix_one_live_information_bigN_three_world
#check gpt56_prefix_one_live_information_bigN_sum_equation
#check gpt56_prefix_one_live_bigN_parent_segment_split
#print axioms gst_three_world_factor_rawS
#print axioms gst_handwritten_three_world_joined_prefix_closedS
#print axioms gst_information_eq_bigN_exact_three_world_codeS
#print axioms gst_information_eq_bigN_exact_joined_equationS
#print axioms gst_information_eq_bigN_exact_sum_equationS
#print axioms gpt56_parent_segment_three_world_factorS
#print axioms gpt56_information_bigN_vs_parent_segmentS
#print axioms gpt56_prefix_one_live_information_bigN_three_world
#print axioms gpt56_prefix_one_live_information_bigN_sum_equation
#print axioms gpt56_prefix_one_live_bigN_parent_segment_split
