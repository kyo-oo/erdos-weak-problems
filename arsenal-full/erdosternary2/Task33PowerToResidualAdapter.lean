import GSTFinalResidualConnector

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Task33PowerToResidualAdapter

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2Production
open GSTU2DEventTransport

/-- Exact reverse of the certified residual connector: if the absolute
right-edge perfect-power sheet has no physical Happy cell at any positive row,
then every residual Omega gate polynomial is nonzero.  This manufactures the
`GSTOmegaInfiniteBadTrace` input required by the clean residual collision
without adding it as a hypothesis. -/
theorem absolute_parent_bad_to_omega_bad
    (s k m : Nat) (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hNo : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell
        (graph 1 (residualParentExponent s k m) q).seven.carry
        (graph 1 (residualParentExponent s k m) q).seven.digit) :
    GSTOmegaInfiniteBadTrace s k m := by
  intro j
  change GSTOmegaGatePolynomial (gstOmega s k m j) ≠ 0
  intro hzero
  have hgate :=
    (gst_omega_gate_polynomial_zero_iff (gstOmega s k m j)).1 hzero
  rcases hgate with ⟨hdOmega, hcOmega⟩
  apply hNo
  refine ⟨s + k + 1 + j, by omega, ?_⟩

  have hb2 : 2 ≤ s + 1 := by omega
  have hpow : 3^2 ≤ 3^(s+1) :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hb2
  have hfour : 4 < 3^(s+1) := by
    norm_num at hpow ⊢
    omega
  have hone : 1 < 3^(s+1) := by omega

  have hE :
      4^(residualParentExponent s k m) * 1 =
        1 + 3^(s+1) * gstNavigationConstant s (1 + 3^k*m) := by
    simpa [residualParentExponent] using
      gst_navigation_decomposition s (1 + 3^k*m) hs

  have hproj := gst_omega_parent_projection s k m j hs
  have hdNav :
      gstDigit (gstNavigationConstant s (1 + 3^k*m)) (k+j) = 2 := by
    rw [hproj.1]
    exact hdOmega
  have hcNav :
      seededCarry 1 (gstNavigationConstant s (1 + 3^k*m)) (k+j) = 0 ∨
      seededCarry 1 (gstNavigationConstant s (1 + 3^k*m)) (k+j) = 3 := by
    rw [hproj.2]
    exact hcOmega

  have hiff := graph_prefix_slice_happy_iff
    1 (residualParentExponent s k m) (s+1) 1
    (gstNavigationConstant s (1 + 3^k*m)) (k+j) hE hone
  apply hiff.2
  have hseed : (4 * 1) / 3^(s+1) = 0 := Nat.div_eq_of_lt hfour
  simpa [digit3, gstDigit, seededCarry, gstCarry, hseed] using
    ⟨hdNav, hcNav⟩

#check absolute_parent_bad_to_omega_bad
#print axioms absolute_parent_bad_to_omega_bad

end Task33PowerToResidualAdapter
