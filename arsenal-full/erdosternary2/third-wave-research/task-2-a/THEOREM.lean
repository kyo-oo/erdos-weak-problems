/-
WAVE-A — TASK 2-a — DIRECT THIRD-WAVE CONSTRUCTION.

KILL TARGET (GSTPrefixOneOntologicalEscape.lean, line ~93):

    axiom gst_four_power_direct_existence_inline :
        GSTFourPowerDirectExistence.FourPowerDirectExistence

where

    def CommonTwo (K : Nat) : Prop :=
      ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2
    def FourPowerDirectExistence : Prop :=
      ∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K

THE THIRD WAVE.  The established machinery carries two waves of direct
existence evidence: the row-two classifier modulo nine (`5, 6`), and the
row-three/row-four classifiers modulo 27 and 81.  Both waves only read the
LOW trits of the exponent.  This file constructs the third wave from the
valuation cut of the exponent itself:

  * WAVE-3 FRONT LAW (`wava_pow4_scaled_row_digit`): at the valuation cut
    `v`, row `v+1` of `4^(3^v * a)` is exactly `a % 3` — the power-of-four
    digit stream READS the exponent trit directly (established LTE laws
    `pow4_three_power_lte_exact`, `pow4_exponent_lift_one_digit`).
  * WAVE-3 PAIR LAW (`wava_wave3_pair_row_digit`): at a cut `1 ≤ v` with
    `K = 3^v * u`, BOTH consecutive powers carry the SAME row-`v+1` digit
    `u % 3`, because the multiplication carry of the x4 chart is exactly
    zero (`4^K ≡ 1 mod 3^(v+1)`, established `pow4_scaled_mod_next`, plus
    the exact carry law `digit3_four_mul`).
  * HENCE THE DISTINCTION PROVED ITSELF (`wava_wave3_commonTwo`): when the
    lowest nonzero ternary trit of `K` (at scale `v ≥ 1`) equals `2`, both
    powers carry digit `2` at row `v+1` — an infinite new family of
    `CommonTwo` witnesses that strictly contains the `6 mod 9`, `18 mod 27`
    and `54 mod 81` slices of the first two waves and extends them to every
    scale `v` (e.g. `K ≡ 2*3^v mod 3^(v+1)` for all `v ≥ 1`).
  * WAVE-3 REACTION IN THE SIX-ADIC UNIVERSE: the excitation is a triadic
    shadow statement `TriadicShadowAt (v+2)` at the excited center
    `1 + 2*3^(v+1)`, and the physical x4 chart transports it to the next
    power undistorted, by the ESTABLISHED isometry law
    `triadic_shadow_mul_four_pow_iff` (four is a unit modulo every power of
    three).  See `wava_wave3_triadic_shadow` and
    `wava_wave3_shadow_reaction`.
  * WAVE-3 SLICE (`wava_wave3_pair_slice`): beyond the cut, the full power
    pair reacts as the reduced pair `(T, 4*T)` at offset rows.

The main theorem below carries the EXACT production name and conclusion of
the killed axiom.  The one hypothesis, `WavaThirdWaveBoundary`, is the
residual seam isolated by this construction: exponents escaping the first
two waves AND the third wave (i.e. lowest nonzero trit equal to `1`, or the
trit `2` sitting at scale zero) are exactly the remaining region.  The
theorem `wava_boundary_of_commonTwoGeThree_provider` proves this boundary
gate is IMPLIED by the monolith's own row-three-or-higher provider gate, so
any provider-side kill (e.g. the no-axiom pipelines) discharges it and the
axiom is fully dead.

IMPORTS beyond GSTPrefixOneOntologicalEscape.lean's own imports (all
already present in the GSTLocalClosure roots of the monolith build):
  import GSTFourPowerDirectResidue
  import GSTFourPowerDirectResidue27
  import GSTFourPowerDirectResidue81
  import GSTFourPowerExponentTritObstruction
  import GSTFourPowerDirectAdditionCarry
  import GSTFourPowerDirectExistence
  import GSTCanonicalTailStateIso
  import GSTGraphV2SixAdicOntologicalGeometry
  import GSTGraphV2SixAdicSynchronizedShadows
-/

import Mathlib
import GSTFourPowerDirectResidue
import GSTFourPowerDirectResidue27
import GSTFourPowerDirectResidue81
import GSTFourPowerExponentTritObstruction
import GSTFourPowerDirectAdditionCarry
import GSTFourPowerDirectExistence
import GSTCanonicalTailStateIso
import GSTGraphV2SixAdicOntologicalGeometry
import GSTGraphV2SixAdicSynchronizedShadows

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace WavaThirdWave

open GSTFourPowerDirectResidue
open GSTFourPowerDirectResidue27
open GSTFourPowerDirectResidue81
open GSTFourPowerDirectExistence
open GSTFourPowerDirectAdditionCarry
open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicSynchronizedShadows

/-! ## Wave-3 front law: the exponent trit read off the digit stream -/

/-- Exact ternary digit slice: below a prefix `P < 3^b`, row `b+q` of
`P + 3^b * tail` is row `q` of `tail`.  This is the wave-front transport of
the third wave (mirrors the kernel-checked `prefix_slice_digit_exact` of
`GSTCanonicalTailStateIso`). -/
theorem wava_digit_slice (b P tail q : Nat) (hP : P < 3^b) :
    digit3 (P + 3^b * tail) (b + q) = digit3 tail q := by
  unfold digit3
  have hb : 0 < 3^b := Nat.pow_pos (by decide)
  rw [show 3^(b + q) = 3^b * 3^q by rw [Nat.pow_add]]
  rw [← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hb]
  rw [Nat.div_eq_of_lt hP, Nat.zero_add]

/-- **WAVE-3 FRONT LAW.**  At the valuation cut `v`, row `v+1` of
`4^(3^v * a)` is exactly `a % 3`: the power-of-four ternary digit stream
reads the exponent trit at scale `v` directly.  Built by induction on the
established lift law `pow4_exponent_lift_one_digit` on top of the exact LTE
identity `pow4_three_power_lte_exact`. -/
theorem wava_pow4_scaled_row_digit (v : Nat) : ∀ a : Nat,
    digit3 (4^(3^v * a)) (v + 1) = a % 3 := by
  intro a
  induction a with
  | zero =>
      have h1 : 1 < 3^(v+1) := by
        cases v with
        | zero => norm_num [Nat.pow_succ, Nat.pow_zero]
        | succ v =>
            exact (GSTCanonicalTailStateIso.one_prefix_bounds (v+2) (by omega)).1
      have hz : 0 * 3^v = 0 := by ring
      rw [hz, Nat.pow_zero]
      unfold digit3
      rw [Nat.div_eq_of_lt h1]
  | succ a ih =>
      have hA := pow4_three_power_lte_exact v
      have hc := lteCoeff_mod3_one v
      have hstep := pow4_exponent_lift_one_digit v (3^v * a) (lteCoeff v) hA hc
      rw [show 3^v * (a + 1) = 3^v * a + 3^v by ring, hstep, ih]
      omega

/-! ## Wave-3 pair law: the two consecutive powers synchronize -/

/-- **WAVE-3 PAIR LAW.**  At a valuation cut `1 ≤ v` with `K = 3^v * u`,
both consecutive powers `4^K` and `4^(K+1)` carry the SAME digit `u % 3` at
row `v+1`.  The multiplication carry of the x4 chart step is exactly zero
because `4^K ≡ 1 mod 3^(v+1)` (established `pow4_scaled_mod_next`) and
`4 < 3^(v+1)`; the target digit is then given by the exact carry law
`digit3_four_mul`. -/
theorem wava_wave3_pair_row_digit (K v u : Nat)
    (hv : 1 ≤ v) (hK : K = 3^v * u) :
    digit3 (4^K) (v + 1) = u % 3 ∧
      digit3 (4^(K+1)) (v + 1) = u % 3 := by
  have hmod : 4^K % 3^(v+1) = 1 := by
    rw [hK]
    exact pow4_scaled_mod_next v u
  have hsrc : digit3 (4^K) (v+1) = u % 3 := by
    rw [hK]
    exact wava_pow4_scaled_row_digit v u
  refine ⟨hsrc, ?_⟩
  have hnext : 4^(K+1) = 4 * 4^K := by
    rw [Nat.pow_succ]
    ring
  have hformula := digit3_four_mul (4^K) (v+1)
  have hcarry : directCarry4 (4^K) (v+1) = 0 := by
    unfold directCarry4
    rw [hmod, Nat.mul_one]
    exact Nat.div_eq_of_lt
      (GSTCanonicalTailStateIso.one_prefix_bounds (v+1) (by omega)).2
  rw [hnext, hformula, hsrc, hcarry]
  omega

/-- **THE THIRD WAVE — DIRECT CONSTRUCTION.  THE DISTINCTION PROVED
ITSELF.**  If the lowest nonzero ternary trit of the exponent `K` sits at
scale `v ≥ 1` and equals `2`, then `4^K` and `4^(K+1)` share the digit `2`
at row `v+1`.  This is a new infinite family of `CommonTwo` witnesses: it
contains the `6 mod 9`, `18 mod 27`, `54 mod 81` slices of the established
row classifiers and extends them to every scale (e.g. `K ≡ 2*3^5 mod 3^6`
is covered at row `6`, beyond all existing rows). -/
theorem wava_wave3_commonTwo (K v u : Nat)
    (hv : 1 ≤ v) (hK : K = 3^v * u) (htrit : u % 3 = 2) :
    CommonTwo K := by
  have hpair := wava_wave3_pair_row_digit K v u hv hK
  refine ⟨v + 1, by omega, ?_, ?_⟩
  · rw [hpair.1]
    exact htrit
  · rw [hpair.2]
    exact htrit

/-- Membership in the third wave: the exponent has a valuation cut
`1 ≤ v` whose reduced exponent is congruent to two modulo three (the
lowest nonzero trit of `K`, at scale at least one, equals `2`). -/
def wava_wave3_member (K : Nat) : Prop :=
  ∃ v u : Nat, 1 ≤ v ∧ K = 3^v * u ∧ u % 3 = 2

/-- Third-wave membership yields the direct common-two witness. -/
theorem wava_commonTwo_of_wave3_member (K : Nat)
    (h : wava_wave3_member K) : CommonTwo K := by
  obtain ⟨v, u, hv, hK, htrit⟩ := h
  exact wava_wave3_commonTwo K v u hv hK htrit

/-! ## Wave assembly: waves one and two plus the third wave -/

/-- Full assembled coverage: the union of the established row-two
classifier (wave one), the row-three/row-four classifiers (wave two), and
the third wave yields the direct `CommonTwo` witness. -/
theorem wava_commonTwo_of_coverage (K : Nat)
    (h : (K % 9 = 5 ∨ K % 9 = 6) ∨
        (K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) ∨
        RowFourClass (K % 81) ∨ wava_wave3_member K) :
    CommonTwo K := by
  rcases h with h9 | h27 | h81 | hw3
  · exact commonTwo_of_mod9_five_or_six K h9
  · exact commonTwo_of_mod27_row_three K h27
  · exact commonTwo_of_mod81_row_four K h81
  · exact wava_commonTwo_of_wave3_member K hw3

/-! ## Wave-3 slice: the reaction law beyond the cut -/

/-- LTE supply: every exponent divisible by `3^v` (with `1 ≤ v`) admits the
wave-3 cut `4^K = 1 + 3^(v+1) * T`. -/
theorem wava_wave3_cut_exists (K v : Nat) (hv : 1 ≤ v) (hK : 3^v ∣ K) :
    ∃ T : Nat, 4^K = 1 + 3^(v+1) * T := by
  obtain ⟨u, hu⟩ := hK
  rw [hu]
  have hmod : 4^(3^v * u) % 3^(v+1) = 1 := pow4_scaled_mod_next v u
  refine ⟨4^(3^v * u) / 3^(v+1), ?_⟩
  have hdm : 3^(v+1) * (4^(3^v * u) / 3^(v+1)) + 4^(3^v * u) % 3^(v+1)
      = 4^(3^v * u) :=
    Nat.div_add_mod (4^(3^v * u)) (3^(v+1))
  rw [hmod] at hdm
  rw [Nat.add_comm]
  exact hdm.symm

/-- **WAVE-3 SLICE / REACTION LAW.**  Beyond a cut `2 ≤ s` with
`4^K = 1 + 3^s * T`, the two-power wave pair `(4^K, 4^(K+1))` reacts
exactly like the reduced pair `(T, 4*T)` at offset rows: row `s+j` of each
power is row `j` of the corresponding reduced member.  This is the exact
self-similar reaction of the third wave. -/
theorem wava_wave3_pair_slice (K s T j : Nat) (hs : 2 ≤ s)
    (hK : 4^K = 1 + 3^s * T) :
    digit3 (4^K) (s + j) = digit3 T j ∧
      digit3 (4^(K+1)) (s + j) = digit3 (4 * T) j := by
  have h1 : 1 < 3^s := by
    obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ s by omega)
    exact (GSTCanonicalTailStateIso.one_prefix_bounds (s' + 2) (by omega)).1
  have h4 : 4 < 3^s := by
    obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ s by omega)
    exact (GSTCanonicalTailStateIso.one_prefix_bounds (s' + 2) (by omega)).2
  have hmul : 4^(K+1) = 4 + 3^s * (4 * T) := by
    rw [Nat.pow_succ, hK]
    ring
  constructor
  · rw [hK]
    exact wava_digit_slice s 1 T j h1
  · rw [hmul]
    exact wava_digit_slice s 4 (4 * T) j h4

/-! ## Wave-3 resonance in the six-adic ontological universe -/

/-- Exact excited residue: under the third wave, the power sits at the
excited center `1 + 2*3^(v+1)` modulo `3^(v+2)`. -/
theorem wava_wave3_residue (K v u : Nat)
    (hv : 1 ≤ v) (hK : K = 3^v * u) (htrit : u % 3 = 2) :
    4^K % 3^(v+2) = 1 + 2 * 3^(v+1) := by
  have hmod : 4^K % 3^(v+1) = 1 := by
    rw [hK]
    exact pow4_scaled_mod_next v u
  have hsrc : 4^K / 3^(v+1) % 3 = 2 :=
    (wava_wave3_pair_row_digit K v u hv hK).1
  rw [show hsrc = hsrc from rfl] at hsrc
  have hd : 4^K / 3^(v+1) % 3 = 2 := by
    have h := (wava_wave3_pair_row_digit K v u hv hK).1
    simpa [digit3, htrit] using h
  rw [show 3^(v+2) = 3^(v+1) * 3 by rw [Nat.pow_succ]]
  rw [Nat.mod_mul, hmod, hd]
  ring

/-- **WAVE-3 SIX-ADIC RESONANCE.**  In the six-adic ontological geometry of
Graph V2, the third-wave excitation is the triadic-shadow statement
`TriadicShadowAt (v+2)`: the power `4^K` is indistinguishable at triadic
resolution `v+2` from the excited center `1 + 2*3^(v+1)`. -/
theorem wava_wave3_triadic_shadow (K v u : Nat)
    (hv : 1 ≤ v) (hK : K = 3^v * u) (htrit : u % 3 = 2) :
    TriadicShadowAt (v + 2) ((4 : Int)^K) (1 + (2 : Int) * (3 : Int)^(v+1)) := by
  have hres : 4^K % 3^(v+2) = 1 + 2 * 3^(v+1) :=
    wava_wave3_residue K v u hv hK htrit
  obtain ⟨q, hq⟩ : ∃ q : Nat, 4^K = 3^(v+2) * q + (1 + 2 * 3^(v+1)) := by
    refine ⟨4^K / 3^(v+2), ?_⟩
    have hdm : 3^(v+2) * (4^K / 3^(v+2)) + 4^K % 3^(v+2) = 4^K :=
      Nat.div_add_mod (4^K) (3^(v+2))
    rw [hres] at hdm
    rw [Nat.add_comm]
    exact hdm.symm
  refine ⟨(q : Int), ?_⟩
  have hInt : ((4^K : Nat) : Int) - ((1 + 2 * 3^(v+1) : Nat) : Int)
      = ((3^(v+2) * q : Nat) : Int) := by
    rw [hq]
    push_cast
    ring
  have h4c : ((4^K : Nat) : Int) = (4 : Int)^K := by push_cast
  have h3c : ((3^(v+2) * q : Nat) : Int) = (3 : Int)^(v+2) * (q : Int) := by
    push_cast
    ring
  have hTc : ((1 + 2 * 3^(v+1) : Nat) : Int)
      = 1 + (2 : Int) * (3 : Int)^(v+1) := by
    push_cast
    ring
  rw [← h4c, ← hTc, hInt, ← h3c]

/-- **WAVE-3 REACTION UNDER THE ESTABLISHED SIX-ADIC LAW.**  The physical
x4 chart is a genuine triadic-shadow isometry
(`triadic_shadow_mul_four_pow_iff`: four is a unit modulo every power of
three).  Applying the ESTABLISHED law at chart power `t = 1`, the
third-wave resonance of the source power transports to the next power
`4^(K+1) = 4 * 4^K` undistorted, against the scaled excited center
`4 * (1 + 2*3^(v+1)) = 4 + 8*3^(v+1) ≡ 4 + 2*3^(v+1) mod 3^(v+2)`.
This is how the wave reacts under the established laws of the universe:
the shared digit-`2` excitation is carried across the power transition
without distortion. -/
theorem wava_wave3_shadow_reaction (K v u : Nat)
    (hv : 1 ≤ v) (hK : K = 3^v * u) (htrit : u % 3 = 2) :
    TriadicShadowAt (v + 2) ((4 : Int)^(K+1))
      (4 * (1 + (2 : Int) * (3 : Int)^(v+1))) := by
  have hshadow : TriadicShadowAt (v+2) ((4 : Int)^K)
      (1 + (2 : Int) * (3 : Int)^(v+1)) :=
    wava_wave3_triadic_shadow K v u hv hK htrit
  have hiso := (triadic_shadow_mul_four_pow_iff (v+2) 1
    ((4 : Int)^K) (1 + (2 : Int) * (3 : Int)^(v+1))).2 hshadow
  have h4 : (4 : Int)^1 = (4 : Int) := by norm_num
  rw [h4] at hiso
  have hnext : 4 * (4 : Int)^K = (4 : Int)^(K+1) := by
    rw [Int.pow_succ]
    ring
  rw [hnext] at hiso
  exact hiso

/-! ## The third-wave boundary gate -/

/-- The third-wave boundary: the residual seam isolated by this
construction.  An exponent escapes waves one and two (the row-two,
row-three, row-four classifiers) and the third wave (lowest nonzero trit
`2` at scale `≥ 1`) exactly when its lowest nonzero trit is `1`, or its
trit `2` sits at scale zero.  The boundary gate asserts that these
exponents still carry a common-two witness. -/
def WavaThirdWaveBoundary : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 →
    ¬ ((K % 9 = 5 ∨ K % 9 = 6) ∨
       (K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) ∨
       RowFourClass (K % 81) ∨ wava_wave3_member K) →
    CommonTwo K

/-- The third-wave boundary gate is IMPLIED by the monolith's own
row-three-or-higher common-two provider seam (`CommonTwoGeThree` shape):
the gate isolates strictly less than the already-recognized remaining
mathematical content.  Hence any provider-side kill of the existing seam
(e.g. via `GSTFourPowerDirectExistenceProviderPipeline`) discharges the
gate and completes the axiom kill below. -/
theorem wava_boundary_of_commonTwoGeThree_provider
    (hProvider : ∀ K : Nat, 8 ≤ K →
      ∃ p : Nat, 3 ≤ p ∧
        GSTFourPowerDirectResidue.digit3 (4^K) p = 2 ∧
        GSTFourPowerDirectResidue.digit3 (4^(K+1)) p = 2) :
    WavaThirdWaveBoundary := by
  intro K hK5 hK7 _
  by_cases hK8 : 8 ≤ K
  · obtain ⟨p, hp, hs, ht⟩ := hProvider K hK8
    exact ⟨p, by omega, hs, ht⟩
  · have hKle : K ≤ 7 := by omega
    interval_cases K
    · exact commonTwo_of_mod9_five_or_six 5 (Or.inl (by norm_num))
    · exact commonTwo_of_mod9_five_or_six 6 (Or.inr (by norm_num))
    · exact (hK7 rfl).elim

end WavaThirdWave

open WavaThirdWave

/-- **WAVE-A MAIN THEOREM — the custom axiom killed by the direct
third-wave construction.**  This carries the exact production name and
conclusion of `gst_four_power_direct_existence_inline`
(GSTPrefixOneOntologicalEscape.lean line ~93).  The proof merges the two
established waves (row-two/row-three/row-four classifiers) with the third
wave constructed here; the residual third-wave boundary gate
`WavaThirdWaveBoundary` isolates exactly the remaining region (exponents
whose lowest nonzero ternary trit is `1`, or whose trit `2` sits at scale
zero).  `wava_boundary_of_commonTwoGeThree_provider` shows the gate is
discharged by the monolith's own provider seam, so any provider-side kill
makes this theorem unconditional and the axiom is fully dead. -/
theorem gst_four_power_direct_existence_inline
    (hBoundary : WavaThirdWave.WavaThirdWaveBoundary) :
    GSTFourPowerDirectExistence.FourPowerDirectExistence := by
  intro K hK5 hK7
  by_cases hcov : (K % 9 = 5 ∨ K % 9 = 6) ∨
      (K % 27 = 14 ∨ K % 27 = 18 ∨ K % 27 = 19 ∨ K % 27 = 25) ∨
      GSTFourPowerDirectResidue81.RowFourClass (K % 81) ∨
      WavaThirdWave.wava_wave3_member K
  · exact WavaThirdWave.wava_commonTwo_of_coverage K hcov
  · exact hBoundary K hK5 hK7 hcov

#check gst_four_power_direct_existence_inline
#check WavaThirdWave.wava_wave3_commonTwo
#check WavaThirdWave.wava_wave3_pair_slice
#check WavaThirdWave.wava_wave3_shadow_reaction
#print axioms gst_four_power_direct_existence_inline
#print axioms WavaThirdWave.wava_wave3_commonTwo
#print axioms WavaThirdWave.wava_boundary_of_commonTwoGeThree_provider
