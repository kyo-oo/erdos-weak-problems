/- ======================================================================
/- CHRONOLOGICAL LABEL -- #1032 / 1132
/-    Path         : branches/sol_global-flux-surgery/HandwrittenBig1PathProjectorScratch.lean
/-    Ref          : origin/sol/global-flux-surgery
/-    First-commit : 2026-08-17 12:39:11 +0530  (163d621)
/-    Last-commit  : 2026-08-17 12:46:18 +0530  (33e93dd)
/-    Total commits: 3
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/3] 2026-08-17 12:39:11 +0530  163d621  (ker07-dev)
/-        Add pathwise BIG1 projector chord experiment
/- [02/3] 2026-08-17 12:44:36 +0530  8b1b808  (ker07-dev)
/-        Strengthen BIG1 projector with exact two-layer GST+ gate
/- [03/3] 2026-08-17 12:46:18 +0530  33e93dd  (ker07-dev)
/-        Add exact 36-state chord identity for projected two-digit sector
/- ====================================================================== -/

import HandwrittenBigNOmegaScratch
import HandwrittenSixUniverseScratch
import PhysicalSixBridgeGateScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Pathwise BIG1 projector for Boss's handwritten operator

This scratch promotes the handwritten condition `I ≠ BIG1` from a single
annotation to a condition imposed at every microscopic x2/base3 bridge layer.

For one physical bridge

    a + 2*d = e + 3*a'

with a<2 and d<3, if both endpoint information digits are BIG1-clear and the
incoming information is nonzero, then the only legal cell is

    a=1, d=2, e=2,

so its six-state mass is 5 and its event symbol is 8 (SURVIVE).

Iterating this gives a path theorem: a nonzero path whose every information
vertex is BIG1-clear is forced to be the all-BIG2 path, and every microscopic
six-state coordinate on the path is 5.

At exactly two x2 layers -- one physical x4 GST cell -- the same projector
selects C=3,d=2 and microscopic pair (5,5).  Its base-six word is 55_6=35,
which is simultaneously the maximal nonzero mass of the 36-state aligned V2
cell and the coefficient 36-1 in the general world-projection identity.
-/

/-- One bridge: BIG1-clear on both endpoints plus nonzero input forces the
unique SURVIVE cell. -/
theorem gst_big1_clear_nonzero_bridge_forces_surviveS
    (a d : Nat) (ha : a < 2) (hd : d < 3)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hout1 : gstBinaryBridgeOutputS a d ≠ 1) :
    a = 1 ∧ d = 2 ∧ gstBinaryBridgeOutputS a d = 2 ∧
      gstBinaryBridgeMassS a d = 5 ∧ gstBinaryBridgeEventS a d = 8 := by
  have hac : a = 0 ∨ a = 1 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hac with h0 | h1 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst a <;> subst d <;>
    simp [gstBinaryBridgeOutputS, gstBinaryBridgeMassS,
      gstBinaryBridgeEventS] at hd0 hd1 hout1 ⊢

/-- Pathwise form of Boss's `I ≠ BIG1` condition.  `d j` is the information
vertex at depth j and `a j` is the incoming binary bridge bit on edge j. -/
def GSTBig1ClearBridgePathS
    (a d : Nat → Nat) (K : Nat) : Prop :=
  (∀ j, j < K → a j < 2) ∧
  (∀ j, j ≤ K → d j < 3) ∧
  (∀ j, j ≤ K → d j ≠ 1) ∧
  (∀ j, j < K → gstBinaryBridgeOutputS (a j) (d j) = d (j+1))

/-- The handwritten pathwise projector is rigid: once its aligned input is
nonzero, every information vertex is BIG2. -/
theorem gst_big1_clear_path_nonzero_forces_all_big2S
    (a d : Nat → Nat) (K : Nat)
    (hpath : GSTBig1ClearBridgePathS a d K)
    (h0 : d 0 ≠ 0) :
    ∀ j, j ≤ K → d j = 2 := by
  intro j hj
  induction j with
  | zero =>
      have hdlt := hpath.2.1 0 (by omega)
      have hd1 := hpath.2.2.1 0 (by omega)
      omega
  | succ j ih =>
      have hjK : j < K := by omega
      have hdj : d j = 2 := ih (by omega)
      have ha := hpath.1 j hjK
      have hdlt := hpath.2.1 j (by omega)
      have hd1 := hpath.2.2.1 j (by omega)
      have htrans := hpath.2.2.2 j hjK
      have hout1 : gstBinaryBridgeOutputS (a j) (d j) ≠ 1 := by
        rw [htrans]
        exact hpath.2.2.1 (j+1) (by omega)
      have hsurv := gst_big1_clear_nonzero_bridge_forces_surviveS
        (a j) (d j) ha hdlt (by omega) hd1 hout1
      exact htrans.symm.trans hsurv.2.2.1

/-- Every edge of a nonzero pathwise-BIG1-clear component is the microscopic
SURVIVE state: binary bit 1, information digit 2, mass 5, event 8. -/
theorem gst_big1_clear_path_edges_are_surviveS
    (a d : Nat → Nat) (K : Nat)
    (hpath : GSTBig1ClearBridgePathS a d K)
    (h0 : d 0 ≠ 0) :
    ∀ j, j < K →
      a j = 1 ∧ d j = 2 ∧ gstBinaryBridgeOutputS (a j) (d j) = 2 ∧
        gstBinaryBridgeMassS (a j) (d j) = 5 ∧
        gstBinaryBridgeEventS (a j) (d j) = 8 := by
  intro j hj
  have hdj := gst_big1_clear_path_nonzero_forces_all_big2S
    a d K hpath h0 j (by omega)
  have ha := hpath.1 j hj
  have hdlt := hpath.2.1 j (by omega)
  have hd1 := hpath.2.2.1 j (by omega)
  have htrans := hpath.2.2.2 j hj
  have hout1 : gstBinaryBridgeOutputS (a j) (d j) ≠ 1 := by
    rw [htrans]
    exact hpath.2.2.1 (j+1) (by omega)
  exact gst_big1_clear_nonzero_bridge_forces_surviveS
    (a j) (d j) ha hdlt (by omega) hd1 hout1

/-- Base-six code of the K microscopic bridge states. -/
def gstBig1ProjectedPathCodeS
    (a d : Nat → Nat) (K : Nat) : Nat :=
  ∑ j in Finset.range K, gstBinaryBridgeMassS (a j) (d j) * 6^j

/-- A nonzero pathwise-BIG1-clear component is exactly 55...55 in base six,
therefore its code is 6^K-1. -/
theorem gst_big1_projected_path_code_eq_six_pow_sub_oneS
    (a d : Nat → Nat) (K : Nat)
    (hpath : GSTBig1ClearBridgePathS a d K)
    (h0 : d 0 ≠ 0) :
    gstBig1ProjectedPathCodeS a d K = 6^K - 1 := by
  induction K with
  | zero => simp [gstBig1ProjectedPathCodeS]
  | succ K ih =>
      have hprefix : GSTBig1ClearBridgePathS a d K := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j hj
          exact hpath.1 j (by omega)
        · intro j hj
          exact hpath.2.1 j (by omega)
        · intro j hj
          exact hpath.2.2.1 j (by omega)
        · intro j hj
          exact hpath.2.2.2 j (by omega)
      have ih' := ih hprefix h0
      have hedge := gst_big1_clear_path_edges_are_surviveS
        a d (K+1) hpath h0 K (by omega)
      unfold gstBig1ProjectedPathCodeS at ih' ⊢
      rw [Finset.sum_range_succ, ih', hedge.2.2.2.1]
      have hp : 0 < 6^K := Nat.pow_pos (by decide)
      rw [Nat.pow_succ]
      omega

/-! ## Exact two-layer / two-digit physical collapse -/

/-- Output information digit after the second x2 bridge of one x4 cell. -/
def gstSecondMicroOutputS (C d : Nat) : Nat :=
  gstSecondMicroMassS C d % 3

/-- The three canonical BIG2 orientations expose three different information
paths.  Hidden CREATE->DESTROY and NULL DESTROY->CREATE both pass through
BIG1; GST+ SURVIVE->SURVIVE is BIG1-clear at all three vertices. -/
theorem gst_two_layer_big2_information_path_tableS :
    gstFirstMicroOutputS 0 1 = 2 ∧ gstSecondMicroOutputS 0 1 = 1 ∧
    gstFirstMicroOutputS 0 2 = 1 ∧ gstSecondMicroOutputS 0 2 = 2 ∧
    gstFirstMicroOutputS 3 2 = 2 ∧ gstSecondMicroOutputS 3 2 = 2 := by
  decide

/-- Pathwise `I ≠ BIG1`, together with nonzero aligned input, completely
solves the physical two-layer sector: the only legal x4 cell is GST+ with
input 2, intermediate 2, output 2 and microscopic masses (5,5). -/
theorem gst_big1_projector_two_layer_forces_plus_surviveS
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hmid1 : gstFirstMicroOutputS C d ≠ 1)
    (hout1 : gstSecondMicroOutputS C d ≠ 1) :
    C = 3 ∧ d = 2 ∧
      gstFirstMicroOutputS C d = 2 ∧
      gstSecondMicroOutputS C d = 2 ∧
      gstFirstMicroMassS C d = 5 ∧
      gstSecondMicroMassS C d = 5 := by
  have hd2 : d = 2 := by omega
  subst d
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    subst C <;>
    norm_num [gstFirstMicroOutputS, gstFirstMicroMassS,
      gstSecondMicroOutputS, gstSecondMicroMassS,
      gstMicroHighBitS, gstMicroLowBitS] at hmid1 hout1 ⊢

/-- Therefore the nonzero BIG1-projected two-digit sector is not merely
associated with a Happy Gate: it is exactly the physical GST+ Happy gate. -/
theorem gst_big1_projector_two_layer_is_physical_gst_plus_gateS
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hmid1 : gstFirstMicroOutputS C d ≠ 1)
    (hout1 : gstSecondMicroOutputS C d ≠ 1) :
    (d = 2 ∧ (C = 0 ∨ C = 3)) ∧
      (gstFirstMicroMassS C d = 5 ∧ gstSecondMicroMassS C d = 5) := by
  obtain ⟨hC3, hd2, _hm, _ho, hM1, hM2⟩ :=
    gst_big1_projector_two_layer_forces_plus_surviveS
      C d hC hd hd0 hd1 hmid1 hout1
  exact ⟨⟨hd2, Or.inr hC3⟩, hM1, hM2⟩

/-- The exact two-layer chord: the projected microscopic word is 55 in base 6,
so its state number is 35 = 6^2-1. -/
theorem gst_big1_projector_two_layer_chord_35S
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hmid1 : gstFirstMicroOutputS C d ≠ 1)
    (hout1 : gstSecondMicroOutputS C d ≠ 1) :
    gstFirstMicroMassS C d + 6 * gstSecondMicroMassS C d = 35 := by
  obtain ⟨_hC3, _hd2, _hm, _ho, hM1, hM2⟩ :=
    gst_big1_projector_two_layer_forces_plus_surviveS
      C d hC hd hd0 hd1 hmid1 hout1
  rw [hM1, hM2]

/-- The same integer 35 is the maximal aligned 36-state mixed-radix mass
(C,w)=(3,8), i.e. carry GST+ and ternary block 22. -/
theorem gst_aligned_36_max_mass_is_same_chord_35S :
    3 + 4*8 = 35 ∧ 8 = 2 + 3*2 ∧ 35 = 6^2 - 1 := by
  decide

/-- The world-projection coefficient at cardinality 6^K is the same integer
selected by the unique nonzero pathwise-BIG1-clear base-six word. -/
def gstWorldProjectionCoefficientS (K : Nat) : Nat := K - 1

theorem gst_big1_projected_path_equals_world_projection_coefficientS
    (a d : Nat → Nat) (K : Nat)
    (hpath : GSTBig1ClearBridgePathS a d K)
    (h0 : d 0 ≠ 0) :
    gstBig1ProjectedPathCodeS a d K =
      gstWorldProjectionCoefficientS (6^K) := by
  rw [gst_big1_projected_path_code_eq_six_pow_sub_oneS a d K hpath h0]
  rfl
