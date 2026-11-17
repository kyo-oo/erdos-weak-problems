import GSTGraphV2InfiniteControlScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Infinite BIG-N / I != BIG1 dichotomy

`N` below is not a finite horizon imposed on the graph.  The graph remains an
actual `Nat`-indexed infinite bridge path.  In the BIG-N branch, `N` is the
first coordinate at which the infinite information path itself hits BIG1.
The complementary branch is pathwise `I != BIG1` at every natural coordinate.
-/

structure GSTInfiniteBridgePathS (a d : Nat → Nat) : Prop where
  bit_lt_two : ∀ j, a j < 2
  digit_lt_three : ∀ j, d j < 3
  bridge_step : ∀ j, gstBinaryBridgeOutputS (a j) (d j) = d (j+1)

def GSTFirstBig1AtS (d : Nat → Nat) (N : Nat) : Prop :=
  d N = 1 ∧ ∀ j, j < N → d j ≠ 1

theorem gst_infinite_bridge_to_big1_clearS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (hno1 : ∀ j, d j ≠ 1) :
    GSTBig1ClearInfinitePathS a d := by
  exact ⟨hpath.bit_lt_two, hpath.digit_lt_three,
    hno1, hpath.bridge_step⟩

theorem gst_infinite_bigN_or_notBig1S
    (d : Nat → Nat) :
    (∃ N, d N = 1) ∨ (∀ j, d j ≠ 1) := by
  by_cases h : ∃ N, d N = 1
  · exact Or.inl h
  · right
    intro j hj
    exact h ⟨j, hj⟩

theorem gst_exists_first_big1S
    (d : Nat → Nat)
    (hex : ∃ N, d N = 1) :
    ∃ N, GSTFirstBig1AtS d N := by
  let N := Nat.find hex
  refine ⟨N, ?_⟩
  constructor
  · exact Nat.find_spec hex
  · intro j hj h1
    have hle : Nat.find hex ≤ j := Nat.find_min' hex h1
    change j < Nat.find hex at hj
    omega

theorem gst_before_first_big1_all_big2S
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hfirst : GSTFirstBig1AtS d N) :
    ∀ j, j < N → d j = 2 := by
  intro j hj
  induction j with
  | zero =>
      have hdlt := hpath.digit_lt_three 0
      have hd1 := hfirst.2 0 (by omega)
      omega
  | succ j ih =>
      have hjN : j < N := by omega
      have hdj : d j = 2 := ih hjN
      have ha := hpath.bit_lt_two j
      have hdlt := hpath.digit_lt_three j
      have hd1 := hfirst.2 j hjN
      have hout1 : gstBinaryBridgeOutputS (a j) (d j) ≠ 1 := by
        rw [hpath.bridge_step j]
        exact hfirst.2 (j+1) (by omega)
      have hs := gst_big1_clear_nonzero_bridge_forces_surviveS
        (a j) (d j) ha hdlt (by omega) hd1 hout1
      rw [← hpath.bridge_step j]
      exact hs.2.2.1

theorem gst_before_first_big1_edges_surviveS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hfirst : GSTFirstBig1AtS d N) :
    ∀ j, j+1 < N →
      a j = 1 ∧ d j = 2 ∧
      gstBinaryBridgeMassS (a j) (d j) = 5 ∧
      gstBinaryBridgeEventS (a j) (d j) = 8 := by
  intro j hj
  have hdj := gst_before_first_big1_all_big2S
    a d hpath h0 N hN hfirst j (by omega)
  have ha := hpath.bit_lt_two j
  have hdlt := hpath.digit_lt_three j
  have hd1 := hfirst.2 j (by omega)
  have hout1 : gstBinaryBridgeOutputS (a j) (d j) ≠ 1 := by
    rw [hpath.bridge_step j]
    exact hfirst.2 (j+1) hj
  have hs := gst_big1_clear_nonzero_bridge_forces_surviveS
    (a j) (d j) ha hdlt (by omega) hd1 hout1
  exact ⟨hs.1, hs.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

theorem gst_first_big1_boundary_is_destroyS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hfirst : GSTFirstBig1AtS d N) :
    let j := N-1
    a j = 0 ∧ d j = 2 ∧
      gstBinaryBridgeMassS (a j) (d j) = 4 ∧
      gstBinaryBridgeEventS (a j) (d j) = 5 := by
  dsimp only
  let j := N-1
  have hjN : j < N := by dsimp [j]; omega
  have hdj : d j = 2 :=
    gst_before_first_big1_all_big2S a d hpath h0 N hN hfirst j hjN
  have hstep := hpath.bridge_step j
  have hidx : j + 1 = N := by dsimp [j]; omega
  rw [hidx, hfirst.1, hdj] at hstep
  have haLt := hpath.bit_lt_two j
  have ha0 : a j = 0 := by
    have hac : a j = 0 ∨ a j = 1 := by omega
    rcases hac with h | h
    · exact h
    · rw [h] at hstep
      norm_num [gstBinaryBridgeOutputS] at hstep
  rw [ha0, hdj]
  norm_num [gstBinaryBridgeMassS, gstBinaryBridgeEventS,
    gstBinaryBridgeOutputS]

theorem gst_first_big1_survive_prefix_codeS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hfirst : GSTFirstBig1AtS d N) :
    gstBig1ProjectedPathCodeS a d (N-1) = 6^(N-1) - 1 := by
  have hprefix : ∀ K, K ≤ N - 1 →
      gstBig1ProjectedPathCodeS a d K = 6^K - 1 := by
    intro K
    induction K with
    | zero =>
        intro _
        simp [gstBig1ProjectedPathCodeS]
    | succ K ih =>
        intro hKN
        have hKedge : K + 1 < N := by omega
        have hedge := gst_before_first_big1_edges_surviveS
          a d hpath h0 N hN hfirst K hKedge
        have ih' := ih (by omega)
        unfold gstBig1ProjectedPathCodeS at ih' ⊢
        rw [Finset.sum_range_succ, ih', hedge.2.2.1]
        have hp : 0 < 6^K := Nat.pow_pos (by decide)
        rw [Nat.pow_succ]
        omega
  exact hprefix (N-1) (by omega)

theorem gst_first_big1_exact_bigN_codeS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hfirst : GSTFirstBig1AtS d N) :
    gstBig1ProjectedPathCodeS a d N = 5 * 6^(N-1) - 1 := by
  cases N with
  | zero => omega
  | succ N =>
      have hpre := gst_first_big1_survive_prefix_codeS
        a d hpath h0 (N+1) (by omega) hfirst
      have hbound := gst_first_big1_boundary_is_destroyS
        a d hpath h0 (N+1) (by omega) hfirst
      dsimp only at hbound
      simp only [Nat.add_sub_cancel] at hpre hbound ⊢
      unfold gstBig1ProjectedPathCodeS at hpre ⊢
      rw [Finset.sum_range_succ, hpre, hbound.2.2.1]
      have hp : 0 < 6^N := Nat.pow_pos (by decide)
      omega

theorem gst_infinite_two_case_controlS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0) :
    (∃ N, GSTFirstBig1AtS d N) ∨
      GSTBig1ClearInfinitePathS a d := by
  rcases gst_infinite_bigN_or_notBig1S d with hbig | hno
  · exact Or.inl (gst_exists_first_big1S d hbig)
  · exact Or.inr (gst_infinite_bridge_to_big1_clearS a d hpath hno)

theorem gst_infinite_two_case_quantitativeS
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0) :
    (∃ N, GSTFirstBig1AtS d N ∧
        (1 ≤ N → gstBig1ProjectedPathCodeS a d N =
          5 * 6^(N-1) - 1)) ∨
      (GSTBig1ClearInfinitePathS a d ∧
        ∀ K, gstBig1ProjectedPathCodeS a d K = 6^K - 1) := by
  rcases gst_infinite_two_case_controlS a d hpath h0 with hbig | hclear
  · left
    obtain ⟨N, hfirst⟩ := hbig
    refine ⟨N, hfirst, ?_⟩
    intro hN
    exact gst_first_big1_exact_bigN_codeS a d hpath h0 N hN hfirst
  · right
    exact ⟨hclear,
      gst_big1_clear_infinite_all_six_prefixes_maximalS a d hclear h0⟩

end GSTInfiniteV2
