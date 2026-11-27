import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# GST Graph V2 — standalone infinite-scale controller

This file kernelizes the handwritten V2/Omega/Pi/U layer independently of the
old scratch import graph.  The graph domain is `Nat`, so the object itself has
all natural information depths.  A finite prefix is only an observation of the
infinite object, never a replacement for it.

Two handwritten information regimes are represented explicitly below:

* `BIG-N`: an arbitrary natural Navigation information packet, controlled by
  an infinite Omega transfer stream plus all-scale Pi multiply/divide energy;
* `I != BIG1`: an infinite microscopic bridge path on which information value
  one is excluded at every depth.  A nonzero such path is rigidly forced to
  BIG2/SURVIVE at every depth.

No axiom, `proof-hole`, `admit`, terminal-NULL principle, or finite-search bound is
introduced here.
-/

/-! ## Exact V2 local arithmetic -/

def gstDigitS (R p : Nat) : Nat := R / 3^p % 3

def gstCarryS (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p

def gstStepCarryS (C d : Nat) : Nat := (C + 4*d) / 3

def gstAffineCarryS (D X p : Nat) : Nat :=
  (D + 4 * (X % 3^p)) / 3^p

/-- The x4 carry law holds at every natural coordinate. -/
theorem gstCarryS_forward_exact_all (R p : Nat) :
    gstCarryS R (p+1) = gstStepCarryS (gstCarryS R p) (gstDigitS R p) := by
  simp only [gstCarryS, gstDigitS, gstStepCarryS, Nat.pow_succ]
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : R % (3^p * 3) =
      R % 3^p + 3^p * (R / 3^p % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit]
  have hshape :
      4 * (R % 3^p + 3^p * (R / 3^p % 3)) =
        4 * (R % 3^p) + 3^p * (4 * (R / 3^p % 3)) := by ring
  rw [hshape, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ hp]

/-- Seeded x4 carry recurrence, again at every natural coordinate. -/
theorem gstAffineCarryS_forward_exact_all (D X p : Nat) :
    gstAffineCarryS D X (p+1) =
      gstStepCarryS (gstAffineCarryS D X p) (gstDigitS X p) := by
  simp only [gstAffineCarryS, gstDigitS, gstStepCarryS, Nat.pow_succ]
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : X % (3^p * 3) =
      X % 3^p + 3^p * (X / 3^p % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit]
  have hshape :
      D + 4 * (X % 3^p + 3^p * (X / 3^p % 3)) =
        (D + 4 * (X % 3^p)) +
          3^p * (4 * (X / 3^p % 3)) := by ring
  rw [hshape, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ hp]

/-- A legal seeded x4 carry remains one of the four GST carries. -/
theorem gstAffineCarryS_lt_four
    (D X p : Nat) (hD : D < 4) : gstAffineCarryS D X p < 4 := by
  unfold gstAffineCarryS
  have hpow : 0 < 3^p := Nat.pow_pos (by decide)
  have hr : X % 3^p < 3^p := Nat.mod_lt X hpow
  have hnum : D + 4 * (X % 3^p) < 3^p * 4 := by
    calc
      D + 4 * (X % 3^p) < 4 + 4 * (X % 3^p) :=
        Nat.add_lt_add_right hD _
      _ = 4 * ((X % 3^p) + 1) := by ring
      _ ≤ 4 * 3^p := Nat.mul_le_mul_left 4 (Nat.succ_le_of_lt hr)
      _ = 3^p * 4 := by ring
  exact Nat.div_lt_of_lt_mul hnum

inductive GSTSpaceV2S
  | null
  | altMinus
  | gstPlus
  deriving Repr, DecidableEq

def gstSpaceV2S (C : Nat) : GSTSpaceV2S :=
  if C = 0 then .null else if C = 3 then .gstPlus else .altMinus

structure GSTSevenAxisVertexV2S where
  x : Nat
  xNext : Nat
  carry : Nat
  space : GSTSpaceV2S
  digit : Nat
  boundary : Nat
  descent : Nat
  nextDescent : Nat
  deriving Repr

def gstSevenAxisVertexV2S (R N p : Nat) : GSTSevenAxisVertexV2S where
  x := p
  xNext := p+1
  carry := gstCarryS R p
  space := gstSpaceV2S (gstCarryS R p)
  digit := gstDigitS R p
  boundary := N - p
  descent := R / 3^p
  nextDescent := R / 3^(p+1)

/-- The V2 graph is literally a function on every natural depth. -/
def gstGraphV2InfiniteOrbitS (R N : Nat) : Nat → GSTSevenAxisVertexV2S :=
  fun p => gstSevenAxisVertexV2S R N p

theorem gst_graph_v2_infinite_orbit_stepS
    (R N p : Nat) :
    (gstGraphV2InfiniteOrbitS R N (p+1)).carry =
      gstStepCarryS
        (gstGraphV2InfiniteOrbitS R N p).carry
        (gstGraphV2InfiniteOrbitS R N p).digit := by
  simpa [gstGraphV2InfiniteOrbitS, gstSevenAxisVertexV2S] using
    gstCarryS_forward_exact_all R p

/-! ## Handwritten 2-world / 3-world / six-state bridge -/

def gstBinaryBridgeOutputS (a d : Nat) : Nat := (a + 2*d) % 3

def gstBinaryBridgeNextCarryS (a d : Nat) : Nat := (a + 2*d) / 3

def gstBinaryBridgeMassS (a d : Nat) : Nat := a + 2*d

def gstBinaryBridgeEventS (a d : Nat) : Nat :=
  d + 3 * gstBinaryBridgeOutputS a d

/-- Exact local event equation behind the handwritten numerator seven:
    J + 9*a' = 7*d + 3*a. -/
theorem gst_binary_bridge_event_seven_balanceS (a d : Nat) :
    gstBinaryBridgeEventS a d +
        9 * gstBinaryBridgeNextCarryS a d =
      7*d + 3*a := by
  unfold gstBinaryBridgeEventS gstBinaryBridgeOutputS
    gstBinaryBridgeNextCarryS
  have h := Nat.mod_add_div (a + 2*d) 3
  omega

/-- The handwritten pole coordinate 6 is outside every legal microscopic event
image; this is pointwise and therefore valid on an infinite path. -/
theorem gst_binary_bridge_event_ne_sixS
    (a d : Nat) (ha : a < 2) (hd : d < 3) :
    gstBinaryBridgeEventS a d ≠ 6 := by
  have hac : a = 0 ∨ a = 1 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hac with h0 | h1 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst a <;> subst d <;>
    norm_num [gstBinaryBridgeEventS, gstBinaryBridgeOutputS]

theorem gst_handwritten_event_pole_six_avoided_infiniteS
    (a d : Nat → Nat)
    (ha : ∀ j, a j < 2)
    (hd : ∀ j, d j < 3) :
    ∀ j, gstBinaryBridgeEventS (a j) (d j) ≠ 6 := by
  intro j
  exact gst_binary_bridge_event_ne_sixS (a j) (d j) (ha j) (hd j)

/-! ## Infinite `I != BIG1` branch -/

structure GSTBig1ClearInfinitePathS (a d : Nat → Nat) : Prop where
  bit_lt_two : ∀ j, a j < 2
  digit_lt_three : ∀ j, d j < 3
  information_ne_big1 : ∀ j, d j ≠ 1
  bridge_step : ∀ j, gstBinaryBridgeOutputS (a j) (d j) = d (j+1)

/-- One BIG1-clear nonzero bridge can only be the SURVIVE cell. -/
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

/-- No horizon: nonzero + `I != BIG1` forces BIG2 at every natural depth. -/
theorem gst_big1_clear_infinite_nonzero_forces_all_big2S
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ j, d j = 2 := by
  intro j
  induction j with
  | zero =>
      have hdlt := h.digit_lt_three 0
      have hd1 := h.information_ne_big1 0
      omega
  | succ j ih =>
      have ha := h.bit_lt_two j
      have hdlt := h.digit_lt_three j
      have hd1 := h.information_ne_big1 j
      have hout1 : gstBinaryBridgeOutputS (a j) (d j) ≠ 1 := by
        rw [h.bridge_step j]
        exact h.information_ne_big1 (j+1)
      have hs := gst_big1_clear_nonzero_bridge_forces_surviveS
        (a j) (d j) ha hdlt (by omega) hd1 hout1
      rw [← h.bridge_step j]
      exact hs.2.2.1

/-- Every edge of the same infinite branch is exactly SURVIVE mass 5/event 8. -/
theorem gst_big1_clear_infinite_edges_are_surviveS
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ j,
      a j = 1 ∧ d j = 2 ∧
      gstBinaryBridgeOutputS (a j) (d j) = 2 ∧
      gstBinaryBridgeMassS (a j) (d j) = 5 ∧
      gstBinaryBridgeEventS (a j) (d j) = 8 := by
  intro j
  have hdj := gst_big1_clear_infinite_nonzero_forces_all_big2S a d h h0 j
  have ha := h.bit_lt_two j
  have hdlt := h.digit_lt_three j
  have hd1 := h.information_ne_big1 j
  have hout1 : gstBinaryBridgeOutputS (a j) (d j) ≠ 1 := by
    rw [h.bridge_step j]
    exact h.information_ne_big1 (j+1)
  exact gst_big1_clear_nonzero_bridge_forces_surviveS
    (a j) (d j) ha hdlt (by omega) hd1 hout1

/-- Every translated two-edge window is the same physical right chord
    55_6 = 35 = 6^2-1. -/
theorem gst_big1_clear_infinite_every_window_chord35S
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ j,
      gstBinaryBridgeMassS (a j) (d j) +
        6 * gstBinaryBridgeMassS (a (j+1)) (d (j+1)) = 35 := by
  intro j
  have hj := gst_big1_clear_infinite_edges_are_surviveS a d h h0 j
  have hj1 := gst_big1_clear_infinite_edges_are_surviveS a d h h0 (j+1)
  rw [hj.2.2.2.1, hj1.2.2.2.1]

def gstBig1ProjectedPathCodeS
    (a d : Nat → Nat) (K : Nat) : Nat :=
  Finset.sum (Finset.range K)
    (fun j => gstBinaryBridgeMassS (a j) (d j) * 6^j)

/-- Every finite observation of the one infinite branch is the maximal base-six
word 55...55. Quantification is over all K, not one chosen cutoff. -/
theorem gst_big1_clear_infinite_all_six_prefixes_maximalS
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ K, gstBig1ProjectedPathCodeS a d K = 6^K - 1 := by
  intro K
  induction K with
  | zero => simp [gstBig1ProjectedPathCodeS]
  | succ K ih =>
      have hedge := gst_big1_clear_infinite_edges_are_surviveS a d h h0 K
      unfold gstBig1ProjectedPathCodeS at ih ⊢
      rw [Finset.sum_range_succ, ih, hedge.2.2.2.1]
      have hp : 0 < 6^K := Nat.pow_pos (by decide)
      rw [Nat.pow_succ]
      omega

/-! ## BIG-N / Omega-infinity branch -/

def gstOmegaNaturalTransferS (t T i : Nat) : Nat :=
  3^(t+1+i) * gstDigitS T i

/-- Every finite projection of the Omega stream has an exact closed form. -/
theorem gst_omega_natural_transfer_prefixS
    (t T K : Nat) :
    Finset.sum (Finset.range K) (fun i => gstOmegaNaturalTransferS t T i) =
      3^(t+1) * (T % 3^K) := by
  induction K with
  | zero =>
      simpa [gstOmegaNaturalTransferS] using Nat.mod_one T
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : T % 3^(K+1) =
          T % 3^K + 3^K * gstDigitS T K := by
        unfold gstDigitS
        rw [Nat.pow_succ, Nat.mod_mul]
      rw [hstep]
      have hpow : 3^(t+1+K) = 3^(t+1) * 3^K := Nat.pow_add 3 (t+1) K
      rw [gstOmegaNaturalTransferS, hpow]
      ring

/-- Elementary natural ceiling used only to prove stabilization of a stream
that is already indexed over all Nat. -/
theorem gst_self_lt_three_pow_succS : ∀ N : Nat, N < 3^(N+1)
  | 0 => by decide
  | N+1 => by
      have ih : N < 3^(N+1) := gst_self_lt_three_pow_succS N
      have hp : 0 < 3^(N+1) := Nat.pow_pos (by decide)
      calc
        N + 1 < 3^(N+1) + 1 := by omega
        _ ≤ 3^(N+1) * 3 := by omega
        _ = 3^((N+1)+1) := (Nat.pow_succ 3 (N+1)).symm

/-- An exact infinite natural sum is encoded by stabilization of all deep
prefix observations; the underlying function remains Nat-indexed. -/
def GSTControlledInfiniteSumS (f : Nat → Nat) (total : Nat) : Prop :=
  ∃ K0, ∀ K, K0 ≤ K → Finset.sum (Finset.range K) f = total

/-- BIG-N Omega is controlled on the full natural axis. -/
theorem gst_omega_natural_transfer_infinite_controlS
    (t N : Nat) :
    GSTControlledInfiniteSumS
      (gstOmegaNaturalTransferS t N) (3^(t+1) * N) := by
  refine ⟨N+1, ?_⟩
  intro K hK
  rw [gst_omega_natural_transfer_prefixS]
  have hbase : N < 3^(N+1) := gst_self_lt_three_pow_succS N
  have hpow : 3^(N+1) ≤ 3^K :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hK
  have hlt : N < 3^K := lt_of_lt_of_le hbase hpow
  rw [Nat.mod_eq_of_lt hlt]

/-- Pressure energy named in the handwritten Omega layer. -/
def gstOmegaPressureEnergyS (t N : Nat) : Nat := 1 + 3^(t+1) * N

theorem gst_handwritten_bigN_infinite_energy_controlS
    (t N : Nat) :
    GSTControlledInfiniteSumS
        (gstOmegaNaturalTransferS t N) (3^(t+1) * N) ∧
      1 + 3^(t+1) * N = gstOmegaPressureEnergyS t N := by
  exact ⟨gst_omega_natural_transfer_infinite_controlS t N, rfl⟩

/-! ## Pi: simultaneous multiplication/division at all scales -/

def gstOriginRemainingUS (t n : Nat) : Nat := 4^(3^t * n)

def gstOriginConsumedPrefixUS (t n K : Nat) : Nat :=
  4^(3^t * (n % 3^K))

/-- At every K simultaneously, consumed U times remaining U is the unchanged
original perfect-power energy. -/
theorem gst_origin_prefix_remaining_U_conservationS
    (t n K : Nat) :
    gstOriginConsumedPrefixUS t n K *
      gstOriginRemainingUS (t+K) (n / 3^K) =
      gstOriginRemainingUS t n := by
  unfold gstOriginConsumedPrefixUS gstOriginRemainingUS
  have hn : n = n % 3^K + 3^K * (n / 3^K) := by
    have h := Nat.mod_add_div n (3^K)
    omega
  have hexp :
      3^t * n =
        3^t * (n % 3^K) + 3^(t+K) * (n / 3^K) := by
    calc
      3^t*n = 3^t * (n % 3^K + 3^K*(n/3^K)) :=
        congrArg (fun q : Nat => 3^t * q) hn
      _ = 3^t*(n%3^K) + 3^t*3^K*(n/3^K) := by ring
      _ = 3^t*(n%3^K) + 3^(t+K)*(n/3^K) := by rw [← Nat.pow_add]
  calc
    4^(3^t * (n % 3^K)) * 4^(3^(t+K) * (n / 3^K)) =
        4^(3^t * (n % 3^K) + 3^(t+K) * (n / 3^K)) :=
      (Nat.pow_add 4 _ _).symm
    _ = 4^(3^t * n) := by rw [← hexp]

def GSTOriginInfiniteMulDivControlS (t n : Nat) : Prop :=
  ∀ K,
    gstOriginConsumedPrefixUS t n K *
        gstOriginRemainingUS (t+K) (n / 3^K) =
      gstOriginRemainingUS t n

theorem gst_origin_infinite_mul_div_controlS
    (t n : Nat) : GSTOriginInfiniteMulDivControlS t n := by
  intro K
  exact gst_origin_prefix_remaining_U_conservationS t n K

structure GSTOriginInfinityStateS where
  scale : Nat
  remainingOrigin : Nat
  consumedU : Nat
  remainingU : Nat
  deriving Repr

def gstOriginInfinityStateS (t n K : Nat) : GSTOriginInfinityStateS where
  scale := t+K
  remainingOrigin := n / 3^K
  consumedU := gstOriginConsumedPrefixUS t n K
  remainingU := gstOriginRemainingUS (t+K) (n / 3^K)

theorem gst_origin_infinity_state_energy_invariantS
    (t n K : Nat) :
    (gstOriginInfinityStateS t n K).consumedU *
        (gstOriginInfinityStateS t n K).remainingU =
      gstOriginRemainingUS t n := by
  exact gst_origin_prefix_remaining_U_conservationS t n K

/-! ## U: all-scale bad-language potential -/

def GSTHappyPairS (C d : Nat) : Prop := d = 2 ∧ (C = 0 ∨ C = 3)

def GSTBadPairS (C d : Nat) : Prop := ¬ GSTHappyPairS C d

def gstHandwrittenUChargeS (C : Nat) : Nat :=
  if C = 0 then 5 else if C = 3 then 21 else 15

theorem gst_bad_pair_iff_u_potential_nondecreaseS
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    GSTBadPairS C d ↔
      24*d + gstHandwrittenUChargeS C ≤
        3 * gstHandwrittenUChargeS (gstStepCarryS C d) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    norm_num [GSTBadPairS, GSTHappyPairS,
      gstHandwrittenUChargeS, gstStepCarryS]

theorem gst_prefix_residue_succ_exactS (X K : Nat) :
    X % 3^(K+1) = X % 3^K + 3^K * gstDigitS X K := by
  unfold gstDigitS
  rw [Nat.pow_succ, Nat.mod_mul]

/-- A bad prefix telescopes; quantifying this theorem over every K gives an
all-scale U controller. -/
theorem gst_bad_prefix_u_potential_boundS
    (D X K : Nat) (hD : D < 4)
    (hbad : ∀ j, j < K →
      GSTBadPairS (gstAffineCarryS D X j) (gstDigitS X j)) :
    24*(X % 3^K) + gstHandwrittenUChargeS D ≤
      3^K * gstHandwrittenUChargeS (gstAffineCarryS D X K) := by
  induction K with
  | zero =>
      have hx : X % 1 = 0 := Nat.mod_one X
      simp [gstAffineCarryS, hx]
  | succ K ih =>
      have hprev := ih (fun j hj => hbad j (by omega))
      have hcarrylt : gstAffineCarryS D X K < 4 :=
        gstAffineCarryS_lt_four D X K hD
      have hdigitlt : gstDigitS X K < 3 := by
        unfold gstDigitS
        exact Nat.mod_lt _ (by decide)
      have hlocal :=
        (gst_bad_pair_iff_u_potential_nondecreaseS
          (gstAffineCarryS D X K) (gstDigitS X K)
          hcarrylt hdigitlt).1 (hbad K (by omega))
      have hcarryStep := gstAffineCarryS_forward_exact_all D X K
      rw [gst_prefix_residue_succ_exactS X K]
      have hpow : 3^(K+1) = 3^K * 3 := by rw [Nat.pow_succ]
      calc
        24 * (X % 3^K + 3^K * gstDigitS X K) + gstHandwrittenUChargeS D
            = (24*(X % 3^K) + gstHandwrittenUChargeS D) +
                3^K * (24*gstDigitS X K) := by ring
        _ ≤ 3^K * gstHandwrittenUChargeS (gstAffineCarryS D X K) +
                3^K * (24*gstDigitS X K) := Nat.add_le_add_right hprev _
        _ = 3^K * (24*gstDigitS X K +
                gstHandwrittenUChargeS (gstAffineCarryS D X K)) := by ring
        _ ≤ 3^K * (3 * gstHandwrittenUChargeS
                (gstStepCarryS (gstAffineCarryS D X K) (gstDigitS X K))) :=
              Nat.mul_le_mul_left _ hlocal
        _ = 3^(K+1) * gstHandwrittenUChargeS (gstAffineCarryS D X (K+1)) := by
              rw [hpow, hcarryStep]
              ring

/-- Infinite badness means the U inequality is controlled at every scale at
once, not just at an arbitrarily chosen finite horizon. -/
theorem gst_v2_infinite_bad_u_control_all_scalesS
    (D X : Nat) (hD : D < 4)
    (hbad : ∀ j, GSTBadPairS (gstAffineCarryS D X j) (gstDigitS X j)) :
    ∀ K,
      24*(X % 3^K) + gstHandwrittenUChargeS D ≤
        3^K * gstHandwrittenUChargeS (gstAffineCarryS D X K) := by
  intro K
  exact gst_bad_prefix_u_potential_boundS D X K hD
    (fun j _hj => hbad j)

/-! ## Handwritten x-6 fibre / orientation -/

def gstMicroHighBitS (C : Nat) : Nat := C / 2

def gstMicroLowBitS (C : Nat) : Nat := C % 2

def gstFirstMicroMassS (C d : Nat) : Nat := gstMicroHighBitS C + 2*d

def gstFirstMicroOutputS (C d : Nat) : Nat := gstFirstMicroMassS C d % 3

def gstSecondMicroMassS (C d : Nat) : Nat :=
  gstMicroLowBitS C + 2*gstFirstMicroOutputS C d

def gstHandwrittenXCoordS (C d : Nat) : Nat :=
  gstFirstMicroMassS C d + gstSecondMicroMassS C d

def gstHandwrittenZOrientS (C d : Nat) : Int :=
  (gstSecondMicroMassS C d : Int) - (gstFirstMicroMassS C d : Int)

def gstHandwrittenUJumpS (C d : Nat) : Int :=
  3 * (gstHandwrittenUChargeS (gstStepCarryS C d) : Int) -
    (gstHandwrittenUChargeS C : Int) - 24*(d : Int)

theorem gst_handwritten_x_eq_six_iff_big2_orientationS
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    gstHandwrittenXCoordS C d = 6 ↔
      (C = 0 ∧ d = 1) ∨ (C = 0 ∧ d = 2) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;> decide

theorem gst_handwritten_x6_negative_iff_exposedS
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hx : gstHandwrittenXCoordS C d = 6) :
    gstHandwrittenUJumpS C d < 0 ↔ (C = 0 ∧ d = 2) := by
  have hor := (gst_handwritten_x_eq_six_iff_big2_orientationS C d hC hd).1 hx
  rcases hor with ⟨hC0,hd1⟩ | ⟨hC0,hd2⟩ <;>
    subst C <;> subst d <;> decide

theorem gst_handwritten_x6_infinite_orientation_controlS
    (C d : Nat → Nat)
    (hC : ∀ j, C j < 4)
    (hd : ∀ j, d j < 3)
    (hx : ∀ j, gstHandwrittenXCoordS (C j) (d j) = 6) :
    ∀ j,
      gstHandwrittenUJumpS (C j) (d j) < 0 ↔
        (C j = 0 ∧ d j = 2) := by
  intro j
  exact gst_handwritten_x6_negative_iff_exposedS
    (C j) (d j) (hC j) (hd j) (hx j)

/-! ## The two handwritten infinite regimes, in one controller -/

inductive GSTInformationRegimeS
  | bigN (t N : Nat)
  | notBig1 (a d : Nat → Nat)
      (path : GSTBig1ClearInfinitePathS a d)
      (nonzero : d 0 ≠ 0)

def GSTInformationRegimeControlledS : GSTInformationRegimeS → Prop
  | .bigN t N =>
      GSTControlledInfiniteSumS
          (gstOmegaNaturalTransferS t N) (3^(t+1) * N) ∧
        GSTOriginInfiniteMulDivControlS t N
  | .notBig1 a d _path _nonzero =>
      (∀ j,
        a j = 1 ∧ d j = 2 ∧
          gstBinaryBridgeMassS (a j) (d j) = 5 ∧
          gstBinaryBridgeEventS (a j) (d j) = 8) ∧
        (∀ K, gstBig1ProjectedPathCodeS a d K = 6^K - 1)

/-- Master theorem: whichever of the two handwritten branches is selected,
its infinite object is mathematically controlled at every natural scale. -/
theorem gst_handwritten_two_regime_infinite_controlS
    (r : GSTInformationRegimeS) : GSTInformationRegimeControlledS r := by
  cases r with
  | bigN t N =>
      exact ⟨gst_omega_natural_transfer_infinite_controlS t N,
        gst_origin_infinite_mul_div_controlS t N⟩
  | notBig1 a d path nonzero =>
      constructor
      · intro j
        have h := gst_big1_clear_infinite_edges_are_surviveS
          a d path nonzero j
        exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
      · exact gst_big1_clear_infinite_all_six_prefixes_maximalS
          a d path nonzero

end GSTInfiniteV2
