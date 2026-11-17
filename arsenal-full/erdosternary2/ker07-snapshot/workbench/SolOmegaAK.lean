/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0046 / 1132
/-    Path         : workbench/SolOmegaAK.lean
/-    Ref          : main
/-    First-commit : 2026-08-14 21:44:31 +0530  (83dd56f)
/-    Last-commit  : 2026-08-14 21:44:31 +0530  (83dd56f)
/-    Total commits: 1
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/1] 2026-08-14 21:44:31 +0530  83dd56f  (ker07-dev)
/-        Import Sol inline surgery handoff and GST graph workspace
/- ====================================================================== -/

import SolOmegaSurgery

/-- Position predicates used by the paradox/mirror layer. -/
def GSTOmegaMirrorFixedAt (s n j : Nat) : Prop :=
  (gstOmegaEvent s 1 n j).mirror = gstOmegaEvent s 1 n j

def GSTOmegaActiveAt (s n j : Nat) : Prop :=
  (gstOmegaEvent s 1 n j).Active

def GSTOmegaFreeMirrorAt (s n j : Nat) : Prop :=
  GSTOmegaActiveAt s n j ∧ ¬ GSTOmegaMirrorFixedAt s n j

theorem gst_omega_freeMirror_iff_create_or_destroy (s n j : Nat) :
    GSTOmegaFreeMirrorAt s n j ↔
      gstOmegaEvent s 1 n j = .create ∨
      gstOmegaEvent s 1 n j = .destroy := by
  unfold GSTOmegaFreeMirrorAt GSTOmegaActiveAt GSTOmegaMirrorFixedAt
  exact gst_omega_active_nonfixed_iff_create_or_destroy
    (gstOmegaEvent s 1 n j)

structure GSTPrefixOneOmegaData (s n : Nat) where
  childGateIndex : Nat
  childGate :
    (gstOmega s 1 n childGateIndex).childDigit = 2 ∧
      ((gstOmega s 1 n childGateIndex).childCarry = 0 ∨
       (gstOmega s 1 n childGateIndex).childCarry = 3)
  energyExact :
    ∀ j, (gstOmega s 1 n j).paradoxEnergy = 4^(3^(s+1)*n)
  energyConserved :
    ∀ j,
      (gstOmega s 1 n (j+1)).paradoxEnergy =
        (gstOmega s 1 n j).paradoxEnergy
  omegaStepExact :
    ∀ j,
      gstOmega s 1 n (j+1) =
        gstOmegaStep (4^(3^s)) (gstOmega s 1 n j)
  echoExact :
    c s / 3 + 4^(3^s) * gstNavigationConstant (s+1) n =
      c s / 3 + gstNavigationConstant (s+1) n +
        3^(s+1) * c s * gstNavigationConstant (s+1) n

noncomputable def gst_prefix_one_omegaData
    (s n : Nat) (hs : 1 ≤ s)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) :
    GSTPrefixOneOmegaData s n := by
  have hne : (GSTOmegaChildZeroSet s 1 n).Nonempty :=
    gst_omega_childZeroSet_nonempty_of_navigation_witness s 1 n hchild
  have hexists :
      ∃ j,
        (gstOmega s 1 n j).childDigit = 2 ∧
        ((gstOmega s 1 n j).childCarry = 0 ∨
         (gstOmega s 1 n j).childCarry = 3) := by
    rcases hne with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change (gstOmega s 1 n j).childDigit = 2 ∧
      ((gstOmega s 1 n j).childCarry = 0 ∨
       (gstOmega s 1 n j).childCarry = 3) at hj
    exact hj
  let jChild := Classical.choose hexists
  have hjChild :
      (gstOmega s 1 n jChild).childDigit = 2 ∧
      ((gstOmega s 1 n jChild).childCarry = 0 ∨
       (gstOmega s 1 n jChild).childCarry = 3) :=
    Classical.choose_spec hexists
  refine
    { childGateIndex := jChild
      childGate := hjChild
      energyExact := ?_
      energyConserved := ?_
      omegaStepExact := ?_
      echoExact := ?_ }
  · intro j
    simpa [Nat.add_assoc] using gst_omega_origin_exact s 1 n j hs
  · intro j
    exact gst_omega_paradoxEnergy_succ s 1 n j
  · intro j
    exact gst_omega_universal_equation s 1 n j
  · simpa [Nat.pow_one, Nat.add_assoc, Nat.mul_assoc] using
      gst_omega_affine_tail_block_echo s 1 n hs

theorem gst_prefix_one_bad_implies_active_free
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∀ j, GSTOmegaActiveAt s n j → GSTOmegaFreeMirrorAt s n j := by
  intro j hActive
  refine ⟨hActive, ?_⟩
  intro hFixed
  have hSurvive : gstOmegaEvent s 1 n j = .survive :=
    (gst_omega_active_mirror_fixed_iff_survive
      (gstOmegaEvent s 1 n j)).1 ⟨hActive, hFixed⟩
  exact gst_prefix_one_bad_implies_no_survive s n hs hBad j hSurvive

theorem gst_prefix_one_bad_active_is_create_or_destroy
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n)
    (j : Nat) (hActive : GSTOmegaActiveAt s n j) :
    gstOmegaEvent s 1 n j = .create ∨
    gstOmegaEvent s 1 n j = .destroy := by
  exact (gst_omega_freeMirror_iff_create_or_destroy s n j).1
    (gst_prefix_one_bad_implies_active_free s n hs hBad j hActive)

def gstParadoxOrigin : Nat := 1

def gstParadoxFuture (t T j : Nat) : Nat :=
  3^(t+1+j) * (T / 3^j)

def gstParadoxPast (t T j : Nat) : Nat :=
  3^(t+1) * (T % 3^j)

theorem gst_infinite_paradox_energy_split (t T j : Nat) :
    gstInfiniteParadoxEnergy t T j =
      gstParadoxOrigin + gstParadoxFuture t T j + gstParadoxPast t T j := by
  rfl

inductive GSTParadoxComponent
  | origin
  | future
  | past
  deriving Repr, DecidableEq

def GSTParadoxComponent.mirror : GSTParadoxComponent → GSTParadoxComponent
  | .origin => .origin
  | .future => .past
  | .past => .future

theorem gst_paradox_component_mirror_involutive :
    Function.Involutive GSTParadoxComponent.mirror := by
  intro x
  cases x <;> rfl

theorem gst_paradox_component_fixed_iff_origin (x : GSTParadoxComponent) :
    x.mirror = x ↔ x = .origin := by
  cases x <;> simp [GSTParadoxComponent.mirror]

def gstParadoxComponentValue (t T j : Nat) : GSTParadoxComponent → Nat
  | .origin => gstParadoxOrigin
  | .future => gstParadoxFuture t T j
  | .past => gstParadoxPast t T j

theorem gst_paradox_energy_as_components (t T j : Nat) :
    gstInfiniteParadoxEnergy t T j =
      gstParadoxComponentValue t T j .origin +
      gstParadoxComponentValue t T j .future +
      gstParadoxComponentValue t T j .past := by
  rfl

def gstParadoxTransfer (t T j : Nat) : Nat :=
  3^(t+1+j) * gstDigit T j

theorem gst_paradox_future_transfer (t T j : Nat) :
    gstParadoxFuture t T j =
      gstParadoxFuture t T (j+1) + gstParadoxTransfer t T j := by
  unfold gstParadoxFuture gstParadoxTransfer
  have hsplit :
      T / 3^j =
        3 * (T / 3^(j+1)) + gstDigit T j := by
    unfold gstDigit
    have h := Nat.mod_add_div (T / 3^j) 3
    have hq : T / 3^j / 3 = T / 3^(j+1) := by
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    rw [hq] at h
    omega
  conv_lhs => rw [hsplit]
  rw [Nat.mul_add]
  have hpow : 3^(t+1+j) * 3 = 3^(t+1+(j+1)) := by
    rw [show t+1+(j+1) = (t+1+j)+1 by omega, Nat.pow_succ]
  have hfirst :
      3^(t+1+j) * (3 * (T / 3^(j+1))) =
        3^(t+1+(j+1)) * (T / 3^(j+1)) := by
    calc
      3^(t+1+j) * (3 * (T / 3^(j+1))) =
          (3^(t+1+j) * 3) * (T / 3^(j+1)) := by ac_rfl
      _ = 3^(t+1+(j+1)) * (T / 3^(j+1)) := by rw [hpow]
  rw [hfirst]

theorem gst_paradox_past_transfer (t T j : Nat) :
    gstParadoxPast t T (j+1) =
      gstParadoxPast t T j + gstParadoxTransfer t T j := by
  unfold gstParadoxPast gstParadoxTransfer
  rw [gst_residue_succ_exact, Nat.mul_add]
  have hpow :
      3^(t+1) * (3^j * gstDigit T j) =
        3^(t+1+j) * gstDigit T j := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
  rw [hpow]

theorem gst_paradox_transfer_exact (t T j : Nat) :
    gstParadoxFuture t T j =
        gstParadoxFuture t T (j+1) + gstParadoxTransfer t T j ∧
      gstParadoxPast t T (j+1) =
        gstParadoxPast t T j + gstParadoxTransfer t T j := by
  exact ⟨gst_paradox_future_transfer t T j,
    gst_paradox_past_transfer t T j⟩

theorem gst_paradox_transfer_pos_of_digit_two
    (t T j : Nat) (hd : gstDigit T j = 2) :
    0 < gstParadoxTransfer t T j := by
  unfold gstParadoxTransfer
  rw [hd]
  have hp : 0 < 3^(t+1+j) := Nat.pow_pos (by decide)
  omega

theorem gst_prefix_one_child_transfer_pos
    (s n : Nat) (data : GSTPrefixOneOmegaData s n) :
    0 < gstParadoxTransfer
      (s+1) (gstNavigationConstant (s+1) n) data.childGateIndex := by
  apply gst_paradox_transfer_pos_of_digit_two
  simpa only [gstOmega] using data.childGate.1
