/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0048 / 1132
/-    Path         : workbench/SolOmegaSurgery.lean
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

import ErdosTernary2

/-!
  SolOmegaSurgery.lean

  Scratch/kernel-check module for the prefix-one Ω∞ surgery.
  It deliberately does NOT use `gst_prefix_one_navigation_lift`.
  The original file remains untouched while each replacement lemma is compiled.
-/

set_option maxRecDepth 10000000
set_option maxHeartbeats 100000000

inductive GSTOmegaEvent
  | create
  | destroy
  | survive
  | neither
  deriving Repr, DecidableEq

def gstOmegaParentOutputDigit (w : GSTOmegaState) : Nat :=
  gstOutputDigit w.parentCarry w.parentDigit

def gstOmegaEventOfState (w : GSTOmegaState) : GSTOmegaEvent :=
  let d := w.parentDigit
  let e := gstOmegaParentOutputDigit w
  if d = 2 then
    if e = 2 then .survive else .destroy
  else
    if e = 2 then .create else .neither

def gstOmegaEvent (s k m j : Nat) : GSTOmegaEvent :=
  gstOmegaEventOfState (gstOmega s k m j)

theorem gst_omega_event_survive_iff_raw (w : GSTOmegaState) :
    gstOmegaEventOfState w = .survive ↔
      w.parentDigit = 2 ∧ gstOmegaParentOutputDigit w = 2 := by
  unfold gstOmegaEventOfState gstOmegaParentOutputDigit
  constructor
  · intro h
    by_cases hd : w.parentDigit = 2
    · refine ⟨hd, ?_⟩
      rw [if_pos hd] at h
      by_cases he : gstOutputDigit w.parentCarry w.parentDigit = 2
      · exact he
      · rw [if_neg he] at h
        cases h
    · rw [if_neg hd] at h
      by_cases he : gstOutputDigit w.parentCarry w.parentDigit = 2
      · rw [if_pos he] at h
        cases h
      · rw [if_neg he] at h
        cases h
  · rintro ⟨hd, he⟩
    rw [if_pos hd, if_pos he]

def GSTOmegaEvent.mirror : GSTOmegaEvent → GSTOmegaEvent
  | .create => .destroy
  | .destroy => .create
  | .survive => .survive
  | .neither => .neither

def GSTOmegaEvent.Active : GSTOmegaEvent → Prop
  | .create => True
  | .destroy => True
  | .survive => True
  | .neither => False

theorem gst_omega_event_mirror_involutive :
    Function.Involutive GSTOmegaEvent.mirror := by
  intro e
  cases e <;> rfl

theorem gst_omega_active_mirror_fixed_iff_survive (e : GSTOmegaEvent) :
    e.Active ∧ e.mirror = e ↔ e = .survive := by
  cases e <;> simp [GSTOmegaEvent.Active, GSTOmegaEvent.mirror]

theorem gst_omega_active_nonfixed_iff_create_or_destroy (e : GSTOmegaEvent) :
    e.Active ∧ e.mirror ≠ e ↔ e = .create ∨ e = .destroy := by
  cases e <;> simp [GSTOmegaEvent.Active, GSTOmegaEvent.mirror]

theorem gst_omega_prefix_one_parentCarry_lt_four
    (s n j : Nat) (hs : 1 ≤ s) :
    (gstOmega s 1 n j).parentCarry < 4 := by
  have hp := gst_omega_parent_projection s 1 n j hs
  have hpos : 1 ≤ 1 + j := by omega
  have hlt :
      gstCarry (gstNavigationConstant s (1 + 3^1 * n)) (1 + j) < 4 :=
    gstCarry_lt_four _ _ hpos
  rw [hp.2] at hlt
  simpa [Nat.pow_one] using hlt

theorem gst_omega_prefix_one_survive_implies_gate
    (s n j : Nat) (hs : 1 ≤ s)
    (hsurvive : gstOmegaEvent s 1 n j = .survive) :
    (gstOmega s 1 n j).parentDigit = 2 ∧
      ((gstOmega s 1 n j).parentCarry = 0 ∨
       (gstOmega s 1 n j).parentCarry = 3) := by
  have hraw :
      (gstOmega s 1 n j).parentDigit = 2 ∧
        gstOmegaParentOutputDigit (gstOmega s 1 n j) = 2 :=
    (gst_omega_event_survive_iff_raw (gstOmega s 1 n j)).1 hsurvive
  refine ⟨hraw.1, ?_⟩
  have hC : (gstOmega s 1 n j).parentCarry < 4 :=
    gst_omega_prefix_one_parentCarry_lt_four s n j hs
  rcases nat_lt_four_cases (gstOmega s 1 n j).parentCarry hC with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exfalso
    have hout := hraw.2
    rw [gstOmegaParentOutputDigit, h1, hraw.1] at hout
    norm_num [gstOutputDigit] at hout
  · exfalso
    have hout := hraw.2
    rw [gstOmegaParentOutputDigit, h2, hraw.1] at hout
    norm_num [gstOutputDigit] at hout
  · exact Or.inr h3

theorem gst_omega_prefix_one_gate_implies_survive
    (s n j : Nat)
    (hgate :
      (gstOmega s 1 n j).parentDigit = 2 ∧
      ((gstOmega s 1 n j).parentCarry = 0 ∨
       (gstOmega s 1 n j).parentCarry = 3)) :
    gstOmegaEvent s 1 n j = .survive := by
  apply (gst_omega_event_survive_iff_raw (gstOmega s 1 n j)).2
  refine ⟨hgate.1, ?_⟩
  rcases hgate.2 with h0 | h3
  · rw [gstOmegaParentOutputDigit, gstOutputDigit, hgate.1, h0]
  · rw [gstOmegaParentOutputDigit, gstOutputDigit, hgate.1, h3]

theorem gst_omega_prefix_one_survive_iff_gatePolynomial_zero
    (s n j : Nat) (hs : 1 ≤ s) :
    gstOmegaEvent s 1 n j = .survive ↔
      GSTOmegaGatePolynomial (gstOmega s 1 n j) = 0 := by
  constructor
  · intro hsurvive
    apply (gst_omega_gate_polynomial_zero_iff (gstOmega s 1 n j)).2
    exact gst_omega_prefix_one_survive_implies_gate s n j hs hsurvive
  · intro hzero
    have hgate :=
      (gst_omega_gate_polynomial_zero_iff (gstOmega s 1 n j)).1 hzero
    exact gst_omega_prefix_one_gate_implies_survive s n j hgate

theorem gst_omega_prefix_one_active_fixed_iff_gate_zero
    (s n j : Nat) (hs : 1 ≤ s) :
    (gstOmegaEvent s 1 n j).Active ∧
      (gstOmegaEvent s 1 n j).mirror = gstOmegaEvent s 1 n j ↔
      GSTOmegaGatePolynomial (gstOmega s 1 n j) = 0 := by
  rw [gst_omega_active_mirror_fixed_iff_survive]
  exact gst_omega_prefix_one_survive_iff_gatePolynomial_zero s n j hs

/-- Under a complete Ω bad trace, no parent event can be SURVIVE. -/
theorem gst_prefix_one_bad_implies_no_survive
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∀ j, gstOmegaEvent s 1 n j ≠ .survive := by
  intro j hSurvive
  have hZero : GSTOmegaGatePolynomial (gstOmega s 1 n j) = 0 :=
    (gst_omega_prefix_one_survive_iff_gatePolynomial_zero s n j hs).1 hSurvive
  have hNe := hBad j
  change GSTOmegaGatePolynomial (gstOmega s 1 n j) ≠ 0 at hNe
  exact hNe hZero

#check gst_omega_universal_equation
#check gst_omega_origin_exact
#check gst_omega_paradoxEnergy_succ
#check gst_omega_affine_tail_block_echo
#check gst_omega_childZeroSet_nonempty_of_navigation_witness
#check gst_omega_infiniteBadTrace_iff_seededAffine
