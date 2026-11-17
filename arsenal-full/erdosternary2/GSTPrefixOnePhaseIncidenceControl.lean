import GSTCanonicalEnergyControl
import GSTInfiniteCoupledLedger

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2
open GSTV2

/-!
# Canonical prefix-one phase-incidence coordinates

This module places the exact earliest horizontal chord in the same theorem as
the all-depth parent bad suffix and the coupled Past synchronization law.  It
does not identify the horizontal base-six chord code with the vertical
ternary Past coordinate: those are different observables.  Instead it records
the exact vertical Past equation forced by each of the two carry-correlated
chords.
-/

def gpt56PhaseA (s : Nat) : Nat := 4^(3^s)

def gpt56PhaseT (s n : Nat) : Nat :=
  gstNavigationConstant (s+1) n

def gpt56PhaseInitialState (s n : Nat) : GSTV2.CoupledState where
  parentSeed := 1
  parentOffset := c s / 3
  childResidue := 1 + 4 * (c s / 3)
  childCarry := 0
  childTail := gpt56PhaseT s n

/-- Remaining horizontal multiplier after one physical x2 column. -/
def gpt56PhaseA1 (s : Nat) : Nat := 2^(2 * 3^s - 1)

/-- Alternate coupled representation after moving one physical x2 column
into the child word. -/
def gpt56PhaseInitialState1 (s n : Nat) : GSTV2.CoupledState where
  parentSeed := 1
  parentOffset := c s / 3
  childResidue := 1 + 4 * (c s / 3)
  childCarry := 0
  childTail := 2 * gpt56PhaseT s n

/-- Moving one x2 column from the multiplier into the child preserves the
complete horizontal product. -/
theorem gpt56_phase_A1_mul_two (s : Nat) (hs : 1 ≤ s) :
    gpt56PhaseA1 s * 2 = gpt56PhaseA s := by
  have hwidth : 1 ≤ 2 * 3^s := by
    have hp : 0 < 3^s := Nat.pow_pos (by decide)
    omega
  calc
    gpt56PhaseA1 s * 2 = 2^(2 * 3^s - 1) * 2^1 := by
      simp [gpt56PhaseA1]
    _ = 2^((2 * 3^s - 1) + 1) := by rw [Nat.pow_add]
    _ = 2^(2 * 3^s) := by congr 1 <;> omega
    _ = gpt56PhaseA s := by
      rw [← gpt56_parent_multiplier_is_binary_bridge]
      rfl

def GPT56NullChord (s n q : Nat) : Prop :=
  gstDigit (gpt56PhaseT s n) q = 2 ∧
  gstCarry (gpt56PhaseT s n) q = 0 ∧
  GSTFirstBig1AtS
    (fun r => GSTPhysicalKernel.binaryColumnDigit
      (gpt56PhaseT s n) q r) 1 ∧
  gstBig1ProjectedPathCodeS
    (fun r => GSTPhysicalKernel.binaryColumnCarry
      (gpt56PhaseT s n) q r)
    (fun r => GSTPhysicalKernel.binaryColumnDigit
      (gpt56PhaseT s n) q r) 1 = 4 ∧
  Finset.sum (Finset.range 1)
    (fun r => GSTPhysicalKernel.signedKernelTwice
      (GSTPhysicalKernel.binaryColumnCarry (gpt56PhaseT s n) q r)
      (GSTPhysicalKernel.binaryColumnDigit (gpt56PhaseT s n) q r)) =
        (-14 : Int)

def GPT56PlusChord (s n q : Nat) : Prop :=
  gstDigit (gpt56PhaseT s n) q = 2 ∧
  gstCarry (gpt56PhaseT s n) q = 3 ∧
  GSTFirstBig1AtS
    (fun r => GSTPhysicalKernel.binaryColumnDigit
      (gpt56PhaseT s n) q r) 3 ∧
  gstBig1ProjectedPathCodeS
    (fun r => GSTPhysicalKernel.binaryColumnCarry
      (gpt56PhaseT s n) q r)
    (fun r => GSTPhysicalKernel.binaryColumnDigit
      (gpt56PhaseT s n) q r) 3 = 179 ∧
  Finset.sum (Finset.range 3)
    (fun r => GSTPhysicalKernel.signedKernelTwice
      (GSTPhysicalKernel.binaryColumnCarry (gpt56PhaseT s n) q r)
      (GSTPhysicalKernel.binaryColumnDigit (gpt56PhaseT s n) q r)) = 0

theorem gpt56_phase_initial_residue_lt
    (s : Nat) (hs : 1 ≤ s) :
    1 + 4 * (c s / 3) < gpt56PhaseA s := by
  have hcmod : c s % 3 = 1 := c_mod3 s hs
  have hcne : c s ≠ 0 := by
    intro h0
    rw [h0] at hcmod
    norm_num at hcmod
  have hcpos : 0 < c s := Nat.pos_of_ne_zero hcne
  have hcdiv : c s / 3 ≤ c s := Nat.div_le_self _ _
  have h4 : 4 * (c s / 3) ≤ 4 * c s :=
    Nat.mul_le_mul_left 4 hcdiv
  have h49 : 4 * c s < 9 * c s := by omega
  have hpow : 9 ≤ 3^(s+1) := by
    have h : 3^2 ≤ 3^(s+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at h ⊢
    exact h
  have h9A : 9 * c s ≤ 3^(s+1) * c s :=
    Nat.mul_le_mul_right (c s) hpow
  have hLTE := lte_identity s hs
  unfold gpt56PhaseA
  rw [hLTE]
  omega

theorem gpt56_phase_initial_invariant
    (s n : Nat) (hs : 1 ≤ s) :
    GSTV2.CoupledInvariant (gpt56PhaseA s)
      (gpt56PhaseInitialState s n) := by
  constructor
  · simp [gpt56PhaseInitialState]
  · simpa [gpt56PhaseInitialState] using
      gpt56_phase_initial_residue_lt s hs

theorem gpt56_phase_bad_to_v2_seeded
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTV2.SeededBadTrace 1
      ((gpt56PhaseInitialState s n).parentWord (gpt56PhaseA s)) := by
  have hold := (gst_omega_infiniteBadTrace_iff_seededAffine s 1 n).1 hBad
  have hseed : (4 * (c s % 3^1)) / 3^1 = 1 := by
    rw [Nat.pow_one, c_mod3 s hs]
  rw [hseed] at hold
  simpa [GSTV2.SeededBadTrace, GSTV2.Happy, GSTV2.affineCarry,
    GSTV2.digit, GSTV2.CoupledState.parentWord,
    gpt56PhaseInitialState, gpt56PhaseA, gpt56PhaseT,
    GSTSeededAffineBadTrace, GSTBadPair, gstAffineMulCarry, gstDigit] using hold

theorem gpt56_phase_infinite_bad_control
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTV2.InfiniteBadCoupledControl
      (gpt56PhaseA s) (gpt56PhaseInitialState s n) := by
  apply GSTV2.infinite_bad_coupled_control
  · unfold gpt56PhaseA
    exact Nat.pow_pos (by decide)
  · exact gpt56_phase_initial_invariant s n hs
  · rfl
  · exact gpt56_phase_bad_to_v2_seeded s n hs hBad

/-!
At the reindexed earliest gate, the NULL and GST+ signatures give different
exact vertical Past equations.  The parent bad suffix and the all-depth
synchronization equation are retained at that same coordinate.
-/
theorem gpt56_prefix_one_exact_gate_past_incidence
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gpt56PhaseT s n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∃ q,
      (gpt56PhaseInitialState s n).parentPast (gpt56PhaseA s) q +
          3^q *
            (GSTV2.coupledOrbit (gpt56PhaseA s)
              (gpt56PhaseInitialState s n) q).childResidue =
        (gpt56PhaseInitialState s n).childResidue +
          gpt56PhaseA s * (gpt56PhaseInitialState s n).childPast q ∧
      GSTV2.SeededBadTrace
        (GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).parentSeed
        ((GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).parentWord (gpt56PhaseA s)) ∧
      ((GPT56NullChord s n q ∧
          (gpt56PhaseInitialState s n).childPast q =
            4 * (gpt56PhaseT s n % 3^q)) ∨
       (GPT56PlusChord s n q ∧
          (gpt56PhaseInitialState s n).childPast q + 3 * 3^q =
            4 * (gpt56PhaseT s n % 3^q))) := by
  have hpacket := gpt56_prefix_one_live_exact_chord_energy_packet
    s n hs hn (by simpa [gpt56PhaseT] using hchild) hBad
  dsimp only at hpacket
  obtain ⟨q, hchord, _hseeded, _henergy⟩ := hpacket
  have hcontrol := gpt56_phase_infinite_bad_control s n hs hBad
  have hsync := GSTV2.coupledOrbit_past_synchronization
    (gpt56PhaseA s) (gpt56PhaseInitialState s n)
    (by unfold gpt56PhaseA; exact Nat.pow_pos (by decide))
    (gpt56_phase_initial_invariant s n hs) q
  refine ⟨q, hsync, hcontrol.parentBadSuffix q, ?_⟩
  rcases hchord with hnull | hplus
  · have hdiv :
        (4 * (gpt56PhaseT s n % 3^q)) / 3^q = 0 := by
      simpa [gpt56PhaseT, gstCarry] using hnull.2.1
    have hdecomp := Nat.mod_add_div
      (4 * (gpt56PhaseT s n % 3^q)) (3^q)
    rw [hdiv] at hdecomp
    have hmod :
        (4 * (gpt56PhaseT s n % 3^q)) % 3^q =
          4 * (gpt56PhaseT s n % 3^q) := by
      simpa using hdecomp
    have hpast :
        (gpt56PhaseInitialState s n).childPast q =
          4 * (gpt56PhaseT s n % 3^q) := by
      simpa [GSTV2.CoupledState.childPast, GSTV2.seededPast,
        gpt56PhaseInitialState] using hmod
    exact Or.inl ⟨by simpa [GPT56NullChord, gpt56PhaseT] using hnull, hpast⟩
  · have hdiv :
        (4 * (gpt56PhaseT s n % 3^q)) / 3^q = 3 := by
      simpa [gpt56PhaseT, gstCarry] using hplus.2.1
    have hdecomp := Nat.mod_add_div
      (4 * (gpt56PhaseT s n % 3^q)) (3^q)
    rw [hdiv] at hdecomp
    have hmod :
        (4 * (gpt56PhaseT s n % 3^q)) % 3^q + 3 * 3^q =
          4 * (gpt56PhaseT s n % 3^q) := by
      omega
    have hpast :
        (gpt56PhaseInitialState s n).childPast q + 3 * 3^q =
          4 * (gpt56PhaseT s n % 3^q) := by
      simpa [GSTV2.CoupledState.childPast, GSTV2.seededPast,
        gpt56PhaseInitialState] using hmod
    exact Or.inr ⟨by simpa [GPT56PlusChord, gpt56PhaseT] using hplus, hpast⟩

/-- A seed-one affine x4 stream always regenerates inside the four physical
carry states.  This is an all-depth bound, not a terminal-state argument. -/
theorem gpt56_affineCarry_one_lt_four (X K : Nat) :
    GSTV2.affineCarry 1 X K < 4 := by
  unfold GSTV2.affineCarry
  have hp : 0 < 3^K := Nat.pow_pos (by decide)
  have hr : X % 3^K < 3^K := Nat.mod_lt _ hp
  exact (Nat.div_lt_iff_lt_mul hp).2 (by omega)

/-- The parent digit emitted by one coupled state. -/
def gpt56ParentEmitted (A : Nat) (st : GSTV2.CoupledState) : Nat :=
  (st.parentOffset + A * (st.childTail % 3)) % 3

/-- Canonical horizontal multiplier phase at the two-digit ternary scale. -/
theorem gpt56_phase_A_mod_nine (s : Nat) (hs : 1 ≤ s) :
    gpt56PhaseA s % 9 = 1 := by
  unfold gpt56PhaseA
  rw [lte_identity s hs, Nat.add_mod, Nat.mul_mod,
    pow3_mod9 (s+1) (by omega)]
  norm_num

/-- The remaining multiplier after one physical x2 column lies in the other
nonzero residue class modulo three. -/
theorem gpt56_phase_A1_mod_three (s : Nat) (hs : 1 ≤ s) :
    gpt56PhaseA1 s % 3 = 2 := by
  have hA3 : gpt56PhaseA s % 3 = 1 := by
    have hdiv : 3 ∣ 9 := by decide
    calc
      gpt56PhaseA s % 3 = (gpt56PhaseA s % 9) % 3 := by
        rw [Nat.mod_mod_of_dvd _ hdiv]
      _ = 1 := by rw [gpt56_phase_A_mod_nine s hs]
  have hmul := congrArg (fun z : Nat => z % 3)
    (gpt56_phase_A1_mul_two s hs)
  rw [Nat.mul_mod, hA3] at hmul
  have hlt : gpt56PhaseA1 s % 3 < 3 := Nat.mod_lt _ (by decide)
  omega

/-- Exact ancestry law for the parent-offset phase.  When `A = 1 (mod 9)`,
one coupled step exposes the next ternary coordinate of the old offset and
adds precisely the carry created by its current phase plus the child digit.
This holds for every state and does not assume badness or termination. -/
theorem gpt56_coupledStep_parentOffset_phase
    (A : Nat) (st : GSTV2.CoupledState) (hAmod9 : A % 9 = 1) :
    (GSTV2.coupledStep A st).parentOffset % 3 =
      (((st.parentOffset % 3 + st.childTail % 3) / 3) +
        st.parentOffset / 3) % 3 := by
  let r := st.childTail % 3
  let p := st.parentOffset % 3
  let Q := st.parentOffset / 3
  let B := A / 9
  have hA : A = 1 + 9*B := by
    have h := Nat.mod_add_div A 9
    rw [hAmod9] at h
    dsimp [B]
    omega
  have hZ : st.parentOffset = p + 3*Q := by
    have h := Nat.mod_add_div st.parentOffset 3
    dsimp [p, Q]
    omega
  have hnum :
      st.parentOffset + A*r = (p+r) + 3*(Q + 3*(B*r)) := by
    rw [hA, hZ]
    ring
  unfold GSTV2.coupledStep
  dsimp only
  change ((st.parentOffset + A*r) / 3) % 3 =
    (((p+r)/3) + Q) % 3
  rw [hnum, Nat.add_mul_div_left _ _ (by decide : 0 < (3:Nat))]
  simp [Nat.add_mod, Nat.mul_mod]

/-- Complete local phase table at a child digit-two collision.  The table is
all-Nat and transition-level: it neither invokes a support horizon nor a
terminal state.  Parent badness is used only in phase zero, where the emitted
parent digit is also two and therefore excludes carries zero and three. -/
theorem gpt56_parent_digit_two_phase_table
    (A : Nat) (st : GSTV2.CoupledState)
    (hAmod : A % 3 = 1)
    (hchildDigit : st.childTail % 3 = 2)
    (hseedlt : st.parentSeed < 4)
    (hbad : ¬ GSTV2.Happy st.parentSeed (gpt56ParentEmitted A st)) :
    (st.parentOffset % 3 = 0 →
      gpt56ParentEmitted A st = 2 ∧
      (st.parentSeed = 1 ∨ st.parentSeed = 2) ∧
      (GSTV2.coupledStep A st).parentSeed = 3) ∧
    (st.parentOffset % 3 = 1 →
      gpt56ParentEmitted A st = 0 ∧
      ((GSTV2.coupledStep A st).parentSeed = 0 ∨
       (GSTV2.coupledStep A st).parentSeed = 1)) ∧
    (st.parentOffset % 3 = 2 →
      gpt56ParentEmitted A st = 1 ∧
      ((GSTV2.coupledStep A st).parentSeed = 1 ∨
       (GSTV2.coupledStep A st).parentSeed = 2)) := by
  have hseedCases :
      st.parentSeed = 0 ∨ st.parentSeed = 1 ∨
      st.parentSeed = 2 ∨ st.parentSeed = 3 := by
    omega
  have hstep :
      (GSTV2.coupledStep A st).parentSeed =
        GSTV2.cellNextCarry st.parentSeed (gpt56ParentEmitted A st) := by
    rfl
  constructor
  · intro hphase
    have hemit : gpt56ParentEmitted A st = 2 := by
      simp [gpt56ParentEmitted, Nat.add_mod, Nat.mul_mod, Nat.mod_mod,
        hphase, hAmod, hchildDigit]
    have hnot0 : st.parentSeed ≠ 0 := by
      intro hzero
      exact hbad ⟨hemit, Or.inl hzero⟩
    have hnot3 : st.parentSeed ≠ 3 := by
      intro hthree
      exact hbad ⟨hemit, Or.inr hthree⟩
    have hmiddle : st.parentSeed = 1 ∨ st.parentSeed = 2 := by
      omega
    refine ⟨hemit, hmiddle, ?_⟩
    rw [hstep, hemit]
    rcases hmiddle with h1 | h2
    · simp [GSTV2.cellNextCarry, GSTV2.cellMass, h1]
    · simp [GSTV2.cellNextCarry, GSTV2.cellMass, h2]
  constructor
  · intro hphase
    have hemit : gpt56ParentEmitted A st = 0 := by
      simp [gpt56ParentEmitted, Nat.add_mod, Nat.mul_mod, Nat.mod_mod,
        hphase, hAmod, hchildDigit]
    refine ⟨hemit, ?_⟩
    rw [hstep, hemit]
    rcases hseedCases with h0 | h1 | h2 | h3
    · exact Or.inl (by simp [GSTV2.cellNextCarry, GSTV2.cellMass, h0])
    · exact Or.inl (by simp [GSTV2.cellNextCarry, GSTV2.cellMass, h1])
    · exact Or.inl (by simp [GSTV2.cellNextCarry, GSTV2.cellMass, h2])
    · exact Or.inr (by simp [GSTV2.cellNextCarry, GSTV2.cellMass, h3])
  · intro hphase
    have hemit : gpt56ParentEmitted A st = 1 := by
      simp [gpt56ParentEmitted, Nat.add_mod, Nat.mul_mod, Nat.mod_mod,
        hphase, hAmod, hchildDigit]
    refine ⟨hemit, ?_⟩
    rw [hstep, hemit]
    rcases hseedCases with h0 | h1 | h2 | h3
    · exact Or.inl (by simp [GSTV2.cellNextCarry, GSTV2.cellMass, h0])
    · exact Or.inl (by simp [GSTV2.cellNextCarry, GSTV2.cellMass, h1])
    · exact Or.inr (by simp [GSTV2.cellNextCarry, GSTV2.cellMass, h2])
    · exact Or.inr (by simp [GSTV2.cellNextCarry, GSTV2.cellMass, h3])

/-- The complete local phase table realized at the exact canonical earliest
gate, together with its correlated NULL/GST+ chord signature. -/
theorem gpt56_prefix_one_exact_gate_three_phase_table
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gpt56PhaseT s n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∃ q,
      (GPT56NullChord s n q ∨ GPT56PlusChord s n q) ∧
      let st := GSTV2.coupledOrbit (gpt56PhaseA s)
        (gpt56PhaseInitialState s n) q
      (st.parentOffset % 3 = 0 →
        gpt56ParentEmitted (gpt56PhaseA s) st = 2 ∧
        (st.parentSeed = 1 ∨ st.parentSeed = 2) ∧
        (GSTV2.coupledStep (gpt56PhaseA s) st).parentSeed = 3) ∧
      (st.parentOffset % 3 = 1 →
        gpt56ParentEmitted (gpt56PhaseA s) st = 0 ∧
        ((GSTV2.coupledStep (gpt56PhaseA s) st).parentSeed = 0 ∨
         (GSTV2.coupledStep (gpt56PhaseA s) st).parentSeed = 1)) ∧
      (st.parentOffset % 3 = 2 →
        gpt56ParentEmitted (gpt56PhaseA s) st = 1 ∧
        ((GSTV2.coupledStep (gpt56PhaseA s) st).parentSeed = 1 ∨
         (GSTV2.coupledStep (gpt56PhaseA s) st).parentSeed = 2)) := by
  obtain ⟨q, _hsync, _hbadSuffix, hbranch⟩ :=
    gpt56_prefix_one_exact_gate_past_incidence s n hs hn hchild hBad
  have hchord : GPT56NullChord s n q ∨ GPT56PlusChord s n q := by
    rcases hbranch with hnull | hplus
    · exact Or.inl hnull.1
    · exact Or.inr hplus.1
  let st := GSTV2.coupledOrbit (gpt56PhaseA s)
    (gpt56PhaseInitialState s n) q
  have hd2 : gstDigit (gpt56PhaseT s n) q = 2 := by
    rcases hchord with hnull | hplus
    · exact hnull.1
    · exact hplus.1
  have hchildDigit : st.childTail % 3 = 2 := by
    dsimp [st]
    calc
      (GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).childTail % 3 =
          GSTV2.digit (gpt56PhaseInitialState s n).childTail q :=
        GSTV2.coupledOrbit_childDigit_exact
          (gpt56PhaseA s) (gpt56PhaseInitialState s n) q
      _ = 2 := by
        simpa [gpt56PhaseInitialState, gpt56PhaseT,
          GSTV2.digit, gstDigit] using hd2
  have hAmod : gpt56PhaseA s % 3 = 1 := by
    simp [gpt56PhaseA, Nat.pow_mod]
  have hcontrol := gpt56_phase_infinite_bad_control s n hs hBad
  have hbad : ¬ GSTV2.Happy st.parentSeed
      (gpt56ParentEmitted (gpt56PhaseA s) st) := by
    dsimp [st, gpt56ParentEmitted]
    exact GSTV2.coupledOrbit_parent_bad_current
      (gpt56PhaseA s) (gpt56PhaseInitialState s n)
      hcontrol.parentBad q
  have hseedlt : st.parentSeed < 4 := by
    dsimp [st]
    rw [GSTV2.coupledOrbit_parentSeed_exact]
    simpa [gpt56PhaseInitialState] using
      gpt56_affineCarry_one_lt_four
        ((gpt56PhaseInitialState s n).parentWord (gpt56PhaseA s)) q
  refine ⟨q, hchord, ?_⟩
  dsimp only
  exact gpt56_parent_digit_two_phase_table
    (gpt56PhaseA s) st hAmod hchildDigit hseedlt hbad

/-- The ancestry law instantiated at the exact canonical earliest gate. -/
theorem gpt56_prefix_one_exact_gate_offset_phase
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gpt56PhaseT s n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∃ q,
      (GPT56NullChord s n q ∨ GPT56PlusChord s n q) ∧
      (GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) (q+1)).parentOffset % 3 =
        ((((GSTV2.coupledOrbit (gpt56PhaseA s)
              (gpt56PhaseInitialState s n) q).parentOffset % 3 +
            (GSTV2.coupledOrbit (gpt56PhaseA s)
              (gpt56PhaseInitialState s n) q).childTail % 3) / 3) +
          (GSTV2.coupledOrbit (gpt56PhaseA s)
            (gpt56PhaseInitialState s n) q).parentOffset / 3) % 3 := by
  obtain ⟨q, hchord, _htable⟩ :=
    gpt56_prefix_one_exact_gate_three_phase_table s n hs hn hchild hBad
  refine ⟨q, hchord, ?_⟩
  rw [GSTV2.coupledOrbit]
  exact gpt56_coupledStep_parentOffset_phase
    (gpt56PhaseA s)
    (GSTV2.coupledOrbit (gpt56PhaseA s)
      (gpt56PhaseInitialState s n) q)
    (gpt56_phase_A_mod_nine s hs)

/-- Exact all-depth parent-offset closed form specialized at the certified
earliest gate.  This connects the local collision phase directly to the
canonical origin and its lower ternary residue. -/
theorem gpt56_prefix_one_exact_gate_parentOffset_closed
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gpt56PhaseT s n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∃ q,
      (GPT56NullChord s n q ∨ GPT56PlusChord s n q) ∧
      (GSTV2.coupledOrbit (gpt56PhaseA s)
        (gpt56PhaseInitialState s n) q).parentOffset =
          (c s / 3 + gpt56PhaseA s *
            (gpt56PhaseT s n % 3^q)) / 3^q := by
  obtain ⟨q, hchord, _htable⟩ :=
    gpt56_prefix_one_exact_gate_three_phase_table s n hs hn hchild hBad
  refine ⟨q, hchord, ?_⟩
  simpa [gpt56PhaseInitialState] using
    GSTV2.coupledOrbit_parentOffset_exact
      (gpt56PhaseA s) (gpt56PhaseInitialState s n) q

/-- In the GST+ chord, the one-column alternate representation has exactly
the same parent information word.  The horizontal carry is one, so at the
certified vertical gate the original parent offset is the alternate offset
plus the entire remaining multiplier. -/
theorem gpt56_plus_chord_one_column_offset_shift
    (s n q : Nat) (hs : 1 ≤ s) (hplus : GPT56PlusChord s n q) :
    (GSTV2.coupledOrbit (gpt56PhaseA s)
        (gpt56PhaseInitialState s n) q).parentOffset =
      (GSTV2.coupledOrbit (gpt56PhaseA1 s)
        (gpt56PhaseInitialState1 s n) q).parentOffset +
        gpt56PhaseA1 s := by
  let T := gpt56PhaseT s n
  let P := 3^q
  let R := T % P
  have hP : 0 < P := by
    dsimp [P]
    exact Nat.pow_pos (by decide)
  have hcarry4 : (4*R)/P = 3 := by
    simpa [T, P, R, GPT56PlusChord, gpt56PhaseT, gstCarry] using hplus.2.1
  have hrem4 : (4*R) % P < P := Nat.mod_lt _ hP
  have hsplit4 : 4*R = P*((4*R)/P) + (4*R)%P :=
    (Nat.div_add_mod (4*R) P).symm
  rw [hcarry4] at hsplit4
  have h2lo : P ≤ 2*R := by omega
  have hRlt : R < P := Nat.mod_lt _ hP
  have h2hi : 2*R < 2*P := by omega
  have hdiv2lo : 1 ≤ (2*R)/P :=
    (Nat.le_div_iff_mul_le hP).2 (by simpa using h2lo)
  have hdiv2hi : (2*R)/P < 2 :=
    (Nat.div_lt_iff_lt_mul hP).2 (by simpa using h2hi)
  have hdiv2 : (2*R)/P = 1 := by omega
  have hmod2 : (2*T) % P = (2*R) % P := by
    simp [T, R, Nat.mul_mod]
  have hdecomp2 : (2*R)%P + P = 2*R := by
    have h := Nat.mod_add_div (2*R) P
    rw [hdiv2] at h
    simpa [Nat.mul_comm] using h
  have hmul := gpt56_phase_A1_mul_two s hs
  have hnum :
      c s / 3 + gpt56PhaseA s * R =
        (c s / 3 + gpt56PhaseA1 s * ((2*T) % P)) +
          P * gpt56PhaseA1 s := by
    calc
      c s / 3 + gpt56PhaseA s * R =
          c s / 3 + (gpt56PhaseA1 s * 2) * R := by rw [hmul]
      _ = c s / 3 + gpt56PhaseA1 s * (2*R) := by ring
      _ = c s / 3 + gpt56PhaseA1 s * ((2*R)%P + P) := by rw [hdecomp2]
      _ = (c s / 3 + gpt56PhaseA1 s * ((2*T)%P)) +
          P * gpt56PhaseA1 s := by rw [hmod2]; ring
  rw [GSTV2.coupledOrbit_parentOffset_exact,
    GSTV2.coupledOrbit_parentOffset_exact]
  change (c s / 3 + gpt56PhaseA s * R) / P =
    (c s / 3 + gpt56PhaseA1 s * ((2*T)%P)) / P +
      gpt56PhaseA1 s
  rw [hnum, Nat.add_mul_div_left _ _ hP]

/-- Modulo three, the exact GST+ horizontal bridge crosses to the next offset
phase.  The equality is a corollary of the full natural-number offset shift,
not an independently projected residue claim. -/
theorem gpt56_plus_chord_one_column_phase_shift
    (s n q : Nat) (hs : 1 ≤ s) (hplus : GPT56PlusChord s n q) :
    (GSTV2.coupledOrbit (gpt56PhaseA s)
        (gpt56PhaseInitialState s n) q).parentOffset % 3 =
      ((GSTV2.coupledOrbit (gpt56PhaseA1 s)
          (gpt56PhaseInitialState1 s n) q).parentOffset % 3 + 2) % 3 := by
  have hshift := gpt56_plus_chord_one_column_offset_shift s n q hs hplus
  have hmod := congrArg (fun z : Nat => z % 3) hshift
  simpa [Nat.add_mod, gpt56_phase_A1_mod_three s hs] using hmod

/-- The same one-column move that crosses the parent phase turns the child
GST+ gate into the exact middle-carry trap: its digit stays two, while its
ordinary x4 carry becomes two. -/
theorem gpt56_plus_chord_one_column_child_trap
    (s n q : Nat) (hplus : GPT56PlusChord s n q) :
    gstDigit (2 * gpt56PhaseT s n) q = 2 ∧
      gstCarry (2 * gpt56PhaseT s n) q = 2 := by
  let T := gpt56PhaseT s n
  let P := 3^q
  let R := T % P
  have hP : 0 < P := by
    dsimp [P]
    exact Nat.pow_pos (by decide)
  have hRlt : R < P := Nat.mod_lt _ hP
  have hd2raw : T / P % 3 = 2 := by
    simpa [T, P, GPT56PlusChord, gstDigit] using hplus.1
  have hcarry4 : (4*R)/P = 3 := by
    simpa [T, P, R, GPT56PlusChord, gstCarry] using hplus.2.1
  have hsplit4 : 4*R = P*((4*R)/P) + (4*R)%P :=
    (Nat.div_add_mod (4*R) P).symm
  rw [hcarry4] at hsplit4
  have h2lo : P ≤ 2*R := by omega
  have h2hi : 2*R < 2*P := by omega
  have hdiv2lo : 1 ≤ (2*R)/P :=
    (Nat.le_div_iff_mul_le hP).2 (by simpa using h2lo)
  have hdiv2hi : (2*R)/P < 2 :=
    (Nat.div_lt_iff_lt_mul hP).2 (by simpa using h2hi)
  have hdiv2 : (2*R)/P = 1 := by omega
  have hdAltRaw : (2*T)/P % 3 = 2 := by
    have hq2 := gpt56_mul_ternary_quotient_split 2 T q
    change (2*T)/P = (2*R)/P + 2*(T/P) at hq2
    rw [hq2, Nat.add_mod, Nat.mul_mod, hdiv2, hd2raw]
  have hd8 : (8*T)/P % 3 = 1 := by
    have h := hplus.2.2.1.1
    simpa [GSTPhysicalKernel.binaryColumnDigit, T, P] using h
  have hq8 := gpt56_mul_ternary_quotient_split 8 T q
  change (8*T)/P = (8*R)/P + 8*(T/P) at hq8
  rw [hq8, Nat.add_mod, Nat.mul_mod, hd2raw] at hd8
  norm_num at hd8
  have hdiv8mod : ((8*R)/P) % 3 = 0 := by omega
  have h8lo : 6*P ≤ 8*R := by omega
  have hdiv8lo : 6 ≤ (8*R)/P :=
    (Nat.le_div_iff_mul_le hP).2 (by simpa using h8lo)
  have h8lt8 : (8*R)/P < 8 :=
    (Nat.div_lt_iff_lt_mul hP).2 (by omega)
  have hdiv8 : (8*R)/P = 6 := by omega
  have h8hi : 8*R < 7*P :=
    (Nat.div_lt_iff_lt_mul hP).1 (by omega)
  have hmod2 : (2*T) % P = (2*R) % P := by
    simp [T, R, Nat.mul_mod]
  have hdecomp2 : (2*R)%P + P = 2*R := by
    have h := Nat.mod_add_div (2*R) P
    rw [hdiv2] at h
    simpa [Nat.mul_comm] using h
  have hmass : 4*((2*T)%P) + 4*P = 8*R := by
    rw [hmod2]
    omega
  have hcarryAltLo : 2*P ≤ 4*((2*T)%P) := by omega
  have hcarryAltHi : 4*((2*T)%P) < 3*P := by omega
  have hcarryAltLo' : 2 ≤ (4*((2*T)%P))/P :=
    (Nat.le_div_iff_mul_le hP).2 (by simpa using hcarryAltLo)
  have hcarryAltHi' : (4*((2*T)%P))/P < 3 :=
    (Nat.div_lt_iff_lt_mul hP).2 (by simpa using hcarryAltHi)
  have hcarryAlt : (4*((2*T)%P))/P = 2 := by omega
  constructor
  · simpa [gstDigit, T, P] using hdAltRaw
  · simpa [gstCarry, T, P] using hcarryAlt

/-- Canonical exact-gate dichotomy retaining the cross-subspace offset shift
in the GST+ alternative. -/
theorem gpt56_prefix_one_exact_gate_horizontal_phase_crossing
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gpt56PhaseT s n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∃ q,
      GPT56NullChord s n q ∨
      (GPT56PlusChord s n q ∧
        (GSTV2.coupledOrbit (gpt56PhaseA s)
            (gpt56PhaseInitialState s n) q).parentOffset =
          (GSTV2.coupledOrbit (gpt56PhaseA1 s)
            (gpt56PhaseInitialState1 s n) q).parentOffset +
              gpt56PhaseA1 s) := by
  obtain ⟨q, hchord, _htable⟩ :=
    gpt56_prefix_one_exact_gate_three_phase_table s n hs hn hchild hBad
  refine ⟨q, ?_⟩
  rcases hchord with hnull | hplus
  · exact Or.inl hnull
  · exact Or.inr ⟨hplus,
      gpt56_plus_chord_one_column_offset_shift s n q hs hplus⟩

/-!
The zero phase of the parent offset is now a restrictive bad-language event.
At the child digit-two collision it makes the parent digit two as well.  Parent
badness excludes the Happy carries zero and three, hence the current seed is
one or two.  The next regenerated seed is exactly three, so the complete bad
suffix forbids digit two at the next parent coordinate.
-/
theorem gpt56_prefix_one_zero_phase_forces_next_escape
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gpt56PhaseT s n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∃ q,
      (GPT56NullChord s n q ∨ GPT56PlusChord s n q) ∧
      ((GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).parentOffset % 3 = 0 →
        ((GSTV2.coupledOrbit (gpt56PhaseA s)
            (gpt56PhaseInitialState s n) q).parentSeed = 1 ∨
         (GSTV2.coupledOrbit (gpt56PhaseA s)
            (gpt56PhaseInitialState s n) q).parentSeed = 2) ∧
        (GSTV2.coupledOrbit (gpt56PhaseA s)
            (gpt56PhaseInitialState s n) (q+1)).parentSeed = 3 ∧
        ((GSTV2.coupledOrbit (gpt56PhaseA s)
              (gpt56PhaseInitialState s n) (q+1)).parentOffset +
            gpt56PhaseA s *
              ((GSTV2.coupledOrbit (gpt56PhaseA s)
                (gpt56PhaseInitialState s n) (q+1)).childTail % 3)) % 3 ≠ 2) := by
  obtain ⟨q, _hsync, _hbadSuffix, hbranch⟩ :=
    gpt56_prefix_one_exact_gate_past_incidence s n hs hn hchild hBad
  have hchord : GPT56NullChord s n q ∨ GPT56PlusChord s n q := by
    rcases hbranch with hnull | hplus
    · exact Or.inl hnull.1
    · exact Or.inr hplus.1
  refine ⟨q, hchord, ?_⟩
  intro hphase
  have hd2 : gstDigit (gpt56PhaseT s n) q = 2 := by
    rcases hchord with hnull | hplus
    · exact hnull.1
    · exact hplus.1
  have hd :
      (GSTV2.coupledOrbit (gpt56PhaseA s)
        (gpt56PhaseInitialState s n) q).childTail % 3 = 2 := by
    calc
      (GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).childTail % 3 =
          GSTV2.digit (gpt56PhaseInitialState s n).childTail q :=
        GSTV2.coupledOrbit_childDigit_exact
          (gpt56PhaseA s) (gpt56PhaseInitialState s n) q
      _ = 2 := by
        simpa [gpt56PhaseInitialState, gpt56PhaseT,
          GSTV2.digit, gstDigit] using hd2
  have hAmod : gpt56PhaseA s % 3 = 1 := by
    simp [gpt56PhaseA, Nat.pow_mod]
  have hemit :
      ((GSTV2.coupledOrbit (gpt56PhaseA s)
            (gpt56PhaseInitialState s n) q).parentOffset +
          gpt56PhaseA s *
            ((GSTV2.coupledOrbit (gpt56PhaseA s)
              (gpt56PhaseInitialState s n) q).childTail % 3)) % 3 = 2 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, hphase, hAmod, hd]
  have hcontrol := gpt56_phase_infinite_bad_control s n hs hBad
  have hbadCurrent := GSTV2.coupledOrbit_parent_bad_current
    (gpt56PhaseA s) (gpt56PhaseInitialState s n)
    hcontrol.parentBad q
  have hseedlt :
      (GSTV2.coupledOrbit (gpt56PhaseA s)
        (gpt56PhaseInitialState s n) q).parentSeed < 4 := by
    rw [GSTV2.coupledOrbit_parentSeed_exact]
    simpa [gpt56PhaseInitialState] using
      gpt56_affineCarry_one_lt_four
        ((gpt56PhaseInitialState s n).parentWord (gpt56PhaseA s)) q
  have hseedNot :
      (GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).parentSeed ≠ 0 ∧
      (GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).parentSeed ≠ 3 := by
    constructor
    · intro hzero
      exact hbadCurrent ⟨hemit, Or.inl hzero⟩
    · intro hthree
      exact hbadCurrent ⟨hemit, Or.inr hthree⟩
  have hmiddle :
      (GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).parentSeed = 1 ∨
      (GSTV2.coupledOrbit (gpt56PhaseA s)
          (gpt56PhaseInitialState s n) q).parentSeed = 2 := by
    omega
  have hnextSeed :
      (GSTV2.coupledOrbit (gpt56PhaseA s)
        (gpt56PhaseInitialState s n) (q+1)).parentSeed = 3 := by
    rw [GSTV2.coupledOrbit]
    change GSTV2.cellNextCarry
      (GSTV2.coupledOrbit (gpt56PhaseA s)
        (gpt56PhaseInitialState s n) q).parentSeed
      (((GSTV2.coupledOrbit (gpt56PhaseA s)
            (gpt56PhaseInitialState s n) q).parentOffset +
          gpt56PhaseA s *
            ((GSTV2.coupledOrbit (gpt56PhaseA s)
              (gpt56PhaseInitialState s n) q).childTail % 3)) % 3) = 3
    rw [hemit]
    rcases hmiddle with h1 | h2
    · simp [GSTV2.cellNextCarry, GSTV2.cellMass, h1]
    · simp [GSTV2.cellNextCarry, GSTV2.cellMass, h2]
  have hbadNext := GSTV2.coupledOrbit_parent_bad_current
    (gpt56PhaseA s) (gpt56PhaseInitialState s n)
    hcontrol.parentBad (q+1)
  refine ⟨hmiddle, hnextSeed, ?_⟩
  intro hnextDigit
  exact hbadNext ⟨hnextDigit, Or.inr hnextSeed⟩

#check gpt56_prefix_one_exact_gate_past_incidence
#check gpt56_phase_A_mod_nine
#check gpt56_phase_A1_mul_two
#check gpt56_phase_A1_mod_three
#check gpt56_coupledStep_parentOffset_phase
#check gpt56_prefix_one_exact_gate_offset_phase
#check GSTV2.coupledOrbit_parentOffset_exact
#check gpt56_prefix_one_exact_gate_parentOffset_closed
#check gpt56_plus_chord_one_column_offset_shift
#check gpt56_plus_chord_one_column_phase_shift
#check gpt56_plus_chord_one_column_child_trap
#check gpt56_prefix_one_exact_gate_horizontal_phase_crossing
#check gpt56_parent_digit_two_phase_table
#check gpt56_prefix_one_exact_gate_three_phase_table
#check gpt56_prefix_one_zero_phase_forces_next_escape
#print axioms gpt56_prefix_one_exact_gate_past_incidence
#print axioms gpt56_phase_A_mod_nine
#print axioms gpt56_phase_A1_mul_two
#print axioms gpt56_phase_A1_mod_three
#print axioms gpt56_coupledStep_parentOffset_phase
#print axioms gpt56_prefix_one_exact_gate_offset_phase
#print axioms GSTV2.coupledOrbit_parentOffset_exact
#print axioms gpt56_prefix_one_exact_gate_parentOffset_closed
#print axioms gpt56_plus_chord_one_column_offset_shift
#print axioms gpt56_plus_chord_one_column_phase_shift
#print axioms gpt56_plus_chord_one_column_child_trap
#print axioms gpt56_prefix_one_exact_gate_horizontal_phase_crossing
#print axioms gpt56_parent_digit_two_phase_table
#print axioms gpt56_prefix_one_exact_gate_three_phase_table
#print axioms gpt56_prefix_one_zero_phase_forces_next_escape
