import GSTGraphV2CanonicalRenormalization
import GSTGraphV2CanonicalDescentOntology

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2CanonicalPhaseSteering

open GSTCanonicalTailLTE
open GSTPerfectPowerTailNavigation
open GSTPrefixOneSeedCore
open GSTGraphV2CanonicalRenormalization
open GSTGraphV2CanonicalDescentOntology
open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTGraphV2PerfectPowerBlock
open GSTV2

/-- From scale one onward the exact LTE coefficient is rigid modulo nine. -/
theorem lteCoeff_mod9_seven_of_one_le : ∀ s : Nat, 1 ≤ s →
    lteCoeff s % 9 = 7 := by
  intro s hs
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hs
  induction r with
  | zero =>
      norm_num [lteCoeff]
  | succ r ih =>
      rw [show 1 + (r + 1) = (1 + r) + 1 by omega, lteCoeff]
      have hpow1 : 9 ∣ 3 ^ ((1 + r) + 1) := by
        use 3^r
        rw [show (1 + r) + 1 = 2 + r by omega, pow_add]
        norm_num
      have hpow2 : 9 ∣ 3 ^ (2 * (1 + r) + 1) := by
        use 3^(2*r+1)
        rw [show 2 * (1 + r) + 1 = 2 + (2*r+1) by omega, pow_add]
        norm_num
      have hterm1 :
          (3 ^ ((1 + r) + 1) * lteCoeff (1 + r) ^ 2) % 9 = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hpow1 _)
      have hterm2 :
          (3 ^ (2 * (1 + r) + 1) * lteCoeff (1 + r) ^ 3) % 9 = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hpow2 _)
      rw [Nat.add_mod, hterm2, Nat.add_zero,
        Nat.add_mod, hterm1, ih]
      norm_num

/-- The canonical horizontal prefix offset is rigidly two modulo three. -/
theorem prefixOffset_mod3_two
    (s : Nat) (hs : 1 ≤ s) :
    prefixOffset s % 3 = 2 := by
  have hc9 : unitTail s % 9 = 7 := by
    rw [unitTail_eq_lteCoeff]
    exact lteCoeff_mod9_seven_of_one_le s hs
  have hsplit := Nat.mod_add_div (unitTail s) 9
  rw [hc9] at hsplit
  have hunit : unitTail s = 7 + 9 * (unitTail s / 9) := by
    simpa [Nat.add_comm, Nat.mul_comm] using hsplit.symm
  rw [prefixOffset, hunit]
  have hdiv : (7 + 9 * (unitTail s / 9)) / 3 =
      2 + 3 * (unitTail s / 9) := by omega
  rw [hdiv]
  simp

/-- A canonical tail remembers the stripped origin phase exactly modulo three. -/
theorem canonicalTail_mod3_origin
    (r n : Nat) :
    canonicalTail r n % 3 = n % 3 := by
  let a := n % 3
  let m := n / 3
  have ha : a < 3 := Nat.mod_lt n (by decide)
  have hsplit : n = a + 3*m := by
    dsimp [a, m]
    simpa [Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div n 3).symm
  have h := canonicalTail_three_adic_strip r a m ha
  rw [← hsplit] at h
  rw [h]
  simp [a]

/-- The first right-edge digit of the canonical perfect-power rectangle is
exactly the origin phase translated by the rigid Graph-V2 offset two. -/
theorem canonical_right_digit_cut_phase
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+2)).seven.digit =
      (2 + n % 3) % 3 := by
  have hDigit := graphCoupledState_parentDigit_exact
    (canonicalEnergy s n) (canonicalWidth s) (s+2)
  have hOffset := canonical_graph_parentOffset_cut_exact s n
  have hTail := canonical_graph_childTail_cut_exact s n
  rw [hOffset, hTail] at hDigit
  have hA : 4^(canonicalWidth s) % 3 = 1 := by
    simp [canonicalWidth, Nat.pow_mod]
  have hz := prefixOffset_mod3_two s hs
  have hT := canonicalTail_mod3_origin (s+1) n
  rw [Nat.add_mod, Nat.mul_mod, hz, hA, hT] at hDigit
  simpa [Nat.add_mod] using hDigit.symm

/-- Phase zero steers the right seed from one to three in one vertical step. -/
theorem canonical_right_phase_zero_next_seed
    (s n : Nat) (hs : 1 ≤ s) (ha : n % 3 = 0) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+3)).seven.carry = 3 := by
  have hseed := canonical_graph_parentSeed_cut_one s n hs
  have hdigit := canonical_right_digit_cut_phase s n hs
  rw [ha] at hdigit
  norm_num at hdigit
  have hstep := (graph_cell_exact
    (canonicalEnergy s n) (canonicalWidth s) (s+2)).2
  rw [show s + 3 = (s+2)+1 by omega]
  rw [← hstep]
  simp [hseed, hdigit, GSTV2.cellNextCarry, GSTV2.cellMass,
    GST2DMixedEmergence.nextCarry]

/-- Phase one steers the right seed from one to zero in one vertical step. -/
theorem canonical_right_phase_one_next_seed
    (s n : Nat) (hs : 1 ≤ s) (ha : n % 3 = 1) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+3)).seven.carry = 0 := by
  have hseed := canonical_graph_parentSeed_cut_one s n hs
  have hdigit := canonical_right_digit_cut_phase s n hs
  rw [ha] at hdigit
  norm_num at hdigit
  have hstep := (graph_cell_exact
    (canonicalEnergy s n) (canonicalWidth s) (s+2)).2
  rw [show s + 3 = (s+2)+1 by omega]
  rw [← hstep]
  simp [hseed, hdigit, GSTV2.cellNextCarry, GSTV2.cellMass,
    GST2DMixedEmergence.nextCarry]

/-- Phase two leaves the right seed in sector one after the first vertical step. -/
theorem canonical_right_phase_two_next_seed
    (s n : Nat) (hs : 1 ≤ s) (ha : n % 3 = 2) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+3)).seven.carry = 1 := by
  have hseed := canonical_graph_parentSeed_cut_one s n hs
  have hdigit := canonical_right_digit_cut_phase s n hs
  rw [ha] at hdigit
  norm_num at hdigit
  have hstep := (graph_cell_exact
    (canonicalEnergy s n) (canonicalWidth s) (s+2)).2
  rw [show s + 3 = (s+2)+1 by omega]
  rw [← hstep]
  simp [hseed, hdigit, GSTV2.cellNextCarry, GSTV2.cellMass,
    GST2DMixedEmergence.nextCarry]


/-! ## Branch-free canonical phase transfer -/

/-- Deterministic right-edge carry transfer generated by one origin ternary
phase.  The three phase sectors are encoded by one arithmetic map. -/
def rightSeedPhaseTransfer (r : Nat) : Nat :=
  (1 + 4 * ((2 + r) % 3)) / 3

/-- The phase transfer has the exact physical spectrum `0 ↦ 3, 1 ↦ 0,
2 ↦ 1`. -/
theorem rightSeedPhaseTransfer_spectrum :
    rightSeedPhaseTransfer 0 = 3 ∧
    rightSeedPhaseTransfer 1 = 0 ∧
    rightSeedPhaseTransfer 2 = 1 := by
  decide

/-- **BRANCH-FREE PHASE STEERING.**  The next canonical right seed is the
single transfer map applied to the origin phase.  The three earlier branch
theorems are therefore projections of one deterministic law. -/
theorem canonical_right_next_seed_exact
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+3)).seven.carry =
      rightSeedPhaseTransfer (n % 3) := by
  have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [canonical_right_phase_zero_next_seed s n hs h0, h0]
    norm_num [rightSeedPhaseTransfer]
  · rw [canonical_right_phase_one_next_seed s n hs h1, h1]
    norm_num [rightSeedPhaseTransfer]
  · rw [canonical_right_phase_two_next_seed s n hs h2, h2]
    norm_num [rightSeedPhaseTransfer]

/-- On the physical phase sector, the transfer is injective: the next right
seed remembers the consumed origin phase exactly. -/
theorem rightSeedPhaseTransfer_injective_on_trits
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    (h : rightSeedPhaseTransfer a = rightSeedPhaseTransfer b) :
    a = b := by
  have ha_cases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb_cases : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha_cases with rfl | rfl | rfl <;>
    rcases hb_cases with rfl | rfl | rfl
  all_goals norm_num [rightSeedPhaseTransfer] at h
  all_goals rfl

/-- Hence equality of next canonical right seeds forces equality of origin
phases.  The steering law is reversible at the phase level. -/
theorem canonical_right_next_seed_eq_iff_phase_eq
    (s n m : Nat) (hs : 1 ≤ s) :
    (graph (canonicalEnergy s n) (canonicalWidth s) (s+3)).seven.carry =
        (graph (canonicalEnergy s m) (canonicalWidth s) (s+3)).seven.carry
      ↔ n % 3 = m % 3 := by
  rw [canonical_right_next_seed_exact s n hs,
      canonical_right_next_seed_exact s m hs]
  constructor
  · intro h
    exact rightSeedPhaseTransfer_injective_on_trits
      (Nat.mod_lt n (by decide)) (Nat.mod_lt m (by decide)) h
  · intro h
    rw [h]


#check lteCoeff_mod9_seven_of_one_le
#check prefixOffset_mod3_two
#check canonicalTail_mod3_origin
#check canonical_right_digit_cut_phase
#check canonical_right_phase_zero_next_seed
#check canonical_right_phase_one_next_seed
#check canonical_right_phase_two_next_seed
#check rightSeedPhaseTransfer_spectrum
#check canonical_right_next_seed_exact
#check canonical_right_next_seed_eq_iff_phase_eq
#print axioms canonical_right_digit_cut_phase
#print axioms canonical_right_next_seed_exact
#print axioms canonical_right_next_seed_eq_iff_phase_eq

end GSTGraphV2CanonicalPhaseSteering