import GSTGraphV2InfiniteControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTU2DCanonicalPhaseDensity

open GST2DMixedEmergence
open GSTU2DEventTransport

/-- Minimal ternary information potential. On physical digits it is exactly d-1. -/
def phaseDigitPotential (d : Nat) : Int :=
  (d : Int) - 1

/-- Monotone carry potential selected by the exact twelve-state x4/base3 table. -/
def phaseCarryPotential (C : Nat) : Int :=
  if C = 0 then 2 else if C = 1 then 1 else 0

/-- Canonical phase density. Its divergence coefficients are the literal GST
horizontal factor 1 and vertical factor 3. -/
def phaseDensity (C d : Nat) : Int :=
  phaseDigitPotential (outDigit C d) - phaseDigitPotential d +
    phaseCarryPotential C - 3 * phaseCarryPotential (nextCarry C d) +
    surviveI C d

/-- Exact twelve-state table. Both Happy cells are +2; all ten bad cells are
nonpositive, with global floor -4. -/
theorem phaseDensity_physical_table :
    phaseDensity 0 0 = -4 ∧ phaseDensity 0 1 = -1 ∧
    phaseDensity 0 2 = 2 ∧
    phaseDensity 1 0 = -4 ∧ phaseDensity 1 1 = 0 ∧
    phaseDensity 1 2 = -1 ∧
    phaseDensity 2 0 = -4 ∧ phaseDensity 2 1 = -1 ∧
    phaseDensity 2 2 = 0 ∧
    phaseDensity 3 0 = -3 ∧ phaseDensity 3 1 = 0 ∧
    phaseDensity 3 2 = 2 := by
  decide

/-- Happy is exactly the positive sector of the new density. -/
theorem happy_iff_phaseDensity_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < phaseDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [HappyCell, phaseDensity, phaseDigitPotential,
      phaseCarryPotential, outDigit, nextCarry, surviveI,
      midDigit, finalMicroDigit, microOutput, highBit, lowBit, twoI]

/-- Uniform physical floor used by highest-row domination. -/
theorem phaseDensity_ge_neg_four
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (-4 : Int) ≤ phaseDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    decide

/-- Non-Happy is exactly nonpositive on physical cells. -/
theorem phaseDensity_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    phaseDensity C d ≤ 0 := by
  have hiff := happy_iff_phaseDensity_positive C d hC hd
  by_contra hnot
  have hpos : 0 < phaseDensity C d := by omega
  exact hbad (hiff.mpr hpos)

/-- Base-three weighted prefix of one vertical graph column. -/
def weightedPhaseColumnPrefix
    (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | K+1 => weightedPhaseColumnPrefix C d K +
      (((3^K : Nat) : Int)) * phaseDensity (C K) (d K)

/-- Exact accumulated floor. -4 at each row sums to -2*(3^K-1). -/
theorem weightedPhaseColumnPrefix_ge_floor
    (C d : Nat → Nat) (K : Nat)
    (hC : ∀ p, p < K → C p < 4)
    (hd : ∀ p, p < K → d p < 3) :
    (-2 : Int) * ((((3^K : Nat) : Int)) - 1) ≤
      weightedPhaseColumnPrefix C d K := by
  induction K with
  | zero => simp [weightedPhaseColumnPrefix]
  | succ K ih =>
      have ih' := ih
        (fun p hp => hC p (by omega))
        (fun p hp => hd p (by omega))
      have hfloor := phaseDensity_ge_neg_four (C K) (d K)
        (hC K (by omega)) (hd K (by omega))
      have hw : (0 : Int) ≤ (((3^K : Nat) : Int)) := by positivity
      have hwfloor := mul_le_mul_of_nonneg_left hfloor hw
      have hpow :
          (((3^(K+1) : Nat) : Int)) = 3 * (((3^K : Nat) : Int)) := by
        rw [Nat.pow_succ]
        push_cast
        ring
      rw [weightedPhaseColumnPrefix, hpow]
      calc
        (-2 : Int) * (3 * (((3^K : Nat) : Int)) - 1) =
            (-2 : Int) * ((((3^K : Nat) : Int)) - 1) +
              (((3^K : Nat) : Int)) * (-4) := by ring
        _ ≤ weightedPhaseColumnPrefix C d K +
              (((3^K : Nat) : Int)) * phaseDensity (C K) (d K) :=
          add_le_add ih' (by simpa [mul_comm] using hwfloor)

/-- Sharp one-column domination: a top Happy row contributes +2*3^q, which
beats the exact -4 floor of all lower rows by a residual +2. -/
theorem weightedPhaseColumnPrefix_positive_of_top_happy
    (C d : Nat → Nat) (q : Nat)
    (hC : ∀ p, p ≤ q → C p < 4)
    (hd : ∀ p, p ≤ q → d p < 3)
    (hHappy : HappyCell (C q) (d q)) :
    0 < weightedPhaseColumnPrefix C d (q+1) := by
  have htop : phaseDensity (C q) (d q) = 2 := by
    change d q = 2 ∧ (C q = 0 ∨ C q = 3) at hHappy
    rcases hHappy with ⟨hd2, h0 | h3⟩
    · rw [hd2, h0]
      decide
    · rw [hd2, h3]
      decide
  have hlower := weightedPhaseColumnPrefix_ge_floor C d q
    (fun p hp => hC p (by omega))
    (fun p hp => hd p (by omega))
  rw [weightedPhaseColumnPrefix, htop]
  have hpowpos : 0 < (((3^q : Nat) : Int)) := by positivity
  nlinarith

/-- Horizontal digit potential telescopes because the coefficient is exactly one. -/
theorem horizontal_phase_digit_telescope
    (d : Nat → Nat) (N : Nat) :
    Finset.sum (Finset.range N) (fun t =>
      phaseDigitPotential (d (t+1)) - phaseDigitPotential (d t)) =
      phaseDigitPotential (d N) - phaseDigitPotential (d 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Vertical base-three carry potential telescopes exactly. -/
theorem vertical_phase_carry_telescope
    (C : Nat → Nat) (K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        (phaseCarryPotential (C p) - 3 * phaseCarryPotential (C (p+1)))) =
      phaseCarryPotential (C 0) -
        (((3^K : Nat) : Int)) * phaseCarryPotential (C K) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Nat.pow_succ]
      push_cast
      ring

/-- One vertical row-sum identity, keeping the horizontal digit difference
explicit and telescoping only the ternary carry potential. -/
theorem phaseColumn_exact
    (C d dNext : Nat → Nat) (K : Nat)
    (hcell : ∀ p, p < K →
      C p < 4 ∧ d p < 3 ∧
      outDigit (C p) (d p) = dNext p ∧
      nextCarry (C p) (d p) = C (p+1)) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * phaseDensity (C p) (d p)) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (phaseDigitPotential (dNext p) - phaseDigitPotential (d p))) +
      phaseCarryPotential (C 0) -
        (((3^K : Nat) : Int)) * phaseCarryPotential (C K) +
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * surviveI (C p) (d p)) := by
  have hlocal :
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * phaseDensity (C p) (d p)) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (phaseDigitPotential (dNext p) - phaseDigitPotential (d p))) +
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (phaseCarryPotential (C p) - 3 * phaseCarryPotential (C (p+1)))) +
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * surviveI (C p) (d p)) := by
    calc
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * phaseDensity (C p) (d p)) =
        Finset.sum (Finset.range K) (fun p =>
          (((3^p : Nat) : Int)) *
            ((phaseDigitPotential (dNext p) - phaseDigitPotential (d p)) +
             (phaseCarryPotential (C p) - 3 * phaseCarryPotential (C (p+1))) +
             surviveI (C p) (d p))) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hc := hcell p (Finset.mem_range.mp hp)
          rw [phaseDensity, hc.2.2.1, hc.2.2.2]
          ring
      _ = _ := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hcarry := vertical_phase_carry_telescope C K
  rw [hlocal, hcarry]
  ring

/-- Exact 2D rectangle identity for the new phase density. The only interior
term is the nonnegative microscopic SURVIVE incidence. -/
theorem phaseRectangle_exact
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range N) (fun t =>
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * phaseDensity (C t p) (d t p))) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (phaseDigitPotential (d N p) - phaseDigitPotential (d 0 p))) +
      Finset.sum (Finset.range N) (fun t => phaseCarryPotential (C t 0)) -
        (((3^K : Nat) : Int)) *
          Finset.sum (Finset.range N) (fun t => phaseCarryPotential (C t K)) +
      Finset.sum (Finset.range N) (fun t =>
        Finset.sum (Finset.range K) (fun p =>
          (((3^p : Nat) : Int)) * surviveI (C t p) (d t p))) := by
  let Dsum : Nat → Int := fun t =>
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        (phaseDigitPotential (d (t+1) p) - phaseDigitPotential (d t p)))
  let Btm : Nat → Int := fun t => phaseCarryPotential (C t 0)
  let Top : Nat → Int := fun t =>
    (((3^K : Nat) : Int)) * phaseCarryPotential (C t K)
  let Srv : Nat → Int := fun t =>
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * surviveI (C t p) (d t p))

  have hrows :
      Finset.sum (Finset.range N) (fun t =>
        Finset.sum (Finset.range K) (fun p =>
          (((3^p : Nat) : Int)) * phaseDensity (C t p) (d t p))) =
      Finset.sum (Finset.range N) (fun t => Dsum t + Btm t - Top t + Srv t) := by
    apply Finset.sum_congr rfl
    intro t ht
    have hr := phaseColumn_exact
      (fun p => C t p) (fun p => d t p) (fun p => d (t+1) p) K
      (fun p hp => hcell t p (Finset.mem_range.mp ht) hp)
    simpa [Dsum, Btm, Top, Srv] using hr

  have hDigit :
      Finset.sum (Finset.range N) Dsum =
        Finset.sum (Finset.range K) (fun p =>
          (((3^p : Nat) : Int)) *
            (phaseDigitPotential (d N p) - phaseDigitPotential (d 0 p))) := by
    dsimp [Dsum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.mul_sum]
    rw [horizontal_phase_digit_telescope (fun t => d t p) N]

  have hTop :
      Finset.sum (Finset.range N) Top =
        (((3^K : Nat) : Int)) *
          Finset.sum (Finset.range N) (fun t => phaseCarryPotential (C t K)) := by
    dsimp [Top]
    rw [Finset.mul_sum]

  rw [hrows]
  have hsplit :
      Finset.sum (Finset.range N) (fun t => Dsum t + Btm t - Top t + Srv t) =
        Finset.sum (Finset.range N) Dsum +
        Finset.sum (Finset.range N) Btm -
        Finset.sum (Finset.range N) Top +
        Finset.sum (Finset.range N) Srv := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit, hDigit, hTop]

#check phaseDensity_physical_table
#check happy_iff_phaseDensity_positive
#check weightedPhaseColumnPrefix_ge_floor
#check weightedPhaseColumnPrefix_positive_of_top_happy
#check phaseRectangle_exact
#print axioms phaseDensity_physical_table
#print axioms weightedPhaseColumnPrefix_positive_of_top_happy
#print axioms phaseRectangle_exact

end GSTU2DCanonicalPhaseDensity
