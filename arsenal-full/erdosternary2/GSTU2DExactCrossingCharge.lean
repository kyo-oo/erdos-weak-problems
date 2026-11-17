import GSTU2DEventTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTU2DExactCrossingCharge

open GST2DMixedEmergence
open GSTU2DEventTransport

/-- Optimized horizontal information potential.  The three physical ternary
information states receive exact integer charges selected by the finite x4
transition system. -/
def digitPotential (d : Nat) : Int :=
  if d = 0 then 19 else if d = 1 then 56 else 21

/-- Optimized vertical carry potential. -/
def carryPotentialX (C : Nat) : Int :=
  if C = 1 then -19 else if C = 2 then -56 else 0

/-- Exact mixed crossing charge.  The coefficients `4` and `3` are the actual
horizontal and vertical GST scale factors, so this density telescopes in both
directions without a terminal-height or support-horizon premise. -/
def crossDensity (C d : Nat) : Int :=
  digitPotential (outDigit C d) - 4 * digitPotential d +
    carryPotentialX C - 3 * carryPotentialX (nextCarry C d) +
    84 * surviveI C d

/-- Complete twelve-cell certificate.  Both physical Happy realizations have
exact charge `105`; every non-Happy physical cell is non-positive. -/
theorem crossDensity_physical_table :
    crossDensity 0 0 = -57 ∧ crossDensity 0 1 = -111 ∧
    crossDensity 0 2 = 105 ∧
    crossDensity 1 0 = -39 ∧ crossDensity 1 1 = -81 ∧
    crossDensity 1 2 = -84 ∧
    crossDensity 2 0 = -111 ∧ crossDensity 2 1 = -93 ∧
    crossDensity 2 2 = 0 ∧
    crossDensity 3 0 = 0 ∧ crossDensity 3 1 = 0 ∧
    crossDensity 3 2 = 105 := by
  decide

/-- Every physical x4 cell has crossing charge at least `-111`. -/
theorem crossDensity_ge_neg111
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (-111 : Int) ≤ crossDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [crossDensity, digitPotential, carryPotentialX, outDigit,
      nextCarry, surviveI, midDigit, finalMicroDigit, microOutput,
      highBit, lowBit, twoI]

/-- A physical Happy cell is exactly a `+105` crossing-charge source. -/
theorem crossDensity_happy_exact
    (C d : Nat) (h : HappyCell C d) :
    crossDensity C d = 105 := by
  rcases h with ⟨rfl, h0 | h3⟩
  · subst C
    norm_num [crossDensity, digitPotential, carryPotentialX, outDigit,
      nextCarry, surviveI, midDigit, finalMicroDigit, microOutput,
      highBit, lowBit, twoI]
  · subst C
    norm_num [crossDensity, digitPotential, carryPotentialX, outDigit,
      nextCarry, surviveI, midDigit, finalMicroDigit, microOutput,
      highBit, lowBit, twoI]

/-- Every non-Happy physical cell has non-positive crossing charge. -/
theorem crossDensity_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    crossDensity C d ≤ 0 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    simp [HappyCell] at hbad <;>
    norm_num [crossDensity, digitPotential, carryPotentialX, outDigit,
      nextCarry, surviveI, midDigit, finalMicroDigit, microOutput,
      highBit, lowBit, twoI]

/-- Reverse-base-four accumulation of the exact crossing charge. -/
def reverseCrossCode (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 4 * reverseCrossCode C d N + crossDensity (C N) (d N)

/-- Matching reverse-base-four accumulation of vertical carry potential. -/
def reverseCarryCode (C : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 4 * reverseCarryCode C N + carryPotentialX (C N)

/-- Matching reverse-base-four microscopic SURVIVE incidence. -/
def reverseSurviveCode (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 4 * reverseSurviveCode C d N + surviveI (C N) (d N)

/-- **Exact horizontal crossing telescope.** -/
theorem reverseCrossCode_exact
    (C Cnext d : Nat → Nat) : ∀ N : Nat,
    (∀ t, t < N → outDigit (C t) (d t) = d (t+1)) →
    (∀ t, t < N → nextCarry (C t) (d t) = Cnext t) →
    reverseCrossCode C d N =
      digitPotential (d N) - ((4^N : Nat) : Int) * digitPotential (d 0) +
      reverseCarryCode C N - 3 * reverseCarryCode Cnext N +
      84 * reverseSurviveCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hout hnext
      simp [reverseCrossCode, reverseCarryCode, reverseSurviveCode]
  | succ N ih =>
      intro hout hnext
      have ih' := ih
        (fun t ht => hout t (by omega))
        (fun t ht => hnext t (by omega))
      have houtN := hout N (by omega)
      have hnextN := hnext N (by omega)
      rw [reverseCrossCode, reverseCarryCode, reverseCarryCode,
        reverseSurviveCode, ih', crossDensity, houtN, hnextN]
      rw [Nat.pow_succ]
      push_cast
      ring

/-- **All-width horizontal no-erasure.** -/
theorem reverseCrossCode_ge_105_of_leading_happy
    (C d : Nat → Nat)
    (hfirst : HappyCell (C 0) (d 0)) :
    ∀ N : Nat,
      1 ≤ N →
      (∀ t, t < N → C t < 4) →
      (∀ t, t < N → d t < 3) →
      105 ≤ reverseCrossCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hC hd
      by_cases hN0 : N = 0
      · subst N
        rw [reverseCrossCode]
        simp only [reverseCrossCode]
        rw [crossDensity_happy_exact (C 0) (d 0) hfirst]
        norm_num
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have ih' : 105 ≤ reverseCrossCode C d N :=
          ih hNpos
            (fun t ht => hC t (by omega))
            (fun t ht => hd t (by omega))
        have hlast : (-111 : Int) ≤ crossDensity (C N) (d N) :=
          crossDensity_ge_neg111 (C N) (d N)
            (hC N (by omega)) (hd N (by omega))
        rw [reverseCrossCode]
        omega

/-- Exact exponential form of the no-erasure pressure.  The minimum recurrence
is `x ↦ 4x-111`, started at `105`, hence the closed lower envelope is
`17·4^N+37`. -/
theorem reverseCrossCode_ge_exponential_of_leading_happy
    (C d : Nat → Nat)
    (hfirst : HappyCell (C 0) (d 0)) :
    ∀ N : Nat,
      1 ≤ N →
      (∀ t, t < N → C t < 4) →
      (∀ t, t < N → d t < 3) →
      17 * (((4^N : Nat) : Int)) + 37 ≤ reverseCrossCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hC hd
      by_cases hN0 : N = 0
      · subst N
        rw [reverseCrossCode]
        simp only [reverseCrossCode]
        rw [crossDensity_happy_exact (C 0) (d 0) hfirst]
        norm_num
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have ih' :
            17 * (((4^N : Nat) : Int)) + 37 ≤ reverseCrossCode C d N :=
          ih hNpos
            (fun t ht => hC t (by omega))
            (fun t ht => hd t (by omega))
        have hlast : (-111 : Int) ≤ crossDensity (C N) (d N) :=
          crossDensity_ge_neg111 (C N) (d N)
            (hC N (by omega)) (hd N (by omega))
        rw [reverseCrossCode]
        have hpowCast :
            (((4^(N+1) : Nat) : Int)) =
              4 * (((4^N : Nat) : Int)) := by
          rw [Nat.pow_succ]
          push_cast
          ring
        change
          17 * (((4^(N+1) : Nat) : Int)) + 37 ≤
            4 * reverseCrossCode C d N + crossDensity (C N) (d N)
        rw [hpowCast]
        omega

/-- Base-three weighted vertical derivative telescope. -/
theorem ternaryWeightedDiff_telescope (g : Nat → Int) (K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * (g p - 3 * g (p+1))) =
      g 0 - (((3^K : Nat) : Int)) * g K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Nat.pow_succ]
      push_cast
      ring

/-- **Exact base-4 × base-3 crossing rectangle.**
Every interior carry derivative cancels.  The upper boundary remains live and
explicit; no finite-support, terminal-space, or wave-termination premise is
used. -/
theorem reverseCrossRectangle_exact
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        reverseCrossCode (fun t => C t p) (fun t => d t p) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential (d N p) -
            (((4^N : Nat) : Int)) * digitPotential (d 0 p) +
            84 * reverseSurviveCode (fun t => C t p) (fun t => d t p) N)) +
      reverseCarryCode (fun t => C t 0) N -
        (((3^K : Nat) : Int)) * reverseCarryCode (fun t => C t K) N := by
  let g : Nat → Int := fun p => reverseCarryCode (fun t => C t p) N
  have htel := ternaryWeightedDiff_telescope g K
  calc
    Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          reverseCrossCode (fun t => C t p) (fun t => d t p) N) =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          ((digitPotential (d N p) -
              (((4^N : Nat) : Int)) * digitPotential (d 0 p) +
              84 * reverseSurviveCode (fun t => C t p) (fun t => d t p) N) +
            (g p - 3 * g (p+1)))) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpK : p < K := Finset.mem_range.mp hp
      have hrow := reverseCrossCode_exact
        (fun t => C t p) (fun t => C t (p+1)) (fun t => d t p) N
        (fun t ht => (hcell t p ht hpK).2.2.1)
        (fun t ht => (hcell t p ht hpK).2.2.2)
      dsimp [g]
      rw [hrow]
      push_cast
      ring
    _ =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential (d N p) -
            (((4^N : Nat) : Int)) * digitPotential (d 0 p) +
            84 * reverseSurviveCode (fun t => C t p) (fun t => d t p) N)) +
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) * (g p - 3 * g (p+1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          (digitPotential (d N p) -
            (((4^N : Nat) : Int)) * digitPotential (d 0 p) +
            84 * reverseSurviveCode (fun t => C t p) (fun t => d t p) N)) +
      g 0 - (((3^K : Nat) : Int)) * g K := by
        rw [htel]
        ring
    _ = _ := by rfl

/-- The optimized charge gives an exact strict sign separator for one physical
x4 event. -/
theorem happy_iff_crossDensity_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < crossDensity C d := by
  constructor
  · intro h
    rw [crossDensity_happy_exact C d h]
    norm_num
  · intro hpos
    by_contra hbad
    have hnonpos := crossDensity_nonpositive_of_not_happy C d hC hd hbad
    omega

#check crossDensity_physical_table
#check reverseCrossCode_exact
#check reverseCrossCode_ge_exponential_of_leading_happy
#check reverseCrossRectangle_exact
#check happy_iff_crossDensity_positive
#print axioms reverseCrossCode_exact
#print axioms reverseCrossCode_ge_exponential_of_leading_happy
#print axioms reverseCrossRectangle_exact
#print axioms happy_iff_crossDensity_positive

end GSTU2DExactCrossingCharge
