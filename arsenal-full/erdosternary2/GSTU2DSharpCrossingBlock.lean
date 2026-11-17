import GSTU2DExactCrossingCharge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTU2DExactCrossingCharge

open GST2DMixedEmergence
open GSTU2DEventTransport

/-- Terminal digit potential for the sharp horizontal crossing certificate.
The values are the exact finite-state Bellman certificate for the twelve
physical x4/base-3 cells. -/
def sharpTerminalPotential (d : Nat) : Int :=
  if d = 0 then 176 else if d = 1 then 185 else 149

/-- One physical x4 step preserves the sharp crossing certificate.  This is a
complete twelve-state check; unlike the coarse `-111` estimate it uses the
actual emitted ternary digit. -/
theorem sharpTerminalPotential_step
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    sharpTerminalPotential (outDigit C d) ≤
      4 * sharpTerminalPotential d + 5 * crossDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [sharpTerminalPotential, crossDensity, digitPotential,
      carryPotentialX, outDigit, nextCarry, surviveI, midDigit,
      finalMicroDigit, microOutput, highBit, lowBit, twoI]

/-- Sharp all-width no-erasure bound for a physical horizontal row beginning
at a Happy cell.  The old scalar envelope `17*4^N+37` forgets the emitted
ternary state.  Retaining that state gives the stronger exact certificate

  `94*4^N + P(d_N) ≤ 5*reverseCrossCode`,

with `P ∈ {149,176,185}` on physical digits. -/
theorem reverseCrossCode_ge_sharp_of_leading_happy
    (C d : Nat → Nat)
    (hfirst : HappyCell (C 0) (d 0)) :
    ∀ N : Nat,
      1 ≤ N →
      (∀ t, t < N → C t < 4) →
      (∀ t, t < N → d t < 3) →
      (∀ t, t < N → outDigit (C t) (d t) = d (t+1)) →
      94 * (((4^N : Nat) : Int)) + sharpTerminalPotential (d N) ≤
        5 * reverseCrossCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hC hd hout
      by_cases hN0 : N = 0
      · subst N
        have hpres :=
          happyCell_positive_and_preserves_big2 (C 0) (d 0) hfirst
        have hout0 := hout 0 (by omega)
        have hd1 : d 1 = 2 := by
          calc
            d 1 = outDigit (C 0) (d 0) := by simpa using hout0.symm
            _ = 2 := hpres.2
        rw [reverseCrossCode]
        simp only [reverseCrossCode]
        rw [crossDensity_happy_exact (C 0) (d 0) hfirst, hd1]
        norm_num [sharpTerminalPotential]
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have ih' :
            94 * (((4^N : Nat) : Int)) + sharpTerminalPotential (d N) ≤
              5 * reverseCrossCode C d N :=
          ih hNpos
            (fun t ht => hC t (by omega))
            (fun t ht => hd t (by omega))
            (fun t ht => hout t (by omega))
        have hlocal := sharpTerminalPotential_step
          (C N) (d N) (hC N (by omega)) (hd N (by omega))
        have houtN := hout N (by omega)
        have hpowCast :
            (((4^(N+1) : Nat) : Int)) =
              4 * (((4^N : Nat) : Int)) := by
          rw [Nat.pow_succ]
          push_cast
          ring
        rw [reverseCrossCode]
        change
          94 * (((4^(N+1) : Nat) : Int)) +
              sharpTerminalPotential (d (N+1)) ≤
            5 * (4 * reverseCrossCode C d N + crossDensity (C N) (d N))
        rw [hpowCast, ← houtN]
        omega

/-- Exact global floor for any physical horizontal crossing row.  The bound is
sharp for the unrestricted twelve-state recurrence and is the quantity that
must be paid by all rows below a highest Happy row. -/
theorem reverseCrossCode_ge_global_floor
    (C d : Nat → Nat) : ∀ N : Nat,
      (∀ t, t < N → C t < 4) →
      (∀ t, t < N → d t < 3) →
      37 - 37 * (((4^N : Nat) : Int)) ≤ reverseCrossCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hC hd
      simp [reverseCrossCode]
  | succ N ih =>
      intro hC hd
      have ih' := ih
        (fun t ht => hC t (by omega))
        (fun t ht => hd t (by omega))
      have hlast : (-111 : Int) ≤ crossDensity (C N) (d N) :=
        crossDensity_ge_neg111 (C N) (d N)
          (hC N (by omega)) (hd N (by omega))
      have hpowCast :
          (((4^(N+1) : Nat) : Int)) =
            4 * (((4^N : Nat) : Int)) := by
        rw [Nat.pow_succ]
        push_cast
        ring
      rw [reverseCrossCode, hpowCast]
      omega

/-- The sharp terminal potential has a uniform positive floor. -/
theorem sharpTerminalPotential_ge_149 (d : Nat) :
    (149 : Int) ≤ sharpTerminalPotential d := by
  by_cases h0 : d = 0
  · subst d
    norm_num [sharpTerminalPotential]
  · by_cases h1 : d = 1
    · subst d
      norm_num [sharpTerminalPotential]
    · simp [sharpTerminalPotential, h0, h1]

/-- State-free corollary of the sharp row theorem, retaining the improved
`94/5` asymptotic coefficient. -/
theorem reverseCrossCode_ge_sharp149_of_leading_happy
    (C d : Nat → Nat)
    (hfirst : HappyCell (C 0) (d 0))
    (N : Nat) (hN : 1 ≤ N)
    (hC : ∀ t, t < N → C t < 4)
    (hd : ∀ t, t < N → d t < 3)
    (hout : ∀ t, t < N → outDigit (C t) (d t) = d (t+1)) :
    94 * (((4^N : Nat) : Int)) + 149 ≤
      5 * reverseCrossCode C d N := by
  have hsharp := reverseCrossCode_ge_sharp_of_leading_happy C d hfirst
    N hN hC hd hout
  have hfloor := sharpTerminalPotential_ge_149 (d N)
  omega

/-- Base-three weighted prefix of horizontal crossing rows.  Recursion is used
here so the highest-row domination argument is a literal one-step statement. -/
def weightedCrossPrefix
    (C d : Nat → Nat → Nat) (N : Nat) : Nat → Int
  | 0 => 0
  | K+1 =>
      weightedCrossPrefix C d N K +
        (((3^K : Nat) : Int)) *
          reverseCrossCode (fun t => C t K) (fun t => d t K) N

/-- All rows in a physical prefix obey the exact geometric worst-case floor. -/
theorem weightedCrossPrefix_ge_global_floor
    (C d : Nat → Nat → Nat) (N : Nat) : ∀ K : Nat,
    (∀ t p, t < N → p < K → C t p < 4) →
    (∀ t p, t < N → p < K → d t p < 3) →
    (37 - 37 * (((4^N : Nat) : Int))) *
        ((((3^K : Nat) : Int)) - 1) ≤
      2 * weightedCrossPrefix C d N K := by
  intro K
  induction K with
  | zero =>
      intro hC hd
      simp [weightedCrossPrefix]
  | succ K ih =>
      intro hC hd
      have ih' := ih
        (fun t p ht hp => hC t p ht (by omega))
        (fun t p ht hp => hd t p ht (by omega))
      have hrow := reverseCrossCode_ge_global_floor
        (fun t => C t K) (fun t => d t K) N
        (fun t ht => hC t K ht (by omega))
        (fun t ht => hd t K ht (by omega))
      have hw : (0 : Int) ≤ 2 * (((3^K : Nat) : Int)) := by positivity
      have hrowW := mul_le_mul_of_nonneg_left hrow hw
      have h3pow :
          (((3^(K+1) : Nat) : Int)) =
            3 * (((3^K : Nat) : Int)) := by
        rw [Nat.pow_succ]
        push_cast
        ring
      rw [weightedCrossPrefix, h3pow]
      calc
        (37 - 37 * (((4^N : Nat) : Int))) *
            (3 * (((3^K : Nat) : Int)) - 1) =
          (37 - 37 * (((4^N : Nat) : Int))) *
              ((((3^K : Nat) : Int)) - 1) +
            (2 * (((3^K : Nat) : Int))) *
              (37 - 37 * (((4^N : Nat) : Int))) := by ring
        _ ≤ 2 * weightedCrossPrefix C d N K +
            (2 * (((3^K : Nat) : Int))) *
              reverseCrossCode (fun t => C t K) (fun t => d t K) N :=
          add_le_add ih' hrowW
        _ = 2 *
            (weightedCrossPrefix C d N K +
              (((3^K : Nat) : Int)) *
                reverseCrossCode (fun t => C t K) (fun t => d t K) N) := by
          ring

/-- **Highest-Happy-row domination.**  If row `q` begins Happy, its exact
state-aware crossing pressure beats the total worst-case crossing mass of all
rows strictly below it under the canonical base-three vertical weighting.
This is the finite block theorem: no support horizon, terminal state, or
residual-infinite argument occurs. -/
theorem weightedCrossPrefix_positive_of_top_leading_happy
    (C d : Nat → Nat → Nat) (N q : Nat)
    (hN : 1 ≤ N)
    (hC : ∀ t p, t < N → p ≤ q → C t p < 4)
    (hd : ∀ t p, t < N → p ≤ q → d t p < 3)
    (hout : ∀ t p, t < N → p ≤ q →
      outDigit (C t p) (d t p) = d (t+1) p)
    (hHappy : HappyCell (C 0 q) (d 0 q)) :
    0 < weightedCrossPrefix C d N (q+1) := by
  let A : Int := (((4^N : Nat) : Int))
  let w : Int := (((3^q : Nat) : Int))
  let P : Int := weightedCrossPrefix C d N q
  let R : Int := reverseCrossCode (fun t => C t q) (fun t => d t q) N

  have hlower0 := weightedCrossPrefix_ge_global_floor C d N q
    (fun t p ht hp => hC t p ht (by omega))
    (fun t p ht hp => hd t p ht (by omega))
  have hlower : (37 - 37*A) * (w - 1) ≤ 2*P := by
    simpa [A, w, P] using hlower0

  have htop0 := reverseCrossCode_ge_sharp149_of_leading_happy
    (fun t => C t q) (fun t => d t q) hHappy N hN
    (fun t ht => hC t q ht (by omega))
    (fun t ht => hd t q ht (by omega))
    (fun t ht => hout t q ht (by omega))
  have htop : 94*A + 149 ≤ 5*R := by
    simpa [A, R] using htop0

  have hw0 : (0 : Int) ≤ 2*w := by
    dsimp [w]
    positivity
  have htopW := mul_le_mul_of_nonneg_left htop hw0
  have hlower5 := mul_le_mul_of_nonneg_left hlower (by norm_num : (0:Int) ≤ 5)

  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hwpos : 0 < w := by
    dsimp [w]
    positivity
  have hAwpos : 0 < A*w := mul_pos hApos hwpos

  have hpositive :
      0 < 5 * ((37 - 37*A) * (w - 1)) +
        (2*w) * (94*A + 149) := by
    have hshape :
        5 * ((37 - 37*A) * (w - 1)) +
            (2*w) * (94*A + 149) =
          3*A*w + 185*A + 483*w - 185 := by ring
    rw [hshape]
    nlinarith [hApos, hwpos, hAwpos]

  have hbound :
      5 * ((37 - 37*A) * (w - 1)) +
          (2*w) * (94*A + 149) ≤
        10 * (P + w*R) := by
    calc
      5 * ((37 - 37*A) * (w - 1)) +
          (2*w) * (94*A + 149) ≤
        5 * (2*P) + (2*w) * (5*R) := add_le_add hlower5 htopW
      _ = 10 * (P + w*R) := by ring

  have hsumpos : 0 < P + w*R := by omega
  simpa [weightedCrossPrefix, P, R, w] using hsumpos

#check sharpTerminalPotential_step
#check reverseCrossCode_ge_sharp_of_leading_happy
#check reverseCrossCode_ge_global_floor
#check weightedCrossPrefix_ge_global_floor
#check weightedCrossPrefix_positive_of_top_leading_happy
#print axioms sharpTerminalPotential_step
#print axioms reverseCrossCode_ge_sharp_of_leading_happy
#print axioms reverseCrossCode_ge_global_floor
#print axioms weightedCrossPrefix_ge_global_floor
#print axioms weightedCrossPrefix_positive_of_top_leading_happy

end GSTU2DExactCrossingCharge
