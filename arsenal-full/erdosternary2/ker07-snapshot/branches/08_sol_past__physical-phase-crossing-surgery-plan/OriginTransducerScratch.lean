/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0123 / 1132
/-    Path         : branches/sol_physical-phase-crossing-surgery-plan/OriginTransducerScratch.lean
/-    Ref          : origin/sol/physical-phase-crossing-surgery-plan
/-    First-commit : 2026-08-15 07:49:05 +0530  (77d6713)
/-    Last-commit  : 2026-08-15 09:42:25 +0530  (44a7de9)
/-    Total commits: 4
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/4] 2026-08-15 07:49:05 +0530  77d6713  (ker07-dev)
/-        test: kernel-check natural-origin information transducer
/- [02/4] 2026-08-15 07:54:27 +0530  13b1b84  (ker07-dev)
/-        fix: preserve natural-origin lets during descent
/- [03/4] 2026-08-15 09:31:14 +0530  4507a6c  (ker07-dev)
/-        Formalize canonical three-phase GST orbit algebra
/- [04/4] 2026-08-15 09:42:25 +0530  44a7de9  (ker07-dev)
/-        Fix canonical phase-wrap algebra
/- ====================================================================== -/

import Mathlib

/-!
Temporary kernel scratch for the canonical natural-origin information step.
No Erdős theorem and no extra axiom: all canonical decomposition data enters
as explicit theorem hypotheses.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Cancellation algebra used by the Navigation Constant recurrence. -/
theorem origin_navigation_algebraS
    (D A c0 Q Qnext K : Nat) (hD : 0 < D)
    (hA : A = 1 + D*c0)
    (hQ : 1 + D*Q = A * (1 + D*K*Qnext)) :
    Q = c0 + K*A*Qnext := by
  have hfactor : A * (1 + D*K*Qnext) =
      1 + D * (c0 + K*A*Qnext) := by
    rw [hA]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
    ac_rfl
  rw [hfactor] at hQ
  have hadd := Nat.add_left_cancel hQ
  exact Nat.mul_left_cancel hD hadd

/-- If Q has the exact perfect-power decomposition at t and t+1, splitting an
    origin parameter as 3*u+d gives the exact digit recurrence
      Q_t(3u+d) = Q_t(d) + 3*A_t^d*Q_{t+1}(u). -/
theorem origin_digit_recurrenceS
    (Q : Nat → Nat → Nat) (t u d A D : Nat)
    (hD : 0 < D)
    (hAd : A^d = 1 + D * Q t d)
    (hcur : 1 + D * Q t (3*u+d) =
      A^d * (1 + D * 3 * Q (t+1) u)) :
    Q t (3*u+d) = Q t d + 3 * A^d * Q (t+1) u := by
  exact origin_navigation_algebraS D (A^d) (Q t d)
    (Q t (3*u+d)) (Q (t+1) u) 3 hD hAd hcur

/-- Exact affine information step.  The emitted ternary digit is E mod 3;
    everything not emitted is retained in the updated offset and multiplier. -/
theorem affine_origin_stepS
    (Q : Nat → Nat → Nat) (t u d z m A : Nat)
    (hrec : Q t (3*u+d) = Q t d + 3 * A^d * Q (t+1) u) :
    let E := z + m * Q t d
    let r := E % 3
    let z' := E / 3
    let m' := m * A^d
    z + m * Q t (3*u+d) =
      r + 3 * (z' + m' * Q (t+1) u) := by
  dsimp only
  rw [hrec]
  have hE : z + m * Q t d =
      (z + m * Q t d) % 3 + 3 * ((z + m * Q t d) / 3) := by
    have h := Nat.mod_add_div (z + m * Q t d) 3
    omega
  rw [Nat.mul_add]
  rw [show m * (3 * A^d * Q (t+1) u) =
      3 * (m * A^d * Q (t+1) u) by ac_rfl]
  omega

/-- Natural-origin specialization: consume exactly the least ternary trit and
    replace the origin by n/3.  This is the formal regeneration/descent step. -/
theorem affine_natural_origin_stepS
    (Q : Nat → Nat → Nat) (t n z m A : Nat)
    (hrec : Q t (3*(n/3) + n%3) =
      Q t (n%3) + 3 * A^(n%3) * Q (t+1) (n/3)) :
    let E := z + m * Q t (n%3)
    let r := E % 3
    let z' := E / 3
    let m' := m * A^(n%3)
    z + m * Q t n =
      r + 3 * (z' + m' * Q (t+1) (n/3)) := by
  dsimp only
  have hn : n = 3*(n/3) + n%3 := by
    have h := Nat.mod_add_div n 3
    omega
  have hstep := affine_origin_stepS Q t (n/3) (n%3) z m A hrec
  dsimp only at hstep
  calc
    z + m * Q t n = z + m * Q t (3*(n/3) + n%3) := by rw [← hn]
    _ = (z + m * Q t (n%3)) % 3 +
        3 * ((z + m * Q t (n%3)) / 3 +
          m * A^(n%3) * Q (t+1) (n/3)) := hstep

/-- Positive origins strictly descend when one ternary trit is consumed. -/
theorem natural_origin_div3_strictS (n : Nat) (hn : 0 < n) :
    n / 3 < n := by
  exact Nat.div_lt_self hn (by decide : 1 < 3)

/-!
Canonical three-phase GST orbit algebra.

These lemmas deliberately do not assert a gate theorem.  They only prove that
phase zero, phase one, and phase two are exact cross-sections of one power
orbit when A = 1 + D*c and c = 1 + 3*z.
-/

/-- From the phase-zero identity A^(3n)=1+3DT, one multiplication by A gives
    the exact phase-one identity with tail X=z+A*T. -/
theorem gst_phase_one_exactS
    (A D c z T n : Nat)
    (hA : A = 1 + D*c)
    (hc : c = 1 + 3*z)
    (h0 : A^(3*n) = 1 + 3*D*T) :
    A^(3*n + 1) = 1 + D + 3*D*(z + A*T) := by
  rw [Nat.pow_succ, h0, hA, hc]
  ring

/-- If D=3N, the next multiplication gives the exact phase-two tail
    z + N*c + A*H1. -/
theorem gst_phase_two_exactS
    (A D N c z H1 n : Nat)
    (hDN : D = 3*N)
    (hA : A = 1 + D*c)
    (hc : c = 1 + 3*z)
    (h1 : A^(3*n + 1) = 1 + D + 3*D*H1) :
    A^(3*n + 2) = 1 + 2*D + 3*D*(z + N*c + A*H1) := by
  have hexp : 3*n + 2 = (3*n + 1) + 1 := by omega
  rw [hexp, Nat.pow_succ, h1, hA, hc, hDN]
  ring

/-- The phase-two cross-section wraps to phase zero after one more A-step.
    `W` is the exact next zero-phase offset, characterized by c+2A=3W. -/
theorem gst_phase_wrap_exactS
    (A D c H2 W n : Nat)
    (hA : A = 1 + D*c)
    (hW : c + 2*A = 3*W)
    (h2 : A^(3*n + 2) = 1 + 2*D + 3*D*H2) :
    A^(3*(n+1)) = 1 + 3*D*(W + A*H2) := by
  have hexp : 3*(n+1) = (3*n + 2) + 1 := by omega
  have hW' : c + 2*(1 + D*c) = 3*W := by
    simpa [hA] using hW
  rw [hexp, Nat.pow_succ, h2, hA]
  have hshape :
      (1 + 2*D + 3*D*H2) * (1 + D*c) =
        1 + D*(c + 2*(1 + D*c)) +
          3*D*((1 + D*c)*H2) := by
    ring
  rw [hshape, hW']
  ring

/-- The three canonical low prefixes occupy disjoint carry bands when D≥9.
    These inequalities are the arithmetic content of the phase seeds 0,1,2. -/
theorem gst_phase_low_prefix_bandsS
    (D : Nat) (hD : 9 ≤ D) :
    4 < 3*D ∧
    (3*D ≤ 4*(1+D) ∧ 4*(1+D) < 6*D) ∧
    (6*D ≤ 4*(1+2*D) ∧ 4*(1+2*D) < 9*D) := by
  omega
