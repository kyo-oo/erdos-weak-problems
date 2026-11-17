import GSTWorldtraceBlockLift
import GSTWorldtraceCoeffStability

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

/-!
# GST / Worldtrace quadratic whole-block lift

The first GST Worldtrace block law is linear only up to one scale-band:
w <= L+1. This file derives, from the same exact perfect-power law,
a SECOND-ORDER physical quotient identity controlling the next scale-band
too, i.e. any w <= 2*(L+1).

The quadratic coefficient is a recursively defined exact triangular
number, not rational arithmetic or a truncated asymptotic heuristic.
No hGate/axiom, no bounded exponent or multiplier, and no dropped carry.
-/

namespace GSTWorldtraceQuadraticBlockLift

open GSTWorldtraceBlockLift

/-- Integer binomial second coefficient, defined by its exact discrete
GST triangular recurrence. -/
def triangle : Nat → Nat
  | 0 => 0
  | n+1 => triangle n+n

theorem triangle_succ (n : Nat) :
    triangle (n+1) = triangle n+n := rfl

/-- All powers of the whole GST block have the exact linear first
remainder modulo the SQUARE of their source scale. -/
theorem power_linear_mod_square
    (T c n : Nat) :
    (1+T*c)^n % T^2 = (1+n*T*c)%T^2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (1+T*c)^(n+1)%T^2 =
          ((1+T*c)^n*(1+T*c))%T^2 := by rw [pow_succ]
        _ = (((1+T*c)^n%T^2)*((1+T*c)%T^2))%T^2 :=
          Nat.mul_mod _ _ _
        _ = (((1+n*T*c)%T^2)*((1+T*c)%T^2))%T^2 := by rw [ih]
        _ = ((1+n*T*c)*(1+T*c))%T^2 :=
          (Nat.mul_mod _ _ _).symm
        _ = (1+(n+1)*T*c)%T^2 := by
          have hshape :
              (1+n*T*c)*(1+T*c) =
                (1+(n+1)*T*c)+T^2*(n*c^2) := by ring
          rw [hshape, Nat.add_mul_mod_self_left]

/-- Exact second GST Worldtrace block law:
the quotient's first TWO full scale-bands are triangular/quadratic.
Holds for ALL T,A,c,b naturals (T>0 is the sole division condition).
This lifts the previous linear law by keeping the previously lost
quadratic transport term. -/
theorem quotient_quadratic_block_lift
    (A c b T : Nat) (hT : 0 < T) :
    (A*(1+T*c)^b/T)%T^2 =
      (A/T + b*c*A + triangle b*T*c^2*A)%T^2 := by
  induction b with
  | zero =>
      simp [triangle]
  | succ b ih =>
      let P := A*(1+T*c)^b
      have hshape :
          A*(1+T*c)^(b+1) = P*(1+T*c) := by
        simp only [P, pow_succ]
        ring
      have hquo : (P*(1+T*c))/T=P/T+c*P :=
        quotient_multiply_step P T c hT
      have hmul :
          (c*P)%T^2 = (c*A+b*T*c^2*A)%T^2 := by
        calc
          (c*P)%T^2 = ((c*A)*(1+T*c)^b)%T^2 := by
            dsimp [P]
            congr 1
            ring
          _ = (((c*A)%T^2)*(((1+T*c)^b)%T^2))%T^2 :=
            Nat.mul_mod _ _ _
          _ = (((c*A)%T^2)*((1+b*T*c)%T^2))%T^2 := by
            rw [power_linear_mod_square]
          _ = ((c*A)*(1+b*T*c))%T^2 :=
            (Nat.mul_mod _ _ _).symm
          _ = (c*A+b*T*c^2*A)%T^2 := by
            congr 1
            ring
      calc
        (A*(1+T*c)^(b+1)/T)%T^2 =
          (P/T+c*P)%T^2 := by rw [hshape,hquo]
        _ = (((P/T)%T^2)+((c*P)%T^2))%T^2 :=
          Nat.add_mod _ _ _
        _ =
            (((A/T+b*c*A+triangle b*T*c^2*A)%T^2)+
              ((c*A+b*T*c^2*A)%T^2))%T^2 := by
                rw [ih,hmul]
        _ =
            ((A/T+b*c*A+triangle b*T*c^2*A)+
              (c*A+b*T*c^2*A))%T^2 :=
          (Nat.add_mod _ _ _).symm
        _ = (A/T+(b+1)*c*A+triangle (b+1)*T*c^2*A)%T^2 := by
          rw [triangle_succ]
          congr 1
          ring

/-- New second-order source-specific GST tower theorem.
Unlike the first-order linear band, the window may extend through
TWO complete postcut scale-bands, w <= 2*(L+1).
All M, multipliers u and scales L are universally quantified.
-/
theorem pow4_quadratic_window_lift
    (M u L w : Nat) (hw : 1 ≤ w) (hband : w ≤ 2*(L+1)) :
    (4^(M+u*3^L)/3^(L+1))%3^w =
      (4^M/3^(L+1) +
         u*GSTCanonicalTailLTE.lteCoeff L*4^M +
         triangle u*3^(L+1)*(GSTCanonicalTailLTE.lteCoeff L)^2*4^M)%3^w := by
  have hdiv : 3^w ∣ (3^(L+1))^2 := by
    have h := Nat.pow_dvd_pow 3 (show w ≤ (L+1)*2 by omega)
    simpa only [pow_mul] using h
  have hpower :
      4^(M+u*3^L) =
        4^M*(1+3^(L+1)*GSTCanonicalTailLTE.lteCoeff L)^u := by
    rw [show M+u*3^L = M+3^L*u by ac_rfl, pow_add,
      pow_mul, GSTCanonicalTailLTE.pow4_three_power_lte_exact L]
  rw [hpower]
  calc
    (4^M*(1+3^(L+1)*GSTCanonicalTailLTE.lteCoeff L)^u/
         3^(L+1))%3^w =
      ((4^M*(1+3^(L+1)*GSTCanonicalTailLTE.lteCoeff L)^u/
         3^(L+1))%((3^(L+1))^2))%3^w :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
    _ =
      ((4^M/3^(L+1)+u*GSTCanonicalTailLTE.lteCoeff L*4^M+
        triangle u*3^(L+1)*(GSTCanonicalTailLTE.lteCoeff L)^2*4^M)%
          ((3^(L+1))^2))%3^w := by
          rw [quotient_quadratic_block_lift _ _ _ _ (by positivity)]
    _ =
      (4^M/3^(L+1)+u*GSTCanonicalTailLTE.lteCoeff L*4^M+
        triangle u*3^(L+1)*(GSTCanonicalTailLTE.lteCoeff L)^2*4^M)%3^w :=
      Nat.mod_mod_of_dvd _ hdiv

/-- The new quadratic GST law reduces exactly to the known linear
transport on its former first scale-band, by modular annihilation
of the quadratic term. -/
theorem quadratic_recovers_linear_first_band
    (M u L w : Nat) (hw : 1 ≤ w) (hband : w ≤ L+1) :
    (4^(M+u*3^L)/3^(L+1))%3^w =
      (4^M/3^(L+1) + u*GSTCanonicalTailLTE.lteCoeff L*4^M)%3^w := by
  exact GSTWorldtraceBlockLift.pow4_whole_block_lift
    M u L w hw hband

#print axioms power_linear_mod_square
#print axioms quotient_quadratic_block_lift
#print axioms pow4_quadratic_window_lift
#print axioms quadratic_recovers_linear_first_band

end GSTWorldtraceQuadraticBlockLift
