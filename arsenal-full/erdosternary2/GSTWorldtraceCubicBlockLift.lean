import GSTWorldtraceQuadraticBlockLift

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

/-!
# GST / Worldtrace cubic whole-block lift

Independent higher-order GST discovery. The first GST scale band was
linear (w <= L+1), and the second triangular (w <= 2*(L+1)).
This module retains the THIRD exact Worldtrace carry channel, extending
the exact physical quotient to w <= 3*(L+1) for ALL exponents.

The cubic coefficient tetra n is defined by the exact discrete-volume
recurrence, not by division or a formal asymptotic expansion.
-/

namespace GSTWorldtraceCubicBlockLift

open GSTWorldtraceBlockLift
open GSTWorldtraceQuadraticBlockLift

/-- Third discrete GST volume coefficient, C(n,3), recursion only. -/
def tetra : Nat → Nat
  | 0 => 0
  | n+1 => tetra n + triangle n

theorem tetra_succ (n : Nat) :
    tetra (n+1) = tetra n+triangle n := rfl

/-- Exact square-order power response through THREE complete scale bands. -/
theorem power_quadratic_mod_cube
    (T c n : Nat) :
    (1+T*c)^n % T^3 =
      (1+n*T*c+triangle n*T^2*c^2)%T^3 := by
  induction n with
  | zero =>
      simp [triangle]
  | succ n ih =>
      calc
        (1+T*c)^(n+1)%T^3 =
          ((1+T*c)^n*(1+T*c))%T^3 := by rw [pow_succ]
        _ = (((1+T*c)^n%T^3)*((1+T*c)%T^3))%T^3 :=
          Nat.mul_mod _ _ _
        _ =
          (((1+n*T*c+triangle n*T^2*c^2)%T^3)*
            ((1+T*c)%T^3))%T^3 := by rw [ih]
        _ = ((1+n*T*c+triangle n*T^2*c^2)*(1+T*c))%T^3 :=
          (Nat.mul_mod _ _ _).symm
        _ =
          (1+(n+1)*T*c+triangle (n+1)*T^2*c^2)%T^3 := by
          have hshape :
              (1+n*T*c+triangle n*T^2*c^2)*(1+T*c) =
                (1+(n+1)*T*c+triangle (n+1)*T^2*c^2)+
                  T^3*(triangle n*c^3) := by
                    rw [triangle_succ]
                    ring
          rw [hshape, Nat.add_mul_mod_self_left]

/-- Cubic GST quotient transport, exactly mod T^3, for ALL multipliers.
No hidden controller, no hGate, and all nonlinear carried terms retained. -/
theorem quotient_cubic_block_lift
    (A c b T : Nat) (hT : 0 < T) :
    (A*(1+T*c)^b/T)%T^3 =
      (A/T+b*c*A+triangle b*T*c^2*A+
        tetra b*T^2*c^3*A)%T^3 := by
  induction b with
  | zero =>
      simp [triangle, tetra]
  | succ b ih =>
      let P := A*(1+T*c)^b
      have hshape :
          A*(1+T*c)^(b+1) = P*(1+T*c) := by
        simp only [P, pow_succ]
        ring
      have hquo : (P*(1+T*c))/T=P/T+c*P :=
        quotient_multiply_step P T c hT
      have hmul :
          (c*P)%T^3 =
            (c*A+b*T*c^2*A+triangle b*T^2*c^3*A)%T^3 := by
        calc
          (c*P)%T^3 = ((c*A)*(1+T*c)^b)%T^3 := by
            dsimp [P]
            congr 1
            ring
          _ = (((c*A)%T^3)*(((1+T*c)^b)%T^3))%T^3 :=
            Nat.mul_mod _ _ _
          _ =
            (((c*A)%T^3)*
              ((1+b*T*c+triangle b*T^2*c^2)%T^3))%T^3 := by
              rw [power_quadratic_mod_cube]
          _ = ((c*A)*(1+b*T*c+triangle b*T^2*c^2))%T^3 :=
            (Nat.mul_mod _ _ _).symm
          _ = (c*A+b*T*c^2*A+triangle b*T^2*c^3*A)%T^3 := by
            congr 1
            ring
      calc
        (A*(1+T*c)^(b+1)/T)%T^3 =
          (P/T+c*P)%T^3 := by rw [hshape,hquo]
        _ = (((P/T)%T^3)+((c*P)%T^3))%T^3 :=
          Nat.add_mod _ _ _
        _ =
          (((A/T+b*c*A+triangle b*T*c^2*A+
            tetra b*T^2*c^3*A)%T^3)+
            ((c*A+b*T*c^2*A+triangle b*T^2*c^3*A)%T^3))%T^3 := by
            rw [ih,hmul]
        _ =
          ((A/T+b*c*A+triangle b*T*c^2*A+tetra b*T^2*c^3*A)+
            (c*A+b*T*c^2*A+triangle b*T^2*c^3*A))%T^3 :=
          (Nat.add_mod _ _ _).symm
        _ =
          (A/T+(b+1)*c*A+triangle (b+1)*T*c^2*A+
             tetra (b+1)*T^2*c^3*A)%T^3 := by
             rw [triangle_succ,tetra_succ]
             congr 1
             ring

/-- Exact cubic physical perfect-power law, extending the GST
Worldtrace control to THREE scale bands, for ALL offsets M,
all multipliers u, all scales L, and every
1<=w<=3*(L+1). -/
theorem pow4_cubic_window_lift
    (M u L w : Nat) (hw : 1 ≤ w) (hband : w ≤ 3*(L+1)) :
    (4^(M+u*3^L)/3^(L+1))%3^w =
      (4^M/3^(L+1)+
        u*GSTCanonicalTailLTE.lteCoeff L*4^M+
        triangle u*3^(L+1)*(GSTCanonicalTailLTE.lteCoeff L)^2*4^M+
        tetra u*(3^(L+1))^2*(GSTCanonicalTailLTE.lteCoeff L)^3*4^M)%3^w := by
  have hdiv : 3^w ∣ (3^(L+1))^3 := by
    have h := Nat.pow_dvd_pow 3 (show w ≤ (L+1)*3 by omega)
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
         3^(L+1))%((3^(L+1))^3))%3^w :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
    _ =
      ((4^M/3^(L+1)+u*GSTCanonicalTailLTE.lteCoeff L*4^M+
        triangle u*3^(L+1)*(GSTCanonicalTailLTE.lteCoeff L)^2*4^M+
        tetra u*(3^(L+1))^2*(GSTCanonicalTailLTE.lteCoeff L)^3*4^M)%
          ((3^(L+1))^3))%3^w := by
          rw [quotient_cubic_block_lift _ _ _ _ (by positivity)]
    _ =
      (4^M/3^(L+1)+u*GSTCanonicalTailLTE.lteCoeff L*4^M+
        triangle u*3^(L+1)*(GSTCanonicalTailLTE.lteCoeff L)^2*4^M+
        tetra u*(3^(L+1))^2*(GSTCanonicalTailLTE.lteCoeff L)^3*4^M)%3^w :=
      Nat.mod_mod_of_dvd _ hdiv

#print axioms power_quadratic_mod_cube
#print axioms quotient_cubic_block_lift
#print axioms pow4_cubic_window_lift

end GSTWorldtraceCubicBlockLift
