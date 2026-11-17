import GSTWorldtraceBlockLift

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST two-support exact nonlinear blade
Combines two distinct ternary support positions without collapsing their
cross-carry interaction. This is a theorem about finite natural numbers,
not a conditional termination axiom or an empirical density rule.
-/

namespace GSTWorldtraceTwoSupport

/-- Exact two-support quotient with nested scales T and T*U.
The last term is the genuine pairwise nonlinear carry. -/
theorem quotient_two_support_exact
    (A T U c d : Nat) (hT : 0 < T) :
    (A * (1+T*c) * (1+T*U*d)) / T =
      A/T + A*c + A*U*d + T*A*U*c*d := by
  have hshape :
      A * (1+T*c) * (1+T*U*d) =
        A + T*(A*c + A*U*d + T*A*U*c*d) := by
    ring
  rw [hshape, Nat.add_mul_div_left _ _ hT]
  ring

/-- All two-support power-of-four traces, retaining exact cross support
mixing c_t*c_v, for every M,t,v with t <= v. -/
theorem power_four_two_support_exact
    (M t v : Nat) (htv : t ≤ v) :
    4^(M+3^t+3^v) / 3^(t+1) =
      4^M / 3^(t+1) +
      4^M * GSTCanonicalTailLTE.lteCoeff t +
      4^M * 3^(v-t) * GSTCanonicalTailLTE.lteCoeff v +
      3^(t+1) * 4^M * 3^(v-t) *
        GSTCanonicalTailLTE.lteCoeff t * GSTCanonicalTailLTE.lteCoeff v := by
  have hv : 3^(v+1) = 3^(t+1) * 3^(v-t) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow :
      4^(M+3^t+3^v) =
        4^M * (1+3^(t+1)*GSTCanonicalTailLTE.lteCoeff t) *
          (1+3^(v+1)*GSTCanonicalTailLTE.lteCoeff v) := by
    calc
      4^(M+3^t+3^v) = 4^M * 4^(3^t) * 4^(3^v) := by
        simp only [pow_add]
      _ = _ := by
        rw [GSTCanonicalTailLTE.pow4_three_power_lte_exact t,
            GSTCanonicalTailLTE.pow4_three_power_lte_exact v]
  rw [hpow, hv]
  exact quotient_two_support_exact (4^M) (3^(t+1)) (3^(v-t))
    (GSTCanonicalTailLTE.lteCoeff t)
    (GSTCanonicalTailLTE.lteCoeff v) (by positivity)

#print axioms quotient_two_support_exact
#print axioms power_four_two_support_exact

end GSTWorldtraceTwoSupport
