import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# Mathbox GST local U-cocycle separator obstruction

We attempted to repair the open power_three_step_collision by
choosing an integer potential U of the four carry states and one linear
information-digit weight w. Let
 J(C,d)=3 U((C+4*d)/3)-U(C)-w*d.
A useful one-sided finite-support telescope would need
 (i) vacuum J(0,0)=0,
 (ii) all non-Happy J(C,d)>=0,
 (iii) each Happy J(C,2)<0 for C=0 or3.

These constraints are INCONSISTENT already on four physical cells.
This forbids one particular proof route, not the hGate statement.
A new source-sensitive cross-column, phase-dependent, or higher-state
potential is required to repair the actual collision.
-/

namespace GSTProblem406UGateSeparatorNoGo

/-- The needed four local inequalities themselves contradict.
The four cells are vacuum (0,0), BAD (2,0), BAD (2,1),
and Happy (0,2). Their actual next carries are 0,0,2,2. -/
theorem no_one_column_carry_potential
    (U0 U2 w : Int)
    (hVacuum : 3*U0-U0=0)
    (hBadTwoZero : 3*U0-U2>=0)
    (hBadTwoOne : 3*U2-U2-w>=0)
    (hHappyZeroTwo : 3*U2-U0-2*w<0) :
    False := by
  omega

/-- The original GST recurrence makes those four inequalities exactly
the ones from a proposed globally separating potential. -/
theorem no_global_GST_happy_separator
    (U : Nat → Int) (w : Int)
    (hVacuum :
      3*U ((0+4*0)/3)-U 0-w*(0:Int)=0)
    (hBadTwoZero :
      0<=3*U ((2+4*0)/3)-U 2-w*(0:Int))
    (hBadTwoOne :
      0<=3*U ((2+4*1)/3)-U 2-w*(1:Int))
    (hHappyZeroTwo :
      3*U ((0+4*2)/3)-U 0-w*(2:Int)<0) :
    False := by
  apply no_one_column_carry_potential (U 0) (U 2) w
  · norm_num at hVacuum ⊢
    exact hVacuum
  · norm_num at hBadTwoZero ⊢
    omega
  · norm_num at hBadTwoOne ⊢
    omega
  · norm_num at hHappyZeroTwo ⊢
    omega

#print axioms no_one_column_carry_potential
#print axioms no_global_GST_happy_separator

end GSTProblem406UGateSeparatorNoGo
