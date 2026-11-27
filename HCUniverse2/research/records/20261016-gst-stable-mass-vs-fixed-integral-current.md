# Mathbox: stable-mass saturation versus the required ONE fixed homology class
2026-10-16; original all-X Hodge-current target unchanged.

## Universal real calibrated current and stable mass

For every smooth projective X, every rational Hodge (p,p) class alpha,
clear rational denominators and make a sufficiently ample shift
beta=m alpha+M h^p, integral modulo torsion. A smooth closed strongly
positive (p,p) form F represents beta. The corresponding real normal
current S_F(phi)=integral_X F wedge phi is closed, has real class
PD(beta), and has Kähler mass equal to its calibration period P_beta.

Thus the infimum of mass over REAL normal currents in beta equals
P_beta. This is unconditional for every smooth projective X and
every rational Hodge alpha. This proves a real, NOT integral,
calibration saturation result.

Standard Federer--Fleming-style mass-controlled polyhedral
approximation of normal cycles, followed by rational approximation
within the finite rational affine space of cycles in the same
rational homology class, suggests closed RATIONAL polyhedral cycles
Q_epsilon in beta with Mass(Q_epsilon)<=P_beta+epsilon. This
external normal-current approximation theorem has not been checked
against a pinned primary source in this turn; treat its exact
hypotheses as an unverified source-dependent input rather than
a theorem proved in the HC-PROOF kernel.

Clearing the rational multiplicity denominator n_epsilon gives
a closed INTEGRAL rectifiable current T_epsilon=n_epsilon Q_epsilon
with:
  [T_epsilon]=n_epsilon PD(beta),
  D(T_epsilon)/n_epsilon <= epsilon.

It is in a MULTIPLE homology class, not in one fixed beta.
Dividing by the denominator destroys integral rectifiability.

## Exact all-multiples construction and decisive N-cohomology test

The existing Lean-green GSTNIntegralCalibrationGap model has:
  period(a,b)=2a+3b,
  mass(a,b)=2|a|+3|b|,
  D=mass-period.

For fixed integer period=1, every integral cycle has D>=4
by the already Lean-kernel-verified theorem
every_integral_carrier_has_defect_at_least_four.

Yet EVERY period n>=2 has a NONNEGATIVE integral cycle of
EXACTLY ZERO defect, explicitly:

  even n=2k+2, k>=0:  T_n=(k+1,0);
  odd  n=2k+3, k>=0:  T_n=(k,1).

These are general all-k formulas (not merely finite checks).
Both have period=n and mass=n. So the multiple-class stable
calibration defect vanishes IDENTICALLY for n>=2.

Try to transfer this to the original fixed integral class by
taking successive differences T_(n+1)-T_n:

  even-to-odd difference =(-1,1), period=1, D=4;
  odd-to-even difference =(2,-1), period=1, D=6.

Hence every successive difference has a STRICT POSITIVE
absolute calibration defect. This illustrates why coherent
all-multiples zero-defect sequences cannot be subtracted
to obtain a single fixed-class zero-defect sequence
without additional *geometric common-support cancellation*.

Wolfram exact integer calculations returned the alternating
difference defects 4,6 for n=2..10. The explicit formulas
prove the alternation for all k>=0. This toy model is not
a counterexample to the Hodge conjecture on real varieties.

## All-X Hodge research status (unchanged quantifiers)

- For every Hodge beta, smooth positive REAL current:
  constructed with defect zero.
- For every integral beta, genuine integer geometric current:
  constructed via triangulation and independently via the
  topological K-theory determinantal locus construction.
- Approximate integral calibrated cycles in expanding
  MULTIPLES n beta: stable norm route, relying on the
  noted external approximation theorem.
- Closed integral rectifiable currents all representing
  ONE FIXED beta with ABSOLUTE defect tending to zero:
  NOT CONSTRUCTED on arbitrary X.

The original universal fixed-homology target is equivalent
to rational Hodge algebraicity. No source-dependent geometric
selection hypothesis is silently added to a Lean theorem.
