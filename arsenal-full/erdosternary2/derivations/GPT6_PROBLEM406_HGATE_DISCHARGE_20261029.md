# Problem 406 — direct discharge of the one remaining `hGate` (2026-10-29)

## Exact target (not a renamed conditional)

Lean's isolated #print on run 40839818747 confirms:

```lean
def gst_four_power_third_wave_gate : Prop :=
  ∀ (K : Nat), 5 ≤ K → K ≠ 7 → GSTFourPowerThirdWave.thirdWave K
```

`GSTFourPowerThirdWave.fourPowerDirectExistence_iff_thirdWave` confirms this is equivalent to
`GSTFourPowerDirectExistence.FourPowerDirectExistence`, i.e. for each K≥5 other than7,
there exists a **single row p≥1** with digit two in both `4^K` and `4^(K+1)`.
`questions/deepmind_problem_406/Solution.lean` currently has
`erdos_ternary_2 (hGate : gst_four_power_third_wave_gate)`, so the
required final proof really is construction of a term of this type.

The complete conditional downstream assembly is **accepted as a valid conditional
proof**; this work does not rewrite or duplicate it.

## Focused direct construction completed

On branch `gpt6/problem406-hgate-discharge-20261029`,
`GSTProblem406HGateCoreClass.lean` uses the previously kernel-green GST
whole-block quotient identity for the two consecutive powers:

For any L≥6 and u≥0,

  floor(4^(4+u*3^L)/3^(L+1)) ≡ 19u (mod27),
  floor(4^(5+u*3^L)/3^(L+1)) ≡ 22u (mod27).

The first is a previously kernel-proven uniform result; the second is proved
in the new module, using exact LTE coefficient c_L≡16 (mod27).
The three ternary digits of the two full powers at positions L+1,L+2,L+3
therefore agree with those of 19u and 22u respectively.

A native Lean Fin27 check proves the two 3-trit words share a digit 2
for exactly the following 11 three-free multiplier residues modulo27:

  {1,2,5,7,8,11,14,17,20,23,26}.

Thus the new mathematically relevant theorem is

  all L≥6, all u≥0, if u%3≠0 and u%27 is not in
  {4,10,13,16,19,22,25},
  then CommonTwo(4+u*3^L).

This is a direct hGate-body witness, not merely a digit two in the source.
Dedicated Lean kernel run **40840753999 PASS**, with no sorryAx.

Wolfram independently checked K=5..1200 for common-two rows:
only K=7 was missing in this range. This is a bounded corroboration,
not a theorem. It also checked 240 exact (L,u) pairs against the new
same-row residue claim with zero violations.

`GSTProblem406HGateCoreIntegration.lean` transplants the new
CommonTwo theorem into the exact type `GSTFourPowerThirdWave.thirdWave`
and original `CreationCertificate`. Its dedicated isolated CI #40841697010 **PASSED** without sorryAx. The exact original gate-body and CreationCertificate are therefore kernel-proved for the 11 unbounded classes, but *not for all K*.

## Critical no-go / missing implication: hGate for every K

The stronger `FourPowerDirectExistence` / `gst_four_power_third_wave_gate`
is not yet discharged for *every* K. The seven uncovered u classes
are only the uncovered three-trit window within a special family
K=4+u*3^L; the full unconditional theorem covers all residues of K
and all observation depths.

The older attempted unconditional theorem
`GSTFourPowerDirectExistenceFromHappy.fourPowerDirectExistence_closed`
calls `GSTInfiniteFourPowerNavigation.four_power_happy_ge_three`.
The latter depends on `power_three_step_collision`, whose independent
run **40785543486 FAIL** at the final arithmetic contradiction (line176).
Its axiom audit shows sorryAx; the failure is not merely the name of
the hypothesis or a need to add an all-Nat conservation identity.

A generic "child Happy -> all-depth parent Happy" statement is false,
as Wolfram exactly reproduces source R=46, 4R with a Happy cell
and scaled 64R=2944 no Happy at any digit. The power-specific identity
R=4^K is indispensable. The existing all-Nat coupled controller
and terminal Ω normal form do not themselves supply this power-specific
cross-wave collision.

Success criterion remains unchanged:
provide a **kernel-checked** theorem `gst_four_power_third_wave_gate`
without assumptions and without sorryAx; then eliminate the `hGate`
argument in the comparator Solution.lean and run the strict type check.
Never substitute a conditional renamed theorem.

## Adversarial repair attempt at the stalled GST Equation-III collision

A possible remedy to the failed all-depth telescoping was to construct a
different four-carry-state charge U and a digit weight w such that the
local GST derivative J(C,d)=3 U(floor((C+4d)/3))-U(C)-w*d

* vanishes on the absorbing vacuum cell (0,0),
* is nonnegative on every BAD (non-Happy) cell,
* is strictly negative on each physical Happy cell.

Wolfram's exact Reduce over four integer/real unknowns found the
inequalities **infeasible**. A 4-cell symbolic subcertificate is:

- Vacuum (0,0): J=2U0=0, so U0=0.
- BAD (2,0): J=3U0-U2=-U2≥0, so U2≤0.
- BAD (2,1): J=2U2-w≥0, so w≤2U2.
- Happy (0,2): J=3U2-2w<0, so 3U2<2w≤4U2 and U2>0.

This contradicts U2≤0. It is a proof that **this class of local
one-column linear separator potentials cannot repair the collision**,
not a refutation of hGate itself or of source-dependent two-dimensional
GST potentials. The theorem is encoded in
`GSTProblem406UGateSeparatorNoGo.lean`; its dedicated kernel
audit workflow is `gpt6_problem406_u_separator_no_go.yml`.

Wolfram also checked the alternative no-adjacent-22 obstruction:
K in {6,7,12,13,18} all have no adjacent ternary 22
within K=5..350, while K=6,12,13,18 still have CommonTwo.
Hence no-22 classification *alone* cannot characterize the gate or
replace the missing power-specific collision.

The viable continuation must introduce an invariant that contains
**more than one carry column or an independent source-specific phase/
energy constraint**, since the one-column sign separator is impossible.
