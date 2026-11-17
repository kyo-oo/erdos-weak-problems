# Mathbox / Wolfram — exact origin of `sorryAx` and physical GST U-flux repair (2026-10-30)

## Contract (no goal changes)

The original target remains
```lean
∀ K : Nat, 5 ≤ K → K ≠ 7 →
  ∃ p : Nat, 1 ≤ p ∧
    digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2
```
The benchmark's existing `gst_four_power_third_wave_gate` assumption
must be removed only by a kernel-checked proof of this exact statement.
A new equivalent axiom, def, instance, sorry, or theorem name is not a proof.

## Source of `sorryAx` — exact failure

`GSTInfiniteFourPowerNavigation.lean:176` calls
`four_power_collision_arith` at the end of
`power_three_step_collision`. The old CI
https://github.com/kyo-oo/erdosternary2/actions/runs/41039244379
shows:
```text
GSTInfiniteFourPowerNavigation.lean:176:2:
  linarith failed to find a contradiction
```
Lean's error-recovery inserts `sorryAx` into that incomplete theorem,
and `#print axioms` then reveals `sorryAx` in
`power_three_step_collision`, `four_power_happy_ge_three`,
and `gst_four_power_navigation_universal`. The eventual
`fourPowerDirectExistence_closed` importing this route inherits it.
The problem is NOT the syntax of the last tactic.

The proof has:
1. `hChild`: a genuine Happy cell on `E=4^K` at `p=3+q`.
2. `hRightBad`: a putative all-depth BAD parent `64E`.
3. `hleft`: left phase-prefix pressure > 0.
4. `hright`: right phase-prefix pressure ≤ 0.
5. `hWidth3`: exact digit and wide-carry conservation.
6. `hUPositive`: local U defect > 0.
7. `hU`: exact vertical U-flux telescope (Equation III).

What is absent: a source-specific GLOBAL implication connecting
the left and right pressure signs so that (1)-(7) cannot coexist,
not another arithmetic identity for a single cell.

## Physical test — why the local sign argument fails

At `K=8, E=4^8=65536, N=3, b=3, q=1`, the genuine child
`4^8` has a Happy cell at `p=4`; the genuine parent
`4^11` has no Happy at `p=3` or `p=4`. Its first actual
common-two witness is later, at `p=10`.

Direct arithmetic using the exact GST physical twelve-state tables:

```text
child at p=3: (carry,digit)=(1,0), phaseDensity=-4
child at p=4: (carry,digit)=(0,2), phaseDensity=+2
parent at p=3:(carry,digit)=(2,1), phaseDensity=-1
parent at p=4:(carry,digit)=(2,1), phaseDensity=-1
```

Therefore
```text
graphPhaseWindow E 0 3 2 = (-4)+3*(+2) = +2
graphPhaseWindow E 3 3 2 = (-1)+3*(-1) = -4
J_left(p=4) = -8
J_right(p=4) = +6
J_right - 64*J_left = 6 -64*(-8) = +518
```

All local facts the old proof tries to combine are literally
compatible on a genuine perfect-power source.
In particular `phaseLeft ≤ phaseRight` at the SAME terminal
row is false: `+2 ≤ -4` fails. Any valid collision
transport must be **nonlocal in height**.
Formal theorem `GSTProblem406TruePowerPhaseMismatch.k8_exact_phase_mismatch_and_u_defect`
and its local comparison no-go are strict Lean-kernel verified:
https://github.com/kyo-oo/erdosternary2/actions/runs/41059938777 .

## NEW kernel-verified all-K physical terminal boundary

`GSTProblem406TerminalUBoundary.lean`, verified by
https://github.com/kyo-oo/erdosternary2/actions/runs/41058947333 ,
proves for EVERY K≥13:

```text
P_K = ceil(24*(K+3)/19)+2
256*4^K < 3^(P_K)
potentialWith gstUChargeExact 64 (unifiedState (4^K) 3 P_K).core = -315
```

The last fact comes from the exact GST physical state:
all four column carries, the reverse carryWord and childTail
are zero at the chosen terminal height. Hence U=5-64*5=-315.

Write `H=P_K-3`, `U_3=U(E,3)`,
`J_L(p)=gstUJumpExact` on `graph E 0 p` and
`J_R(p)` on `graph E 3 p`. The theorem
`pure_source_terminal_u_telescope` proves precisely
```text
SUM_{j=0}^{H-1} 3^j [ J_R(3+j)-64*J_L(3+j) ]
  = -315*3^H - U_3
```
without `hGate`, `sorryAx`, or unjustified terminal truncation.

Wolfram independent exact test K=13:
`P_13=23`, `U_3=-219`, both sides
`-1098337086096`.

## Further algebraic reduction: remove terminal background

Both jumps on a zero-carry, zero-digit cell are `10`.
Define `j_L=J_L-10` and `j_R=J_R-10`.
Using `2*SUM_{j=0}^{H-1}3^j=3^H-1`, the
already-proved physical telescope yields the precise finite
renormalized charge equation

```text
SUM_{j=0}^{H-1} 3^j [ j_R(3+j)-64*j_L(3+j) ]
  = -315 - U_3.
```

The huge `3^H` terms CANCEL exactly, so this is the finite
support-sensitive checksum a nonlocal GST proof can use.
This renormalization is now a STRICT Lean-kernel theorem
`GSTProblem406TerminalUBoundary.pure_source_renormalized_u_checksum`.
Axiom audit / build SUCCESS: https://github.com/kyo-oo/erdosternary2/actions/runs/41061241211 .

`U_3` only depends on `4^K mod 27`, so on `K mod 9`
(since `4^9 ≡ 1 (mod 27)`). Wolfram exact table:

| K mod 9 | U_3 | -315-U_3 |
|---|---:|---:|
| 0 | -257 | -58 |
| 1 | -89 | -226 |
| 2 | -51 | -264 |
| 3 | -393 | +78 |
| 4 | -219 | -96 |
| 5 | +87 | -402 |
| 6 | +125 | -440 |
| 7 | -91 | -224 |
| 8 | -561 | +246 |

This table is exact arithmetic but NOT yet a standalone
Lean period-9 proof. It also proves a limitation:
the original exceptional `K=7` and genuine
`K=16` share the same initial and terminal U
signature (`U_3=-91`, terminal=-315) while
their full ternary trajectories differ.
Therefore endpoints ALONE cannot establish the all-K gate.

## Required continuation — one substantive mathematical implication

Need exploit the *interior* zero-free, odd-cofactor-one source
`E=4^K` to rule out an **all-depth BAD right-hand trajectory**.
The proof must be strong enough to contradict
`hRightBad`, not merely compute a local positive U defect,
an exact terminal U value, or a finite checksum.

The formerly suggested all-source bound
`BAD(R), 0<R<3^L -> v2(R) ≤ floor(4L/3)`
is mathematically FALSE, now proved so in
`GSTProblem406BadValuationNoGo.lean`, strict CI
https://github.com/kyo-oo/erdosternary2/actions/runs/41039922733 .
It cannot be used. The true 24/19 source bound must be
combined with a genuinely *source-specific*, noncircular
arithmetic invariant of the full interior.

No production proof was modified or mislabelled proved.
