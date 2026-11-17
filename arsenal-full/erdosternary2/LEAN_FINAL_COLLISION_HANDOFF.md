# Lean Final Collision: Complete Technical Handoff

## Objective

Finish the Erdos ternary monolith by giving a **kernel-checked Lean proof** of the one remaining mathematical collision theorem and then verify the complete repository with its exact V5 comparator.

This is not presently a syntax, elaboration, recursion, import, or tactic problem. The remaining failure is a missing mathematical implication. A valid solution must provide it without `sorry`, `admit`, a new `axiom`, `native_decide`, or a trust-expanding shortcut.

## Repository state

- Repository: `kyo-oo/erdosternary2`
- Branch: `sol/gpt56-canonical-tail-escape-20260827`
- Restored surgery commit: `f44ba0584d7b4e5f80a3522f8b40f340b8894e46`
- Restored patch: `scripts/patch_live_hcreationcheck.py`
- Do not revert that commit merely because the complete comparator remains red.

Green on the restored commit:

- `GPT56 Monolith Surgery Probe`, run `33282241001`
- `GPT56 Monolith Surgery Trace 2`, run `33282240995`

Those checks establish that the surgery is applied and reaches the intended code. They do **not** establish that the final theorem compiles.

Still red:

- `GPT56 V5 Comparator Now`, run `33282241030`

The preceding exact comparator run `33281818966` built 17,457 of 17,458 targets. Its sole failed target was:

```text
GSTGraphV2PerfectPowerBlockCollision
```

## Exact theorem that must be proved

File: `GSTGraphV2PerfectPowerBlockCollision.lean`

Namespace: `GSTGraphV2PerfectPowerBlockCollision`

```lean
theorem canonical_perfect_power_block_collision
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hChild : HappyCell
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.carry
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.carry
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.digit) :
    False := by
  -- missing proof
```

Definitions:

```lean
def canonicalEnergy (s n : Nat) : Nat := 4^(3^(s+1) * n)
def canonicalWidth (s : Nat) : Nat := 3^s
```

The theorem says:

> A genuine Happy cell on the left boundary of the canonical perfect-power sheet cannot coexist with a completely bad right boundary after the horizontal shift `3^s`.

Under the power-origin identification:

```text
left exponent  = 3^(s+1) * n
right exponent = 3^(s+1) * n + 3^s
               = 3^s * (1 + 3*n).
```

The required conclusion is not merely a finite-prefix sign estimate. From the supplied child Happy witness and the arithmetic structure of this exact power block, derive a Happy witness somewhere on the right boundary, contradicting `hRightBad`.

## Current incomplete proof and exact gap

The current proof defines:

```lean
let E := canonicalEnergy s n
let N := canonicalWidth s
let b := s + 2
let M := 3^(s+1) * n
```

It successfully derives:

```lean
hleft : 0 < graphPhaseWindow E 0 b (q+1)
hright : graphPhaseWindow E N b (q+1) ≤ 0
```

It transports both boundaries to absolute powers:

```lean
hleftAbs : HappyCell
  (graph 1 M (b+q)).seven.carry
  (graph 1 M (b+q)).seven.digit

hrightAbs : ∀ j, ¬ HappyCell
  (graph 1 (M+N) (b+j)).seven.carry
  (graph 1 (M+N) (b+j)).seven.digit
```

It then obtains:

```lean
hU := unified_equationIII_vertical_telescope E N b (q+1)

hPureRight :=
  blockDensity_prefix_nonpositive_of_bad E N b (q+1) ...

hPureExact := blockDensity_column_exact E N b (q+1)
```

The file ends with:

```lean
dsimp [E, N, b, M] at
  hleft hright hleftAbs hrightAbs hU hPureRight hPureExact ⊢
trace_state
omega
```

`omega` fails because these facts remain mathematically disconnected. The exact telescopes do not yet establish a comparison transporting the strictly positive left pressure into a strictly positive observable on the allegedly bad right boundary.

A larger tactic cannot fix this. A genuine conservation, monotonicity, crossing, or collision lemma is missing.

## What the missing lemma must accomplish

Any sound formulation is acceptable, but it must complete a chain equivalent to:

```text
hChild
  -> strictly positive finite left-boundary observable
  -> exact transport across width 3^s
  -> strictly positive finite right-boundary observable
  -> existence of a right-boundary Happy cell
  -> contradiction with hRightBad.
```

A sufficient direct formulation would be:

```lean
private theorem canonical_block_positive_transport
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hChild : HappyCell
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.carry
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.digit) :
    ∃ j, HappyCell
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.carry
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.digit := by
  ...
```

That statement may be stronger than the best immediate helper. A useful intermediate form may instead derive the nonpositive crossing prefix under `hRightBad` by combining the exact controller ledger with the exact U2D rectangle identity:

```lean
private theorem canonical_right_bad_weighted_cross_nonpos ... :
    weightedCrossPrefix ... ≤ 0 := by
  -- existing InfiniteBadCoupledControl
  -- exact all-depth controller ledger
  -- exact U2D rectangle identity
  -- explicit endpoint cancellation/sign bounds
  ...
```

Select a statement justified by the algebra. Do not assert a convenient inequality without deriving every boundary term.

## Intended U2D architecture

```text
existing child Happy
        |
        v
weightedCrossPrefix_positive_of_top_leading_happy
        |
        v
weightedCrossPrefix > 0

existing all-depth right badness
        |
        v
graph_infinite_bad_control / InfiniteBadCoupledControl
        |
        v
exact all-depth controller ledger
        +
exact U2D rectangle identity
        +
explicit endpoint cancellations or sign estimates
        |
        v
weightedCrossPrefix ≤ 0

        > 0 and ≤ 0
        |
        v
False
```

The unresolved step is deriving cross-prefix nonpositivity from the ledger and rectangle identity. Several draft files construct both objects and then call `omega`; those are manifestations of the same unproved seam.

## Primary supporting Lean files

### Target and downstream consumer

- `GSTGraphV2PerfectPowerBlockCollision.lean`
  - Failed target theorem.
  - Defines `blockDigitPotential`, `blockCarryPotential`, and `blockDensity`.
  - Proves the physical table, Happy/positivity equivalence, bad-cell nonpositivity, and exact vertical telescope.

- `GSTPrefixOneU2DCollisionProof.lean`
  - Converts the child quotient Happy witness to the left graph boundary.
  - Converts complete seed-one parent badness to the right graph boundary.
  - Calls `canonical_perfect_power_block_collision` from `canonical_prefix_one_u2d_collision`.

- `ErdosTernary2.lean`
  - Monolith.
  - `gst_step6_collision_kernel` adapts monolith objects into `canonical_prefix_one_u2d_collision`.
  - Do not import the monolith into a supporting module; that creates a cycle.

### Canonical power and graph adapters

- `GSTGraphV2PerfectPowerBlockProbe.lean`
  - `canonicalEnergy`, `canonicalWidth`
  - `canonical_power_origin_happy_iff`
  - `graphPhaseWindow`
  - left-Happy positivity and right-bad nonpositivity
  - exact shifted phase and digit-boundary identities.

- `GSTGraphV2PerfectPowerAncestry.lean`
  - Power-origin transport between an energy `4^K` graph and `graph 1 K`.

- `GSTGraphV2InfiniteControl.lean`
  - Main graph and exact cell law.
  - Physical carry/digit bounds.
  - Exact prefix-slice digit, carry, and Happy adapters.
  - Exact crossing rectangle.

- `GSTPerfectPowerTailNavigation.lean`
  - `canonicalTail`
  - `canonical_tail_decomposition`
  - `perfect_power_happy_position_ge_cut`
  - `canonical_tail_projection`.

- `GSTPrefixOneSeedCore.lean`
  - `prefix_one_tail_shape`
  - Exact identity:
    ```lean
    canonicalTail s (1 + 3*n) =
      1 + 3 *
        (prefixOffset s +
          4^(3^s) * canonicalTail (s+1) n)
    ```
  - Identifies the exact prefix-one parent tail but does not produce Navigation without an additional master theorem.

### Exact U-flux, crossing, and phase components

- `GSTGraphV2CoupledUFlux.lean`
  - Exact coupled U-flux algebra.
  - `gstUChargeExact`, `gstUJumpExact`, and their complete physical table.

- `GSTGraphV2UnifiedVerticalTelescope.lean`
  - `unified_equationIII_graph_closed`
  - `unified_equationIII_vertical_telescope`.

- `GSTU2DCanonicalPhaseDensity.lean`
  - `phaseDensity`
  - Happy iff positive; non-Happy physical cells are nonpositive.
  - Exact vertical and rectangle telescopes.

- `GSTU2DExactCrossingCharge.lean`
- `GSTU2DSharpCrossingBlock.lean`
  - Crossing density, reverse crossing code, weighted crossing prefix, and positivity from a leading Happy cell.

- `GSTU2DPureDivergence83.lean`
  - Separate exact 8-by-3 density and rectangle telescope.
  - Useful certified boundary estimates, but it does not currently close the canonical collision.

### Infinite controller machinery

- `GSTInfiniteCollision.lean`
  - Exact coupled orbit and `InfiniteCoupledControl`.

- `GSTGraphV2InfiniteControllerBridge.lean`
  - Converts graph right-boundary badness into the infinite bad controller.

- `GSTFinalPrefixOneStep6Infinite.lean`
  - `canonical_infinite_bad_control`
  - `canonical_infinite_ledger`
  - all-depth graph/controller synchronization
  - exact cross/mixed controller divergence and rectangle telescope.

- `GSTFinalPrefixOneStep6Boundary.lean`
  - Boundary-focused Step-6 work built on the controller.
  - Audit its final implication; do not assume a theorem ending in unsupported `omega` is green.

- `GSTFinalPrefixOneDirectU2DCollision.lean`
  - Clearest draft of the intended direct solution:
    - `child_navigation_to_left_happy`
    - `residual_base_carry_zero`
    - `collision_rectangle_exact`
    - attempted `canonical_right_bad_forces_weighted_cross_nonpositive`
    - attempted final collision.
  - Its nonpositivity theorem also stops at `trace_state; omega`; it is not a certified bridge.

## Failed or invalid routes

### Old oscillation route

Do not use `gst_oscillation_from_navigation` as a witness producer.

In current source it returns essentially the proposition it receives: logical shape `P -> P`. The old `gst_four_power_creation_certificate_inline` calls it as though it generates a stronger witness. The restored `Nat.strongRecOn` surgery repaired accidental recursion/elaboration, then exposed this deeper mathematical defect. Keep the recursion repair; do not return to this oscillation route.

### Standalone universal four-power module

File: `GSTInfiniteFourPowerNavigation.lean`

It proposes:

```lean
theorem four_power_happy_ge_three (k : Nat) (hk : 8 ≤ k) :
    ∃ p : Nat, 3 ≤ p ∧
      HappyCell (carry4 (4^k) p) (digit3 (4^k) p)
```

and `gst_four_power_navigation_universal`.

Its induction depends on `power_three_step_collision`, which ends in another unsupported `omega`. Dedicated workflow `GPT56 Four Power Navigation Cert`, run `33129001622`, failed while compiling this module. Do not import these declarations as if they were green.

### Master-parameter wrappers

`GSTFourPowerOntologicalAdapter.lean`, `GSTPrefixOneOntologicalEscape.lean`, `GSTPrefixOneSeedCore.lean`, and `GSTPrefixOneLegacyCorollaries.lean` contain implications **from**:

```lean
FourPowerCreationMaster
```

They do not prove that proposition. Passing it as a parameter only relocates the missing theorem and cannot finish the unconditional monolith.

### Tactic escalation

Do not replace `omega` with `aesop`, `linarith`, `nlinarith`, or a custom tactic until a theorem connects the relevant quantities. Tactics cannot derive `False` from insufficient hypotheses.

### Forbidden fake fixes

Do not use:

```lean
sorry
admit
axiom
unsafe
native_decide
```

Do not weaken the target, remove it from the comparator, or alter the comparator to ignore it.

## Recommended development strategy

1. Work on the smallest standalone target first: `GSTGraphV2PerfectPowerBlockCollision.lean`.

2. Expand the definitions of:
   - `unified_equationIII_vertical_telescope`
   - `blockDensity_column_exact`
   - the chosen phase/cross rectangle identity.

3. Record every uncancelled boundary term.

4. Search for a symbolic linear combination of the certified twelve-state tables such that:
   - a leading left Happy cell makes the weighted total strictly positive;
   - all right cells being non-Happy makes it nonpositive.

5. For every boundary term, prove:
   - exact cancellation from the canonical power decomposition; or
   - a sign estimate from physical carry/digit bounds; or
   - exact equality from the infinite controller ledger; or
   - a fully formal finite-to-infinite limiting result.
   
   Never silently set a live upper boundary to zero.

6. Package the completed algebra into one bridge lemma, then make `canonical_perfect_power_block_collision` a short contradiction proof.

7. Compile `GSTPrefixOneU2DCollisionProof.lean`.

8. Apply `scripts/patch_live_hcreationcheck.py` exactly as CI does, compile the transformed monolith, and run the exact V5 comparator.

## Acceptable replacement from scratch

The entire collision mechanism may be replaced by a new theorem if it is unconditional, kernel-checked, acyclic, placeholder-free, and strong enough for the downstream proof.

For example:

```lean
theorem canonical_power_navigation_transfer
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (h : Navigation (4^(3^(s+1) * n))) :
    Navigation (4^(3^s * (1 + 3*n))) := by
  ...
```

This is the same substantive transport in another form and must be derived rather than postulated.

## Verification requirements

A completion claim is valid only when all conditions hold on the same final commit:

1. `GSTGraphV2PerfectPowerBlockCollision.lean` compiles.
2. `GSTPrefixOneU2DCollisionProof.lean` compiles.
3. The transformed `ErdosTernary2.lean` compiles.
4. The exact V5 comparator succeeds.
5. Axiom audits contain no `sorryAx` and no newly introduced custom axiom.
6. The final commit SHA and successful workflow URL are recorded.

Suggested audit:

```lean
import GSTGraphV2PerfectPowerBlockCollision
import GSTPrefixOneU2DCollisionProof

#print axioms GSTGraphV2PerfectPowerBlockCollision.canonical_perfect_power_block_collision
#print axioms GSTPrefixOneU2DCollisionProof.canonical_prefix_one_u2d_collision
```

## Definition of done

The task is complete only when the exact V5 comparator is green. A green patch-application probe, trace workflow, source audit, or partial build is supporting evidence but is not completion.

The central deliverable is a sound Lean derivation of the canonical left-Happy/right-all-bad contradiction. The existing surgery is already positioned to consume that theorem.
