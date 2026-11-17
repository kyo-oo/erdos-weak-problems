<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #1044 / 1132
<!--    Path         : branches/sol_physical-phase-crossing-implementation/docs/superpowers/specs/2026-08-17-prefix-one-phase-crossing-surgery-design.md
<!--    Ref          : origin/sol/physical-phase-crossing-implementation
<!--    First-commit : 2026-08-17 13:50:53 +0530  (11366ca)
<!--    Last-commit  : 2026-08-17 13:50:53 +0530  (11366ca)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 13:50:53 +0530  11366ca  (ker07-dev)
<!--        docs: lock prefix-one phase crossing surgery design
<!-- ====================================================================== -->

# Prefix-One Phase Crossing Surgery Design

Date: 2026-08-17
Branch: `sol/physical-phase-crossing-surgery`
Historical comparator target: `4669bb5e87587f04a49aeabfbce1083eecd8f975`

## Objective

Close the single historical Lean goal left by the comparator snapshot without introducing `sorry`, `admit`, `native_decide`, custom axioms, residual-termination assumptions, terminal-NULL assumptions, or circular imports.

The isolated mathematical target is the canonical phase-crossing statement:

```lean
theorem gst_canonical_prefix_one_phase_crossing_RED
    (s n c z T H E0 E1 q0 : Nat)
    (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hA : 4^(3^s) = 1 + 3^(s+1)*c)
    (hc : c = 1 + 3*z)
    (hT : E0 = 1 + 3*3^(s+1)*T)
    (hH : H = z + 4^(3^s)*T)
    (hE0 : E0 = 4^(3^(s+1)*n))
    (hE1 : E1 = 4^(3^s*(1+3*n)))
    (hchild : GSTDoubleJumpS (3*3^(s+1)) E0 q0) :
    ∃ q1, GSTDoubleJumpS (3*3^(s+1)) E1 q1
```

## Selected architecture: A -> C, with B only as fallback

### A. Exact physical power-strip crossing

1. Start from the child `GSTDoubleJumpS` witness.
2. Rewrite the child/parent power relationship using the exact phase identity `E1 = 4^(3^s) * E0`.
3. Use the power-strip carrier lemmas to translate a child common-two/double-jump into exact strip quotient/carry data.
4. Attempt same-row transport using the exact commuting-square correction equations.
5. If same-row crossing succeeds, construct the parent `GSTDoubleJumpS` witness immediately.
6. If same-row crossing fails, use the existing theorem that failure leaves a live vertical correction modulo 3. Follow that correction forward using the exact correction recurrence rather than discarding it.

### C. BIG1 projector as an internal weapon, not an assumption

The live correction must be converted into the microscopic bridge language. The goal is to derive, from the physical strip/correction equations, the conditions required by the existing BIG1 projector. In particular, BIG1-clearness may not be postulated.

Once the derived bridge state is nonzero and BIG1-clear, the projector forces the surviving information state into the unique physical BIG2/SURVIVE realization. The intended endpoint is the microscopic `(5,5)` GST+ / SURVIVE -> SURVIVE cell, which supplies the parent phase crossing.

### B. Natural-origin descent fallback

Use only if the A -> C route exposes a genuinely missing invariant that cannot be derived locally.

Assume no parent crossing, build the canonical two-boundary trap after the globally last child gate, regenerate the exact shared information state through the natural-origin transformation, and descend along the finite ternary support of natural `n`. The descent must terminate at a proven finite base case; no terminal-NULL axiom is permitted.

## Safety constraints

- Do not use the current stale inline closure that depends on commented-out residual-overproof declarations.
- Do not assume BIG1-clearness.
- Do not infer parent activity from mere positivity of `gstParadoxTransfer`.
- Do not use same-row transport as if it were automatic.
- Do not introduce a theorem stronger than the isolated RED target unless it is independently proved from already compiled physical lemmas.
- Keep all experimental lemmas in scratch files until the isolated RED theorem compiles.

## TDD / verification sequence

1. Preserve `PhaseCrossingSurgeryRED.lean` as the failing RED test.
2. Confirm its failure is exactly the missing crossing step, not an import/name/type error.
3. Add the smallest missing physical lemma in a scratch module.
4. Compile the scratch module.
5. Recompile `PhaseCrossingSurgeryRED.lean`.
6. Repeat until RED becomes green.
7. Only then transplant the proved theorem into the historical materialized source corresponding to commit `4669bb5...`.
8. Compile the authoritative materialized monolith.
9. Run source audit for `sorry`, `admit`, `mkSorry`, custom axioms, and `native_decide`.
10. Run the comparator workflow. Completion is claimed only if the fresh compile and comparator are green.

## Expected historical closure

The final historical proof should manufacture a parent `SURVIVE`/double-jump witness from the child gate, then contradict the historical hypothesis forbidding all parent SURVIVE events. The proof should not rely on the old positive-transfer/finite-ceiling recurrence, because positivity alone does not force a parent event.

## Stop conditions

If A -> C cannot derive the necessary projector hypotheses from the exact physical equations, do not patch around the gap. Record the precise missing invariant and switch to B. If B also reaches an unproved mathematical statement, leave the RED test failing and report the exact residual theorem instead of weakening the statement or adding assumptions.
