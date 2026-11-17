<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #1129 / 1132
<!--    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/docs/superpowers/specs/2026-08-17-prefix-one-physical-crossing-design.md
<!--    Ref          : origin/sol/5c579-final-bigN-right-chord-atomic
<!--    First-commit : 2026-08-17 22:06:13 +0530  (deea9a0)
<!--    Last-commit  : 2026-08-17 22:06:13 +0530  (deea9a0)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 22:06:13 +0530  deea9a0  (ker07-dev)
<!--        surgery: lock 5c579 with full BIG-N right-chord research monolith
<!-- ====================================================================== -->

# Prefix-One Physical Crossing Surgery Design

## Goal
Remove the active dependency on the quarantined residual Ω termination chain and close the prefix-one contradiction through the canonical pure-power phase crossing, so the monolithic proof can compile and reach the comparator.

## Frozen checkpoint
Work only from commit `d6e948c7e13af100210bfbf9956394cde358e743` on branch `sol/physical-phase-crossing-surgery`.

The existing carry-normalization repair is frozen. Do not reactivate `gst_residual_omega_termination`; run #279 proved that doing so exposes three genuine `False` holes.

## Mathematical architecture
Use the exact canonical prefix-one pure-power square. For the child tail `T` and parent affine tail `H`, identify:

- phase 0: `E0 = 1 + 3*D*T`,
- phase 1: `E1 = 1 + D + 3*D*H`,
- with `E1` obtained from the same exact power-of-four rectangle as `E0`.

A child Happy Gate is converted to a phase-zero `GSTDoubleJumpS`. Prove that this double jump crosses the canonical pure-power rectangle to a phase-one `GSTDoubleJumpS`. Existing `gst_physical_crossing_contradicts_parent_badS` then contradicts complete seed-one parent badness.

## Scope locks
- No internet or external theorem search.
- No residual Ω termination proof.
- No global ALT-minus mirror assumption.
- No `sorry`, `admit`, `axiom`, `mkSorry`, or `native_decide`.
- No changes to `Solution.lean`, comparator configuration, odd case, modular base, or the already-fixed carry equation unless a compiler error forces a strictly local compatibility edit.
- Do not claim completion until the full comparator prints its success verdict.

## Proof boundary
The only new mathematical theorem permitted is a canonical specialization of physical phase crossing from the exact pure-power rectangle. Generic `GSTPhysicalPhaseCrossingS` is not to be proved without the canonical relations between `D`, `T`, `H`, `E0`, and `E1`.

## Verification
1. Red test: a dedicated Lean scratch states the canonical crossing theorem without proof and must fail at that theorem only.
2. Green scratch: prove the theorem with existing pure-power residue/carry-word/strip-conservation infrastructure.
3. Transplant a thin adapter into `ErdosTernary2.lean` replacing the dependency on `gst_residual_omega_termination`.
4. Build `ErdosTernary2`.
5. Build all active scratch modules and audits.
6. Build `Challenge` and `Solution`.
7. Run the pinned comparator and require `YOUR SOLUTION IS OKAY`.