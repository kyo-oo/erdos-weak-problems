<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #1057 / 1132
<!--    Path         : branches/sol_5c579-big1-two-digit-surgery/docs/5C579_RIGHT_CHORD_SURGERY_LEDGER.md
<!--    Ref          : origin/sol/5c579-big1-two-digit-surgery
<!--    First-commit : 2026-08-17 20:54:45 +0530  (65e69b5)
<!--    Last-commit  : 2026-08-17 20:54:45 +0530  (65e69b5)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 20:54:45 +0530  65e69b5  (ker07-dev)
<!--        Record 5c579 right-chord surgery invariants
<!-- ====================================================================== -->

# 5c579 right-chord surgery ledger

Target baseline: `5c579001d26fc807dba46b565978ab0d0ad455ab`.

## Non-negotiable projector scope

`I != 1` is **not** a global hypothesis on the full Omega-infinity orbit.
It is used only when the handwritten formula is explicitly solving a physical
two-digit / two-micro-layer cell.  Outside that local solve, Omega-infinity,
Navigation, origin descent, and the public universal theorem remain unrestricted.

## Combined chord

For one x2/base3 micro bridge:

    a + 2*d = e + 3*a'
    e = (a + 2*d) mod 3

In a local two-digit solve, nonzero BIG1-clear information forces the unique
SURVIVE micro state:

    a = 1, d = 2, e = 2, mass = 5, event = 8.

For one physical x4 cell (two micro layers), the relevant orientations are:

    hidden:  masses (2,4), information 1 -> 2 -> 1
    NULL:    masses (4,2), information 2 -> 1 -> 2
    GST+:    masses (5,5), information 2 -> 2 -> 2

The local `I != 1` two-digit projector removes the two orientation-changing
paths and selects GST+.

The selected state obeys the exact chord

    55_6 = 5 + 6*5 = 35 = 6^2 - 1

and the same integer is the aligned V2 mass

    35 = 3 + 4*8,      8 = (22)_3 = 2 + 3*2.

At mass five the handwritten kernel denominator is one:

    6 - 5 = 1,

so the magnitude of `7/(x-6)` on the selected physical state is 7.

## Existing historical machinery retained

- `gstOmega` and `gstOmegaStep`.
- `GSTOmegaInfiniteBadTrace`.
- exact parent projection.
- `GSTPrefixOneOmegaData.childGate`.
- Infinite-Paradox conserved energy and transfer.
- canonical Navigation constants and origin decomposition.
- `gst_prefix_one_omega_bad_of_no_parent_navigation_inline`.
- `gst_prefix_one_bad_implies_no_survive`.
- `gst_power_two_wave_large` as final consumer.

## Historical dependency being removed from the public lift

Old public route:

    gst_prefix_one_navigation_lift
      -> gst_prefix_one_child_gate_contradicts_parent_bad_inline
      -> gst_prefix_one_information_bad_descends_inline
      -> gst_residual_omega_termination

Replacement route under construction:

    parent Navigation failure
      -> exact Omega-infinity bad trace
      -> actual canonical child Happy Gate
      -> canonical physical two-digit alignment
      -> LOCAL two-digit I != 1 projector
      -> unique GST+ (5,5)
      -> parent SURVIVE occurrence
      -> contradiction with bad trace
      -> parent Navigation witness.

## Required bridge theorem

The next theorem must not add a new public assumption.  It must prove that the
actual canonical child Happy Gate is represented by the physical two-digit cell
on which the local projector is legitimately evaluated.  Working name:

    gst_prefix_one_child_gate_projected_two_layer_inline

Then the closure theorem is:

    gst_prefix_one_child_gate_forces_parent_survive_inline

with target:

    exists j, gstOmegaEvent s 1 n j = .survive

After these are kernel-green, only the body of
`gst_prefix_one_navigation_lift` is surgically rewired; the surrounding
400KB theorem architecture is left intact.
