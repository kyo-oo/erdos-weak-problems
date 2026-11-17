<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #1107 / 1132
<!--    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/docs/GST_V2_FINAL_BRIDGE_PROOF_CONTRACT.md
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

# GST Graph V2 — Final Bridge Proof Contract

## Purpose

This is the exact mathematical interface to implement/test when a working Lean runtime is available. It replaces vague requests for a generic phase crossing.

No theorem below is claimed proved merely by this document.

---

## 1. Final bridge target

For `s≥1` and positive residual origin `n` with `n mod3 !=0`, let

`T = Q_(s+1)(n)`,

`H = z_s + A_s*T`.

Assume:

1. `T` has a seed-zero Navigation/Happy witness;
2. `H` is a complete seed-one bad trace.

The missing theorem should conclude

`InfiniteTernarySupportS n`.

Lean-facing shape:

```text
GSTCanonicalResidualInfiniteSupportBridge :=
  forall s n,
    1 <= s ->
    1 <= n ->
    n % 3 != 0 ->
    GSTNavigationWitness (Q_(s+1)(n)) ->
    GSTSeededBadTraceS 1 (z_s + A_s*Q_(s+1)(n)) ->
    InfiniteTernarySupportS n
```

Once supplied,

`finite_origin_contradictionS n`

immediately yields `False`.

This is the exact consumer already proved in `FiniteSupportScratch.lean`.

---

## 2. Why this is sufficient for the production seam

The genuine generalized-cascade factorization entering the residual constructor is

`b = 1 + 3^k*n`,

with

`k>=1`, `n>=1`, and `n%3 !=0`.

For `k=1`, the bridge above is exactly the prefix-one residual.

For `k>1`, existing origin-closed/cut/mature-prefix machinery already removes many states; the production theorem should continue to use those exact constructors rather than forcing all cases through the new bridge.

The old standalone `GSTPrefixOneNavigationLift` is stronger than necessary because it quantifies over every positive `n`, including `n%3=0`, even though such an `n` means the factor `3^k` was not maximally extracted.

---

## 3. Mandatory first split

Because `n%3 !=0`, only two cases exist.

### Case A: `n%3=1`

Exact event law:

- first parent-tail input digit is zero;
- first parent event is NEITHER;
- parent carry seed regenerates `1 -> 0` (NULL).

Writing `n=3u+1`, the exact regenerated suffix is

`H_s(3u+1)/3 = w_s + A_s*H_(s+1)(u)`,

where

`w_s=(z_s+A_s)/3`.

The finite outer offset `w_s` must remain explicit. Do not replace this suffix by bare `H_(s+1)(u)`.

### Case B: `n%3=2`

Exact event law:

- first parent-tail input digit is one;
- output digit is two;
- first event is CREATE;
- parent seed remains one.

Writing `n=3u+2`,

`H_s(3u+2)/3 = ((z_s+2*A_s-1)/3) + A_s*H2_(s+1)(u)`.

Again the finite outer offset is part of the state and may not be dropped.

---

## 4. Existing immediate cylinder closure

If

`n≡4 (mod9)`,

then

`b=1+3n≡13 (mod27)`.

For `s>=2`, `NavigationResidueCutScratch.lean` already proves

`Q_s(b)≡19 (mod27)`,

and residue 19 gives a NULL Happy Gate at position two.

Therefore this entire origin cylinder contradicts complete parent badness immediately and should be discharged before invoking any new global bridge.

---

## 5. What must be produced for every cutoff

To prove `InfiniteTernarySupportS n`, fix an arbitrary cutoff `K`.

The bridge must construct

`k >= K`

such that

`ternaryOriginDigitS n k != 0`.

The construction may use:

- the child gate and its canonical causal origin prefix;
- exact pure-power residue fingerprints;
- EQ2 event-word information;
- the x2/base-6 bridge states;
- EQ5 half-phase all-BIG2 sheet;
- EQ6 / universal Q-origin modular address;
- EQ8/EQ11 scale data;
- EQ10/master carry potential;
- the exact finite offset/multiplier state produced by origin regeneration.

It may **not** use:

- a fixed bound on witness depth;
- a fixed bound on zero-origin runs;
- terminal NULL;
- a global mirror;
- generic affine reflection;
- the mere existence of a conserved equation without an exclusion step.

---

## 6. Exact information coordinates available

### Microscopic bridge

`m_(e,p)=floor(2^(e+1)/3^p) mod6`.

A full x4 Happy Gate is exactly a row where the two x2 bridge masses are

`(4,2)` or `(5,5)`.

### Physical two-row information digit

`m=C+4w=e+9C' = floor(36*x)`.

This is the same physical information object in input/output mixed-radix readings.

### Canonical origin universe

For every `M>0`,

`Q_t(b) mod Q_t(M) = Q_t(b mod M)`.

In particular `M=6^r` gives the exact finite binary/ternary origin coordinate.

### Event word

`J_p=d_p+3e_p`,

`sum J_p*3^p = 13R`.

No-SURVIVE means `J_p != 8` at every position.

### Master potential

`4D_R(x)-E_R(x)=(3/x-1)C_R(x)`.

Special projections:

- `x=1/2` -> factor 5;
- `x=3/8` -> factor 7;
- `x=1/4` -> factor 11;
- `x=1/12` -> factor 35;
- `x=3/6^r` -> factor `6^r-1`.

---

## 7. Exact proof criterion

A successful proof must establish a **forcing** statement, not another identity:

> if all origin trits beyond some cutoff were zero, then the finite regenerated `(offset,multiplier,0)` state would force a physical phase-one Happy Gate.

Equivalently:

> complete physical phase-one badness forces the canonical origin to keep injecting nonzero trits at arbitrarily high depths.

Once that implication is arithmetic, the mathematics closes through the existing finite-support contradiction.

---

## 8. Production surgery after proof

Only after the bridge is kernel-green:

1. instantiate `finite_origin_contradictionS` to refute the parent bad trace;
2. derive the residual `k=1` Navigation constructor;
3. plug it into `gst_navigation_witness_all_of_residual` / or refactor the strong-induction body to use the residual-only bridge directly;
4. remove the active dependency on `gst_residual_omega_termination`;
5. compile `ErdosTernary2`;
6. build `Solution`;
7. audit zero `sorry`/`admit`/axioms/native_decide;
8. run the real comparator.

No success claim before the actual comparator verdict.
