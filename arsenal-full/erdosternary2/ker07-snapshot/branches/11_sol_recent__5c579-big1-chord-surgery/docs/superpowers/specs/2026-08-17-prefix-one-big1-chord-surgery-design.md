<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #1058 / 1132
<!--    Path         : branches/sol_5c579-big1-chord-surgery/docs/superpowers/specs/2026-08-17-prefix-one-big1-chord-surgery-design.md
<!--    Ref          : origin/sol/5c579-big1-chord-surgery
<!--    First-commit : 2026-08-17 21:01:06 +0530  (565dccf)
<!--    Last-commit  : 2026-08-17 21:03:12 +0530  (3211b05)
<!--    Total commits: 2
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/2] 2026-08-17 21:01:06 +0530  565dccf  (ker07-dev)
<!--        Design atomic prefix-one BIG1 chord surgery
<!-- [02/2] 2026-08-17 21:03:12 +0530  3211b05  (ker07-dev)
<!--        Tighten BIG1 chord surgery binding contract
<!-- ====================================================================== -->

# Prefix-One BIG1 Chord Surgery — Design

Date: 2026-08-17
Target baseline: `5c579001d26fc807dba46b565978ab0d0ad455ab`
Surgery branch: `sol/5c579-big1-chord-surgery`
Target source: `ErdosTernary2.lean` (401200-byte post-Ω monolith)

## 1. Goal

Replace the remaining prefix-one information-transport seam with a direct, canonical, physically aligned argument assembled from:

- the post-Ω monolith's exact `GSTPrefixOneOmegaData` and Ω∞ bad-trace interface;
- the older information/regeneration/canonical-trap machinery;
- the later canonical-origin/physical-cut intersection machinery;
- Boss's handwritten `6^k`, `7/(x-6)`, simultaneous `×/÷ U`, `N_nav`, and `Ω_∞` structure;
- the exact GST Graph V2 six-state/two-micro-layer cell;
- the exact usable part of the eleven-equation interconnection;
- the new two-digit BIG1-clear rigidity and the `35 = 6^2 - 1` chord.

The public theorem must retain its original statement. No new axiom, no strengthened public hypothesis, no `sorry`, no `admit`, no `mkSorry`, and no `native_decide` are permitted.

## 2. Non-negotiable scope rule for `i != 1`

Boss's rule is local and literal:

> `i != 1` / `I != BIG1` may be invoked only when the proof has opened one actual physical two-digit / two-micro-layer cell of the handwritten formula.

It is NOT:

- a global condition on every Ω state;
- a premise of `GSTPrefixOneNavigationLift`;
- a premise attached to every information path;
- a replacement for canonical origin arithmetic;
- a license to delete the NULL/ALT− sectors globally.

The implementation therefore uses exactly one local predicate:

```lean
def GSTTwoDigitBig1ClearS (C d : Nat) : Prop :=
  d ≠ 0 ∧
  d ≠ 1 ∧
  gstFirstMicroOutputS C d ≠ 1 ∧
  gstSecondMicroOutputS C d ≠ 1
```

Legality bounds `C < 4` and `d < 3` remain theorem hypotheses, because they are physical-cell validity conditions rather than part of the BIG1 projector. `GSTTwoDigitBig1ClearS` may occur only in local two-layer lemmas; it may not occur in the statement of the public prefix-one theorem.

## 3. Existing Old-Sol seam to replace

The historical monolith already reduces the problem to the exact integration target:

1. `hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)`;
2. `gst_prefix_one_omegaData` chooses an actual child Happy Gate and packages exact Ω energy/step/echo data;
3. hypothetical parent failure produces `hBad : GSTOmegaInfiniteBadTrace s 1 n`;
4. the remaining transport is to force a parent SURVIVE occurrence from the canonical child gate;
5. Ω badness forbids every parent SURVIVE occurrence.

The current implementation reaches the contradiction through the old residual-Ω descent path. The surgery bypasses that active dependency and leaves unrelated parts of the monolith untouched.

## 4. Firepower retained from Old Sol

The surgery retains the exact monolith machinery:

- `GSTPrefixOneOmegaData`;
- `data.childGateIndex` and `data.childGate`;
- `data.energyExact`;
- `data.energyConserved`;
- `data.omegaStepExact`;
- `data.echoExact`;
- `gst_prefix_one_omega_bad_of_no_parent_navigation_inline`;
- `gst_prefix_one_bad_implies_no_survive`;
- `gst_omega_parent_projection`;
- `gst_omega_gate_polynomial_zero_iff`;
- exact GST carry/digit recurrence and Navigation-witness constructors.

These give the Ω∞ side of the chord and the contradiction target.

## 5. Firepower retained from Younger Sol

Only exact later discoveries are ported, and only as narrowly as needed.

### 5.1 Canonical shared-information conservation

The two realizations obey the exact carry equation

`a1 + A*h = p + 4*a0`.

This is the finite shared-information conservation law behind the Ω echo.

### 5.2 Canonical two-boundary trap

After the globally last child Happy Gate, hypothetical parent badness yields a finite trap with

`D + 4*Z = W + A*C`, `W < A`, `C = 2 or C = 3`,

plus complete seeded bad traces on both regenerated boundaries.

This is packaging, not the final separation theorem.

### 5.3 Canonical origin/physical-cut intersection

For `b = a + 3^k*m`:

- the physical carry at cut `k` depends only on canonical finite prefix `a`;
- the exposed digit is the prefix digit shifted by `m % 3`;
- good prefix carry plus shifted digit two constructs a genuine physical Navigation witness.

This prevents the rejected mistake of identifying a V2 re-coordinate with horizontal power transport.

### 5.4 Origin/Ω commuting square

The natural-origin product and Ω/information product reconstruct the same canonical energy `4^(3^t*n)`. One natural-origin step and one information-regeneration step therefore meet on the same conserved object.

### 5.5 U-potential

For legal GST cells, badness is the nonnegative local U-flow condition. The two negative jumps are exactly the physical Happy/BIG2 cells:

- NULL/BIG2: jump `-8`;
- GST+/BIG2: jump `-6`.

U is a conserved diagnostic/contradiction coordinate, not an independent forcing axiom.

## 6. Boss's handwritten operator retained

The structural operator remains

`ordered Π_t [ n_t * Σ_k 6^k * | (7/(x-6) ★_{×/÷} U_t) N_nav,t Ω_t |_V2 ]`,

with `n_t mod 3 != 0` on the residual aligned input where that condition is actually established.

The only scope refinement is that `I != BIG1` is invoked only after one selected contribution has been identified as an actual physical two-digit cell.

Nothing else is deleted:

- `6^k` is the state-count/weight axis;
- `7/(x-6)` is the local kernel;
- `★_{×/÷} U` retains the simultaneous GST+/NULL orientation reading;
- `N_nav` is the Navigation coordinate;
- `Ω_∞` is the information-wave coordinate.

## 7. Exact eleven-equation material allowed into the proof

Only exact identities may become Lean premises or lemmas.

Allowed/useful:

1. EQ2 event word: `J = d + 3e`; SURVIVE is `J = 8`.
2. EQ3 directed NULL-crossing projection.
3. EQ5 base-8 phase/orientation residue.
4. EQ6 canonical nested ternary phase address `Q_s(b) mod 3^k`.
5. EQ8 exact ternary scale valuation.
6. EQ10 binary-shadow/carry-flux identity.
7. EQ11 2/3 valuation imbalance.
8. Master generating identity: `4 D_R(x) - E_R(x) = (3/x - 1) C_R(x)`.
9. World projection: `4 D_R(3/K) - E_R(3/K) = (K-1) C_R(3/K)`.

Forbidden as proof premises:

- EQ7's heuristic classifier;
- EQ9 as a pointwise separator;
- defective EQ1 indexing;
- any unproved alternate-V2-to-horizontal-transport identification.

## 8. New local two-digit theorem package

One physical x4 GST cell decomposes into two x2/base3 micro-bridges. Define

```lean
def gstMicroHighBitS (C : Nat) : Nat := C / 2
def gstMicroLowBitS (C : Nat) : Nat := C % 2

def gstFirstMicroMassS (C d : Nat) : Nat :=
  gstMicroHighBitS C + 2*d

def gstFirstMicroOutputS (C d : Nat) : Nat :=
  gstFirstMicroMassS C d % 3

def gstSecondMicroMassS (C d : Nat) : Nat :=
  gstMicroLowBitS C + 2*gstFirstMicroOutputS C d

def gstSecondMicroOutputS (C d : Nat) : Nat :=
  gstSecondMicroMassS C d % 3
```

For one local two-digit solve, physical legality plus `GSTTwoDigitBig1ClearS C d` forces exactly

`C = 3`, `d = 2`, information path `2 -> 2 -> 2`, micro masses `(5,5)`.

The competing canonical BIG2 orientations are:

- hidden CREATE->DESTROY: `(2,4)`, path `1 -> 2 -> 1`;
- NULL DESTROY->CREATE: `(4,2)`, path `2 -> 1 -> 2`;
- GST+ SURVIVE->SURVIVE: `(5,5)`, path `2 -> 2 -> 2`.

Thus local `i != 1` is an orientation selector only after the physical two-layer cell has been identified.

## 9. The new 35 chord

For the unique local two-layer survivor,

`5 + 6*5 = 35 = 6^2 - 1`.

The same `35` is simultaneously:

- base-six word `55_6`;
- unique nonzero local two-layer BIG1-clear code;
- maximal fixed mass of the aligned 36-state V2 cell `(C,w)=(3,8)`;
- `w = 8 = 22_3`;
- physical GST+ `SURVIVE -> SURVIVE`;
- world-projection coefficient `K-1` at `K=36`.

This is the exact two-digit right chord.

## 10. General chord is support, not a global BIG1 premise

The bridge code identity is

`Σ_{j=0}^{k-1} 5*6^j = 6^k - 1`.

The exact world projection at `K=6^k` is

`4 D_R(3/6^k) - E_R(3/6^k) = (6^k-1) C_R(3/6^k)`.

The same coefficient `6^k-1` is therefore generated independently by bridge-world coding and carry-flux projection. This structural match does not authorize applying `I != BIG1` to an arbitrary full Ω path.

## 11. Kernel/U chord on the local cell

For `K_7(x)=7/(x-6)` on the physical active masses:

- mass `2`: magnitude `7/4`;
- mass `4`: magnitude `7/2`;
- mass `5`: magnitude `7`.

After the local two-digit classifier selects `(5,5)`, both micro-layers are fixed mass-5 GST+. The U-potential independently marks GST+/BIG2 as a negative-jump Happy/SURVIVE cell. This is a cross-check tying kernel orientation, U, V2, and Ω event semantics together.

## 12. The real RED target: canonical local-cell binding

The finite six-state classifier is not the hard theorem. The hard theorem must derive that the actual cell selected from `GSTPrefixOneOmegaData` is eligible for the local two-digit projector without adding projector membership as a public assumption.

The exact design contract is:

```lean
theorem gst_prefix_one_child_gate_projected_two_digit_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (data : GSTPrefixOneOmegaData s n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTTwoDigitBig1ClearS
      (gstOmega s 1 n data.childGateIndex).childCarry
      (gstOmega s 1 n data.childGateIndex).childDigit
```

This theorem is accepted only if every conjunct is derived from the already available public hypotheses plus exact canonical/handwritten identities. In particular, its intermediate/output `≠ 1` conjuncts may not be introduced as assumptions.

If the actual physical two-digit term required by the handwritten operator is not literally the raw `data.childGateIndex` cell, implementation may introduce a canonically computed local index `j*`; in that case the theorem must return both `j*` and the exact equality/projection facts that identify it with the corresponding Ω/Navigation physical cut. The existence of `j*` must still be derived, never assumed.

## 13. Direct replacement theorem

After the binding theorem, the closure contract is exactly:

```lean
theorem gst_prefix_one_child_gate_forces_parent_survive_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (data : GSTPrefixOneOmegaData s n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    ∃ j, gstOmegaEvent s 1 n j = .survive
```

Proof architecture:

actual child Happy Gate
→ canonical shared-information/physical-cut binding
→ one actual physical two-digit cell
→ local `GSTTwoDigitBig1ClearS`
→ unique `(5,5)` / GST+ / event-8 state
→ actual parent SURVIVE occurrence.

Then existing Ω badness contradicts that occurrence.

## 14. Minimal public splice

The public theorem statement remains unchanged. Its body becomes:

```lean
theorem gst_prefix_one_navigation_lift :
    GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  by_contra hnoParent
  have hBad : GSTOmegaInfiniteBadTrace s 1 n :=
    gst_prefix_one_omega_bad_of_no_parent_navigation_inline
      s n hs hnoParent
  let data : GSTPrefixOneOmegaData s n :=
    gst_prefix_one_omegaData s n hs hchild
  obtain ⟨j, hSurvive⟩ :=
    gst_prefix_one_child_gate_forces_parent_survive_inline
      s n hs hn data hBad
  exact gst_prefix_one_bad_implies_no_survive
    s n hs hBad j hSurvive
```

Old residual-Ω theorems may remain for historical compatibility, but the active public prefix-one proof may no longer depend on them.

## 15. Isolation strategy

No direct edit of the 401200-byte monolith until the replacement chain is green in scratch.

Implementation stages:

1. Port only the local two-micro-layer definitions and classifier to the frozen branch.
2. Prove local `35`/GST+ theorem independently.
3. Build the exact canonical local-cell binding theorem against the real 5c579 Ω interfaces.
4. Prove direct child-gate-to-parent-SURVIVE closure in scratch.
5. Splice only the minimum proven lemmas/body changes into `ErdosTernary2.lean`.
6. Verify the public lift no longer calls the residual-Ω termination route.

## 16. Verification contract

No completion claim without executable evidence.

Required checks when a Lean runner is available:

1. compile the new scratch target;
2. compile `ErdosTernary2`;
3. compile `Challenge` and `Solution`;
4. run repository audit;
5. run comparator/smoke comparator as configured;
6. grep for `sorry`, `admit`, `mkSorry`, `native_decide`;
7. inspect active `gst_prefix_one_navigation_lift` dependencies and confirm no call to `gst_residual_omega_termination`;
8. record exact compiler errors before and after surgery.

GitHub Actions platform/billing failures do not count as Lean verification. Source commits alone do not count as green builds.

## 17. Success criterion

Success means the original public theorem statement is preserved and the remaining prefix-one seam is closed by the canonical local two-digit chord, with no strengthened assumptions, no global BIG1 projector, and no active dependency on the residual-Ω overproof.
