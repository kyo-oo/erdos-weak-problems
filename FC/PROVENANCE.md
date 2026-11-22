# FC/ — The Official DeepMind Formal-Conjectures Definitions (W82 vendoring)

**BOSS order (W82):** "THEY ARE NOT OFFICIAL STATEMENT OF THE PROBLEMS TO BE
PROVE … USE MY LEAN FILES, TO PROVE AND COMPLETE PROOF." The fix: every
kernel now states and proves THE OFFICIAL STATEMENTS — verbatim from
google-deepmind/formal-conjectures — over the OFFICIAL definitions, with the
BOSS arsenal as the proof machinery, on GitHub CI.

## Provenance

| File | Source @ google-deepmind/formal-conjectures `2207c54d` | Role |
|---|---|---|
| `Data/Set/Triplewise.lean` | `FormalConjecturesForMathlib/Data/Set/Triplewise.lean` | `Set.Triplewise`, `Set.triplewise_of_encard_lt` (behind `NonTrilinear`) |
| `Data/Sym/Sym2.lean` | `FormalConjecturesForMathlib/Data/Sym/Sym2.lean` | dependency of `Geometry.Metric` |
| `Logic/Equiv/Fin/Rotate.lean` | `FormalConjecturesForMathlib/Logic/Equiv/Fin/Rotate.lean` | dependency of `Geometry.2d` |
| `Geometry/Metric.lean` | `FormalConjecturesForMathlib/Geometry/Metric.lean` | dependency of `Geometry.2d` |
| `Geometry/TwoD.lean` | `FormalConjecturesForMathlib/Geometry/2d.lean` (module renamed `2d` → `TwoD`; `2d` is not a valid Lean module identifier) | `ℝ²`, `NonTrilinear`, `ConvexIndep`, `HasConvexNGon` — the #107 official definitions |
| `Combinatorics/AP/Basic.lean` | `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` | `Set.IsAPOfLength`, `Set.IsAPOfLengthFree`, `Set.IsAPOfLengthFree.maxCard` — the official `r_k(N)` of #142 |

Note on `pathGraph` (W82 CI verdict): the upstream `erdos_61.variants.p5`
references `pathGraph`, which I initially vendored as a new definition —
the first kernel-fc CI run proved Mathlib v4.33.0-rc2 ALREADY declares
`SimpleGraph.pathGraph` (in `Mathlib.Combinatorics.SimpleGraph.CycleGraph`).
The vendored duplicate was DELETED (commit: the kernel-fc repair); the
official statement resolves against Mathlib's own definition. No vendored
graph-theory definitions remain — `FC/` carries only the AP and geometry
files above.

## Transformation law (statement-preserving only)

1. `module` line removed; `public import` → `import`; `@[expose] public section`
   removed. **Declarations otherwise byte-identical.**
2. Internal imports `FormalConjecturesForMathlib.X` → `FC.X`.
3. Nothing else. Any semantic change would be a provenance violation.

## Statement files (the official statements of record)

- `problem61-erdos-hajnal/DM61_Official.lean` — `IsErdosHajnalLowerBound`
  verbatim + the five official targets as spec (open core `erdos_61`; solved
  variants `erha89`, `bnss23`, `p5`, `c5`).
- `problem142-rk-asymptotic/DM142_Official.lean` — `r :=
  Set.IsAPOfLengthFree.maxCard` verbatim + the official targets as spec.
- `problem107-happy-ending/DM107_Official.lean` — `cardSet`, `f` verbatim +
  the three official `@[category test]` anchor proofs VERBATIM
  (`f_zero_eq`, `convexIndep_triple_of_not_collinear`, `f_three_eq`) — these
  anchors double as the faithfulness certificate for the vendored
  definitions — + the official targets as spec (open core `erdos_107`;
  solved variants `nonempty_cardSet`, `ersz_bounds`, `su_bound`,
  `hmpt_bound`).

The vendored copies `deepmind-comparator/DM_{61,107,142}.lean` are
byte-identical (diff empty) to `FormalConjectures/ErdosProblems/{61,107,142}.lean`
at 2207c54d — verified in W82.

## Proof-kernel law (W82 lanes)

Every proof kernel (DM*_Proof_*.lean):
1. declares its target with a byte-identical statement signature to the spec;
2. proves it COMPLETELY — no `sorry`, no hidden hypotheses, no `native_decide`
   with free variables, no OOM (campaign NO-OOM law: no `decide` on
   `∀ k < N` for N > 501);
3. imports the BOSS arsenal (`Arsenal.*`) and cites its laws by file:line
   (read-before-cite);
4. is verified by GitHub CI ONLY (kills.yml; NO local lake/lean).
