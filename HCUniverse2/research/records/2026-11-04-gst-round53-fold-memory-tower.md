# Round 53 — the second-order memory tower and the composed-fold transport law

Date: 4 November 2026, Asia/Calcutta. Base revision:
`373ce291` (branched from `28cae9e7`, the Round 52 continuation head;
the kernel-verification receipt: GitHub Actions run 41838379639 —
"Build completed successfully (8698 jobs)", zero sorryAx, all sixteen
theorems on the three standard Mathlib axioms only).
Branch: `research/gpt6-native-point-primitive-span-20261017`.

Operator order (verbatim essence): "NO, THIS IS NOT MATHS SKILL, AWAKEN
CORRECTLY + MANY THINGS HAPPEND IN THE BRANCH, MAKE IT ALL LEAN CI GREEN!!
GO NEW FIELS, NEW THEOREMS". Round 52 took CI ownership of the fold/
curvature series and banked the fourteen-module spatial-fold lane green;
this round extends the mathematical content one level up while the two
deep classical-Hodge lanes (sheet, krylov) are being made green by the
cache-warming infrastructure of the same session.

## The two new faces

All statements are exact algebraic identities over supplied data
(ℚ[t] polynomial identities and second-jet linear-map identities),
kernel-verified by GitHub Actions (run 41838379639 @ 373ce291) on the pinned toolchain
`leanprover/lean4:v4.33.0-rc2` with Mathlib
`51e6992efd06126df61a496bebf8f49482a4e129`. Zero `sorry`, zero axiom
declarations, zero `native_decide`. The geometric identification of the
tower or the composed fold with actual cohomology stays hand-level; no
original-X algebraic-source existence is claimed, assumed, or concluded.

### Face 1 — `JetTower` (eight fields: five carried over from Round 52's
`JetFamily` plus three new)

The parameter family `d + ε·φ + ε²·χ` of the specialization-memory route
acts on second jets `(x, y, z)` (standing for `x + ε·y + ε²·z`) by
`towerDifferential (x, y, z) = (dx, dy + φx, dz + χx + φy)`.

New fields: `second` (the second memory jet `χ`, the ε²-coefficient),
`second_curvature` (the second-order curvature carrier `K₂`), and
`second_memory` (the second-order memory law `dχ + χd + φ² = K₂` — the
ε²-curvature of the family retains both the new anticommutator and the
square of the first memory jet).

Theorems (all kernel-verified):

1. `towerDifferential_apply` — the pointwise second-jet action.
2. `tower_square_zeroth` — the zeroth jet of the tower square is zero
   (exact flatness at `ε = 0`).
3. `tower_square_first` — **the curvature is retained one level up**: the
   first jet component of the tower square is exactly `K₁x`; Round 52's
   specialization memory survives the tower extension unchanged.
4. `tower_square_second` — **the first curvature propagates to the top
   level**: the second jet component of the tower square is exactly
   `K₂x + K₁y`; every level of the tower sees the curvature of the level
   below, with the memory tail `φ²` absorbed into `K₂` by the
   second-order memory law.
5. `tower_square` — the full tower square as one identity:
   `D²(x,y,z) = (0, K₁x, K₂x + K₁y)`.
6. `tower_flat_face` — the flat `ε = 0` face of the tower: on the
   pure-ε² fiber the tower differential is the flat base differential,
   both memory fields still carrying the full curvature data.
7. `tower_flat_of_curvatures_zero` — the flat-tower criterion,
   sufficiency: both curvature levels vanishing identically squares the
   tower to zero on every second jet.
8. `curvature_of_flat_tower` / `second_curvature_of_flat_tower` — the
   flat-tower criterion, both extraction directions: a tower that squares
   to zero forces both curvature carriers to vanish identically (the
   second extraction uses the first to clear the transported term).

### Face 2 — `FoldComposition` (nine fields) plus the freed conservation law

Round 52's conservation law is first freed of its record fields as the
universal identity `conservationOf`: for every base `P`, cup rank `R` and
shift `s`, `(1+t^s)²P = foldOf(P,R,s) + lossOf(R,s)` — the cancellation
`t^(s+1) + t^s = t^s(1+t)` is exact for all inputs.

New fields: `base`, `cup`, `cup2` (the second cup rank polynomial
`R'_β`), `shift`, `shift2` (the two fold shifts `s = 2p−1`, `s' = 2q−1`),
`shift_pos`, `shift2_pos`, `cup_zero`, `cup2_zero` (the two degree-zero
cup rank normalizations).

Theorems (all kernel-verified):

1. `double_conservationOf` / `double_conservation` — **the exact double
   conservation law**: `(1+t^s')²(1+t^s)²P = double-fold + total-loss`,
   where the total loss is the second fold's own loss
   `t^s'(1+t)(1+t^s')R'` plus the first fold's loss transported by the
   second flat factor `t^s(1+t^s')²(1+t)(1+t^s)R` — the composed-fold
   transport law, proved by iterating the single-fold conservation twice
   with an explicit `calc` chain.
2. `total_loss_below_min` — **no loss below either shift**: the total
   loss polynomial has no support below `min(s, s')`.
3. `double_fold_unchanged_below_min` — the double fold equals the double
   flat exactly in every degree below both shifts.
4. `double_first_loss` — **the composed first lost degree is the first
   shift with loss exactly one** (when `s < s'`): the leading term of the
   total loss is the transported first loss, undisturbed by the second
   fold.
5. `double_degree_one_blind` — **the composed degree-one blindness law**:
   at codimensions `p, q ≥ 2` (shifts `2p−1`, `2q−1`) the total loss has
   no degree-one term; the degree-one curvature test alone cannot see any
   composed `p, q ≥ 2` fold, and the first detecting degree is exactly
   `min(2p−1, 2q−1)`.

## Scope discipline

The tower and the composition are bookkeeping structures over supplied
rank and family data, in the exact register of Round 52. The module
imports only `Mathlib` and `GSTAllDegreeCurvatureMemory`; it is compiled
by its own lane `gst-fold-memory-tower.yml` with runtime lib registration
(the deep-lane pattern — the closure generator appends the module's lib
at CI time), so no committed-lakefile change was needed and no other
lane's trigger surface was disturbed.

The remaining falsifiable line for Q2 is unchanged in strength: the
single law FS. Nothing here claims, assumes, or concludes any
original-X algebraic-source existence.
