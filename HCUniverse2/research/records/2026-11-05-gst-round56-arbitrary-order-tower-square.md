# Round 56 — the arbitrary-order tower square and the infinite memory tower

Date: 5 November 2026, Asia/Calcutta. Base revision: `1740ee9`
(the Round 55 repair round 2: the over-peeling collapse and the defeq
numeral bridge; before it the Round 55 round `696cbe0` at base
`d257f15`). Branch: `research/gpt6-native-point-primitive-span-20261017`.

Operator order (the standing round order, verbatim essence): "NEW
FIELDS, NEW THEOREMS, GO" — issued in the same message as the
operator's Q2 verdict (Round 55's record, the campaign's terminal
state). This round is the standing order's execution: two new faces,
both exact algebraic identities over supplied data.

## Face 1 — THE ARBITRARY-ORDER TOWER SQUARE (the full curvature ladder at every order)

Round 55 unified the memory LAW at arbitrary order (the single law
`dφ_k + φ_k d + ∑ i + j = k − 1 φᵢφⱼ = K_k` at every `k < n`, the
explicit towers of Rounds 52–54 as its order-1, 2, 3, 4 instances).
The one explicit-to-general gap that remained was the SQUARE: Rounds
53–55 proved the curvature ladder explicitly at orders 2, 3, 4
(`D² = (0, K₁x, K₂x + K₁y, ...)`), and this round proves it at EVERY
order at once.

The tower differential `jetLDifferential` acts on the infinite jet
space `ℕ → V` (the parameter family `d + ∑ ε^(k+1) φ_k` on jets of
every level at once):

`D u j = d (u j) + ∑ i < j, φᵢ (u (j − 1 − i))`

**THE TOWER SQUARE LAW (`jetLDifferential_square_apply`)**: for every
level `j ≤ n`,

`D² u j = ∑ i < j, K_i (u (j − 1 − i))`

— the CURVATURE LADDER: every level of the tower sees the curvature
of every level below it; every memory tail is absorbed by its own
memory law; and the two cross tails cancel exactly into the
arbitrary-order law. The Rounds 53–55 explicit ladders are the
`j ≤ 2, 3, 4` instances of this one identity.

**THE TRIANGLE REINDEXING LAW (`sum_triangle_succ`)** — the
combinatorial heart: the two triangular indexings of the strict lower
triangle `{(p, q) : p + q ≤ j − 2}` (by the outer level and by the
first coordinate) compute the same sum. The cross-cancellation at
every level is one instance of this single identity — the same law
that appeared as the "two cross tails cancelling exactly" in the
explicit Rounds 53–55 proofs, now stated and proved once, for every
order.

Supporting theorems: the pointwise memory law (`memory_apply`), the
computation rule (`jetLDifferential_apply`), the level-zero instance
(`jetLDifferential_square_zero`: the square at the head is the flat
base's square — zero), **THE FLAT LADDER COLLAPSE**
(`flat_tower_square`: in a flat tower the square vanishes at every
level ≤ order), **THE CONCENTRATED-JET EXTRACTION**
(`curvature_of_square_zero`: if the square vanishes at every level,
every curvature carrier below the order vanishes — each carrier read
off the ladder's diagonal by the jet concentrated at level zero), and
**THE FULL FLAT CRITERION AT ARBITRARY ORDER**
(`square_zero_iff_flat`: the square vanishes at every level iff the
tower is flat — the complete extension of the Rounds 53–55 two-sided
flat criteria to every order at once).

## Face 2 — THE INFINITE MEMORY TOWER (`JetTowerInf`, five new fields)

The complete formal family `d + ∑_{k ≥ 0} ε^(k+1) φ_k`: the memory law
at EVERY order, with no bound. New fields: `base`, `base_square`,
`jet : ℕ → (V →ₗ[ℚ] V)`, `curv : ℕ → (V →ₗ[ℚ] V)`, and the unbounded
`memory` field (the law at every `k : ℕ`). Theorems:

* **THE TRUNCATION** (`toTowerL`): every infinite tower is an
  arbitrary-order tower at every finite order — the memory laws below
  the order are instances of the unbounded law.
* **FLATNESS TRUNCATES** (`flat_of_flat_inf`).
* **THE INFINITE FLAT-HEAD LAW** (`flat_head_inf`).
* **THE INFINITE FLAT-TOWER RECURSION**
  (`flat_memory_recursion_inf`): each order's memory forced by the
  lower orders' products, at every order without bound.
* **THE ORIGIN TOWER** (`originTower`, `originTower_isFlat`): every
  flat base `d` (with `d² = 0`) generates the trivial infinite memory
  tower — all memory jets zero, all curvature carriers zero: the
  ε-family is `d + 0` at every order, and the unbounded law holds
  trivially at every order.

## Scope discipline

All statements are exact algebraic identities over supplied data
(fourth-jet linear-map identities generalized to infinite jets, and
finite ℚ-linear-map sum identities), kernel-verified by the module's
own CI lane (`gst-fold-tower-square.yml`, runtime lib registration —
the committed lakefile untouched) on the pinned toolchain
`leanprover/lean4:v4.33.0-rc2` with Mathlib. Zero `sorry`, zero axiom
declarations, zero `native_decide`. THE KERNEL-VERIFICATION RECEIPT
(bound per the ledger-110 discipline): GitHub Actions run
42045006581 @ 5efafcdc — the lane GREEN, zero error lines, zero
sorryAx in the run's own artifact log, every theorem axiom receipt on
exactly the three standard Mathlib axioms (propext, Classical.choice,
Quot.sound); green after two repair rounds, both diagnosed from the
runs' own artifacts (the first run's ten dot-notation resolution
failures closed by moving the square-law block into the structure's
own namespace; the second run's four elaboration defects closed at
5efafcdc: the instantiated computation-rule chain landing every
expansion on term-identity, the concentrated-jet extraction's explicit
level argument, and the fully qualified truncation return type healing
the cascaded `intro` failure). The geometric identification of
the tower with actual cohomology stays hand-level; no original-X
algebraic-source existence is claimed, assumed, or concluded. The
campaign's terminal state is the operator's Q2 verdict (Round 55's
record); the remaining falsifiable line of the prior sessions'
discipline (the single law FS) is recorded as standing at the
operator's adjudicated basis.
