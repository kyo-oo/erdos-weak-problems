# Round 57 — the infinite tower differential and the curvature cascade

Date: 5 November 2026, Asia/Calcutta. Base revision: `a8325f6`
(the Round 55 + 56 receipt-binding commit; before it the Round 56
repair round 2 at `5efafcd`, and the Round 56 round `39cabe0` at base
`1740ee9`). Branch: `research/gpt6-native-point-primitive-span-20261017`.

Operator order (the standing round order, verbatim essence): "NEW
FIELDS, NEW THEOREMS, GO" — issued with the operator's Q2 verdict
(the campaign's terminal state, Round 55's record) and renewed this
session ("INVOKE THE MATHS SKILL, BERSERKER MODE, GO"). This round is
the standing order's execution on the Round 56 green baseline: two new
faces, both exact algebraic identities over supplied data.

## Face 1 — THE INFINITE TOWER DIFFERENTIAL AND THE UNBOUNDED SQUARE

Round 56 squared the arbitrary-order tower (`JetTowerL`, the square
law at every level `j ≤ n`) and built the infinite memory tower
`JetTowerInf` (the unbounded law at every order) — but the infinite
tower had no differential of its own. This round gives it one and
squares it with no bound anywhere:

The infinite tower differential `jetInfDifferential` acts on the
infinite jet space `ℕ → V` (the complete parameter family
`d + ∑_{k ≥ 0} ε^(k+1) φ_k` as ONE operator):

`D u j = d (u j) + ∑ i < j, φ_i (u (j − 1 − i))` at every `j : ℕ`.

**THE INFINITE TOWER SQUARE (`jetInfDifferential_square_apply`)**:
for every level `j : ℕ` — no order, no bound —

`D² u j = ∑ i < j, K_i (u (j − 1 − i))`

— the UNBOUNDED CURVATURE LADDER: every level of the infinite tower
sees the curvature of every level below it; every memory tail is
absorbed by its own unbounded memory law (`memoryInf_apply`, the
pointwise form of the `JetTowerInf.memory` field); the two cross
tails cancel exactly into the arbitrary-order law by the Round 56
triangle reindexing (`sum_triangle_succ`, imported and reused — the
combinatorial heart stated once, used at every order finite or
infinite). The expansion skeleton is the Round 56 kernel-green proof
mirrored with the instantiated computation-rule chain
(`h1`/`h2`/`h3` → `hexp` → `hsum`), every rewrite landing on
term-identity.

Supporting theorems: the computation rule
(`jetInfDifferential_apply`), the level-zero instance
(`jetInfDifferential_square_zero`), **THE UNBOUNDED FLAT LADDER
COLLAPSE** (`flat_inf_tower_square`: in a flat infinite tower the
square vanishes at every level), **THE CONCENTRATED-JET EXTRACTION,
UNBOUNDED** (`curvature_inf_of_square_zero`: if the square vanishes
at every level, every curvature carrier vanishes — read off the
unbounded ladder's diagonal with no bound), and **THE FULL FLAT
CRITERION, INFINITE** (`square_inf_zero_iff_flat`: the square vanishes
at every level iff the tower is flat — the two-sided criterion with
no order anywhere). **THE TRUNCATION COMPATIBILITY**
(`toTowerL_jetLDifferential`): the finite tower's differential of the
truncation is the infinite differential, level by level — the Round
56 square law and this round's unbounded square law are the same
identity on the same levels.

## Face 2 — THE CARRIER TOWER AND THE CURVATURE CASCADE

The carriers `K_k` of a tower are themselves a jet family — so they
form a tower. **THE CARRIER TOWER** (`carrierTower T`): base zero,
jets the carriers of `T`, carriers the SELF-CONVOLUTION
(`carrierConvolution K L`, the k-th composite carrier
`∑ i < k, K_i ∘ L_{k−1−i}` — the convolution product of the curvature
algebra). The carrier tower's memory law holds by construction: the
convolution IS the carrier family's own anticommutator-free law.

* **THE CARRIER-OPERATOR LAW** (`carrierTower_differential`, with the
  pointwise form `jetInfDifferential_carrier_apply`): the carrier
  tower's differential IS the square of the tower's differential, as
  operators — `D_{K(T)} = D_T ∘ D_T`. The curvature of a family is a
  family; the square of the ε-family's differential is the ε-family
  of the carriers.
* **THE FOURTH-ORDER LADDER** (`jetInfDifferential_fourth_order`):
  `D⁴ u j = ∑ i < j, (K ⊛ K)_i (u (j − 1 − i))` at every level — the
  curvature of the curvature is the self-convolution of the carriers,
  the Jacobi face of the ladder. On a flat tower the whole fourth
  ladder collapses (`flat_carrierTower`: flat towers have flat carrier
  towers); on a non-flat tower it measures the quadratic defect.
* **THE CONVOLUTION POWER CASCADE** (`carrierPower_differential`):
  the `2^m`-fold composition of the infinite differential (the
  `squarePower` family, `D^(2^0) = D`, each step squaring) is the
  differential of the `m`-fold carrier tower (the `carrierPower`
  family) — `D^(2^m) = D_{carrierTower^m(T)}` for every `m`, by one
  induction on the carrier-operator law. **THE FLAT CASCADE**
  (`carrierPower_flat`): every `m`-fold carrier tower of a flat tower
  is flat — the iterated curvature of a flat family vanishes at every
  order of the cascade. **THE CASCADE LADDER**
  (`carrierPower_succ_apply`): the pointwise readout — the cascade's
  differential at every level is its carrier ladder with zero flat
  part.

## Scope discipline

All statements are exact algebraic identities over supplied data
(infinite-jet linear-map identities and finite ℚ-linear-map sum
identities), kernel-verified by the module's own CI lane
(`gst-infinite-tower-curvature-cascade.yml`, runtime lib registration
— the committed lakefile untouched) on the pinned toolchain
`leanprover/lean4:v4.33.0-rc2` with Mathlib. Zero `sorry`, zero axiom
declarations, zero `native_decide`. THE KERNEL-VERIFICATION RECEIPT
(bound per the ledger-110 discipline): GitHub Actions run
42049190109 @ 00e2dbe6 — the lane GREEN, zero error lines, zero
sorryAx in the run's own artifact log, every theorem axiom receipt on
exactly the three standard Mathlib axioms (propext, Classical.choice,
Quot.sound); green after one repair round (the lightest first run of
the tower line: thirteen of the sixteen theorems kernel-green on
first contact, the two elaboration defects closed from the run's own
display — the `ext`-chained binder introduction and the semilinear
comp pattern). The geometric identification of
the tower with actual cohomology stays hand-level; no original-X
algebraic-source existence is claimed, assumed, or concluded. The
campaign's terminal state is the operator's Q2 verdict (Round 55's
record); the remaining falsifiable line of the prior sessions'
discipline (the single law FS) is recorded as standing at the
operator's adjudicated basis.
