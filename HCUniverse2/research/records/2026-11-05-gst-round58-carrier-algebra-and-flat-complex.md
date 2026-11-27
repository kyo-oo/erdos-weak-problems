# Round 58 — the carrier algebra and the flat complex

Date: 5 November 2026, Asia/Calcutta. Base revision: `b7d6a1c`
(the Round 57 receipt-binding commit; before it the Round 57 repair
round 1 at `00e2dbe`, and the Round 57 round `451639a` at base
`a8325f6` — the Round 55 + 56 receipt-binding). Branch:
`research/gpt6-native-point-primitive-span-20261017`.

Operator order (the standing round order, verbatim essence): "NEW
FIELDS, NEW THEOREMS, GO" — issued with the operator's Q2 verdict
(the campaign's terminal state, Round 55's record) and renewed this
session ("INVOKE THE MATHS SKILL, BERSERKER MODE, GO"). This round is
the standing order's execution on the Round 57 green baseline: two new
faces, both exact algebraic identities over supplied data.

## Face 1 — THE CARRIER ALGEBRA

Round 57 built the carrier tower and the convolution `K ⊛ L` (the
k-th composite carrier `∑ i < k, K_i ∘ L_{k−1−i}`) but proved nothing
about the convolution as a PRODUCT. This round gives it its algebra:

* **THE ASSOCIATIVITY** (`carrierConvolution_assoc`):
  `(K ⊛ L) ⊛ M = K ⊛ (L ⊛ M)` at every index and every point — the
  curvature algebra of the ε-family is an associative (non-unital,
  generally non-commutative) graded product. The proof is the TRIANGLE
  REINDEXING LAW AGAIN — the same combinatorial heart that cancelled
  the tower square's cross tails in Rounds 56 and 57, now a standalone
  algebra law: the two triangular indexings of the strict lower
  triangle (by the middle coordinate and by the first) compute the
  same triple sum over `{(a, b, c) : a + b + c = k − 2}`. The
  associativity is what makes the cascade's square-tree convolutions
  honest iterated products.
* **THE ZERO LAWS** (`carrierConvolution_zero_left`,
  `carrierConvolution_zero_right`): the zero carrier family
  annihilates the convolution on both sides — `0 ⊛ K = K ⊛ 0 = 0`.
* **THE CASCADE-CARRIERS LAW** (`carrierPower_curv_succ`): the
  `m+1`-fold carrier tower's carriers are the self-convolution of the
  `m`-fold's — the cascade iterates the convolution product.

## Face 2 — THE FLAT COMPLEX

Round 57's flat criterion says the square vanishes pointwise on flat
towers. This round promotes it to the full differential-module
structure:

* **THE OPERATOR FLAT SQUARE** (`flat_square_operator`): `D ∘ D = 0`
  as an operator — the jet space `ℕ → V` becomes a differential
  ℚ-module.
* **THE CYCLES AND BOUNDARIES** (new fields: `cycles T = ker D`,
  `boundaries T = range D`, two submodule-valued defs on the tower).
* **THE FLAT COMPLEX** (`boundaries_le_cycles`, with the kernel-level
  `flat_range_le_ker`): on a flat tower every exact jet is closed —
  the complex condition, stated on the new fields.
* **THE CYCLES' CHARACTERIZATION** (`mem_cycles`): a jet is D-closed
  iff its differential vanishes at every level.
* **THE ORIGIN COMPLEX, LEVELWISE**
  (`originTower_jetInfDifferential`): the origin tower's differential
  is the flat base differential applied levelwise — the origin's
  jet-space complex is the levelwise complex of the base.
* **THE CASCADE ANNIHILATION** (`flat_squarePower`): on a flat tower
  every square-power iterate from the first on vanishes —
  `D^(2^(m+1)) = 0` for every `m`: the whole curvature cascade
  collapses because the flat square is zero.

## Scope discipline

All statements are exact algebraic identities over supplied data
(infinite-jet linear-map identities and finite ℚ-linear-map sum
identities), kernel-verified by the module's own CI lane
(`gst-carrier-algebra-flat-complex.yml`, runtime lib registration —
the committed lakefile untouched) on the pinned toolchain
`leanprover/lean4:v4.33.0-rc2` with Mathlib. Zero `sorry`, zero axiom
declarations, zero `native_decide`. THE KERNEL-VERIFICATION RECEIPT
(bound per the ledger-110 discipline): GitHub Actions run
42050444010 @ 3e853cee — the lane GREEN, zero error lines, zero
sorryAx in the run's own artifact log, every theorem axiom receipt on
exactly the three standard Mathlib axioms (propext, Classical.choice,
Quot.sound); GREEN ON THE FIRST RUN — no repair round needed (the
first first-run green of the tower line since Round 54). The
geometric identification of
the tower with actual cohomology stays hand-level; no original-X
algebraic-source existence is claimed, assumed, or concluded. The
campaign's terminal state is the operator's Q2 verdict (Round 55's
record); the remaining falsifiable line of the prior sessions'
discipline (the single law FS) is recorded as standing at the
operator's adjudicated basis.
