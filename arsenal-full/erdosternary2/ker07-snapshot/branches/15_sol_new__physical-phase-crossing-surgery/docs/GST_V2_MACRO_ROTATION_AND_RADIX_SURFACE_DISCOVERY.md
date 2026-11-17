<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0729 / 1132
<!--    Path         : branches/sol_physical-phase-crossing-surgery/docs/GST_V2_MACRO_ROTATION_AND_RADIX_SURFACE_DISCOVERY.md
<!--    Ref          : origin/sol/physical-phase-crossing-surgery
<!--    First-commit : 2026-08-17 02:37:31 +0530  (6eb4d2c)
<!--    Last-commit  : 2026-08-17 02:37:31 +0530  (6eb4d2c)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 02:37:31 +0530  6eb4d2c  (ker07-dev)
<!--        Record GST V2 macro rotation and radix-surface discovery
<!-- ====================================================================== -->

# GST Graph V2 — Macro Rotation and Radix Surface Discovery

## Status

This is a mathematics research ledger, not a proof-complete claim. The monolith remains frozen. No `sorry`, axiom, global mirror, terminal-NULL rule, unrestricted affine lift, or residual-Ω termination is introduced.

The purpose of this note is to record exact identities discovered after `GST_V2_PHYSICAL_CROSSING_MATH_LEDGER.md`, plus the experiments that distinguish the canonical pure-power state from false unrestricted affine states.

---

## 1. One horizontal row is literal long division by 3

Fix a phase width `N` and put

- `A = 4^N`,
- `S_q = gstAffineMulCarryS (4*A) (1+4*z) T q`,
- `r_q = gstDigitS T q`.

The already-green shared-information recurrence is

`S_(q+1) = (S_q + 4*A*r_q) / 3`.

Because `4*A = 4^(N+1)`, write `S_q` in base four using exactly `N+1` digits

`[C_0, C_1, ..., C_N]_4`,

where the existing carry-word bridge identifies `C_i` with the horizontal GST carry at column `i` of the physical power rectangle.

Then

`S_q + 4^(N+1) * r_q`

is the base-4 word

`[r_q, C_0, C_1, ..., C_N]_4`.

Dividing this word by `3` by ordinary long division reproduces the entire GST row:

- the successive division remainders are the ternary digits
  `d_0, d_1, ..., d_(N+1)` across the row;
- the quotient base-4 digits are the next-row carries
  `C'_0, ..., C'_N`;
- the final quotient is exactly `S_(q+1)`.

At one microscopic cell the division step is precisely

`C_i + 4*d_i = d_(i+1) + 3*C'_i`.

Therefore a Happy Gate at horizontal edge `i` is exactly the remainder collision

`d_i = 2` and `d_(i+1) = 2`.

The child gate is a `22` collision at the left boundary. The target parent gate is a `22` collision at the right phase boundary.

This makes GST Graph V2 an exact base-4/base-3 radix-conversion tableau, not a metaphorical wave diagram.

---

## 2. Horizontal digit formula from the carry word

Because `4 ≡ 1 (mod 3)`, the row remainder recurrence is

`d_(i+1) = (d_i + C_i) mod 3`.

Hence

`d_i = (r_q + Σ_{j < i} C_j) mod 3`.

In particular:

- left Happy Gate:
  `r_q = 2` and `C_0 ∈ {0,3}`;
- right Happy Gate:
  `d_N = 2` and `C_N ∈ {0,3}`.

Equivalently, since a good carry `0` or `3` is `0 mod 3`, the right gate can also be read as

`d_(N+1)=2` and `C_N ∈ {0,3}`.

So both boundary gates have the same form: a remainder `2` entering a boundary digit whose carry digit is in the good sector.

---

## 3. Exact macro mixed-radix rotation

The shared carrier has two decompositions

`S = W + A*C = D + 4*Z`,

with

- `C < 4` = child/left carry,
- `W < A` = high remainder,
- `D < 4` = parent/right carry,
- `Z < A` = base-4 quotient.

Define the macro rotation on the carrier integer

`rho_A(S) = S/4 + A*(S % 4)`.

For `A=4^N` and `0 ≤ S < 4*A`, this is literally a cyclic rotation of the `N+1` base-4 digits of `S`: the least-significant carry digit is moved to the most-significant position.

If

`S = [C_0,C_1,...,C_N]_4`,

then

`rho_A(S) = [C_N,C_0,C_1,...,C_(N-1)]_4`.

Therefore

`rho_A^(N+1)(S) = S`.

This is an exact finite global subspace cycle of the shared information word.

---

## 4. The first macro rotation is exactly the physical parent boundary

Let the current child digit be `r` and define

`D = S % 4`,
`Z = S / 4`,
`r' = (Z + r) % 3`.

The existing theorem `gst_parent_digit_from_informationS` gives exactly this `r'` as the parent input digit.

Also `rho_A(S) = Z + A*D`, and because `Z < A`, the most-significant base-4 digit of `rho_A(S)` is exactly `D`.

Thus the macro re-coordinate

`(S,r) -> (rho_A(S), (S/4+r)%3)`

sends the left boundary state

`(child carry C, child digit r)`

to the physical right boundary state

`(parent carry D, parent digit r')`

in one step.

This is a genuine global re-coordinate law. It is not an assumed mirror.

The remaining `N` cyclic rotations are alternate/subspace readings of the same shared carry word; only the first rotation is automatically the physical phase-one boundary.

---

## 5. Combined macro state has a full cycle

Cyclic base-4 rotation preserves the sum of the base-4 digits modulo three, hence preserves

`σ = S % 3`.

Under one macro rotation, if the moved least-significant digit is `D_j`, the phase digit updates by

`r_(j+1) = r_j + σ - D_j (mod 3)`.

During one full `N+1`-rotation cycle each base-4 digit is moved exactly once. Their sum is `σ mod 3`. Therefore the total phase increment is

`(N+1)*σ - σ = N*σ (mod 3)`.

For the canonical phase width `N=3^s` with `s≥1`, one has `N ≡ 0 (mod 3)`. Hence

`r_(N+1) = r_0`.

So the combined `(shared carry word, phase digit)` macro state returns after a complete `N+1` subspace circuit.

This is the first exact global subspace-period law obtained directly from the physical carry word.

---

## 6. Why this does not by itself prove phase crossing

A child Happy Gate means macro subspace index `0` is Happy.

The desired parent gate means macro subspace index `1` is Happy.

The macro cycle guarantees return to index `0`, but it does not force index `1` to be Happy. Explicit false affine examples show that the Happy state may live only in other subspace indices and then drain away.

Therefore the missing theorem is not cyclicity alone. The canonical pure-power/origin condition must control how Happy/BIG2 subspace indices evolve when the vertical radix division advances from row `q` to row `q+1`.

---

## 7. Canonical-vs-false-affine control experiment

At `s=1`:

- `A=64`,
- `z=2`.

The unrestricted affine tail `T=2` is a concrete counterexample to generic reflection:

- child seed-zero has an immediate NULL Happy Gate at row `0`;
- parent `X=2+64*2=130` with seed one has no Happy Gate.

In the macro subspace cycle at the child-gate row, Happy indices exist away from the physical parent index; after the input `T=2` is exhausted, the zero tail lets those alternate/subspace Happy states drain without ever reaching physical parent index `1`.

By contrast the canonical child `T=Q_2(2)` begins with the same child digit-two event, but consuming the origin trit leaves a nontrivial canonical offset generated by the `c`-tower/pure-power recurrence. Subsequent vertical rows regenerate the shared word and the physical parent index does acquire a Happy Gate.

Therefore the exact missing content is now sharpened to:

> the canonical residual offset cannot drain through the macro subspace cycle in the same way as an arbitrary finite affine tail.

This is much narrower than unrestricted affine reflection.

---

## 8. The three phase strips glue into one radix surface

The already-green phase micro-output identities show the three phase strips share their boundary waves exactly:

- phase 0 boundary: `T -> 4T`,
- phase 1 boundary: `H1 -> 1+4H1`,
- phase 2 boundary: `H2 -> 2+4H2`,
- wrapped phase 0 boundary: `H0next -> 4H0next`.

The right microscopic output wave of the `0->1` strip is the left microscopic wave of the `1->2` strip. The same is true for `1->2` and `2->0`.

Thus the phase cycle is one glued three-sector radix surface, not three independent affine equations.

CREATE / DESTROY / SURVIVE events can therefore be interpreted as reroutings on one coupled surface while the shared carrier remains one integer.

---

## 9. Current research target after this discovery

The next theorem should not be another conservation identity. It must be an exclusion/intersection statement.

A useful exact interface is:

> Along a canonical origin-driven vertical evolution of the shared carrier, if macro subspace index `0` ever realizes a Happy/BIG2 state and macro index `1` is assumed never Happy, the canonical residual offset must be forced into an impossible origin/subspace configuration.

Equivalent physical form:

> A canonical pure-power radix surface cannot route a left-boundary `22` collision forever through alternate macro subspaces while avoiding the physical phase-one boundary.

The candidate mechanisms now worth testing are:

1. **origin-trit / macro-index coupling:** determine the exact update of the Happy subspace index when one canonical origin trit is consumed;
2. **three-sector gluing:** if phase-one is bad, prove CREATE/DESTROY rerouting enters the adjacent phase sector in a form that strictly changes the canonical origin state;
3. **scale intersection:** combine the macro subspace cycle with the `v3-v2` equal-scale coordinate only after the actual subspace update law is known.

Do not resurrect same-row transport, terminal NULL, fixed synchronizer length, or unrestricted affine reflection.