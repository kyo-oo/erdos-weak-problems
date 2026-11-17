<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0722 / 1132
<!--    Path         : branches/sol_physical-phase-crossing-surgery-plan/docs/GST_V2_PHYSICAL_CROSSING_MATH_LEDGER.md
<!--    Ref          : origin/sol/physical-phase-crossing-surgery-plan
<!--    First-commit : 2026-08-17 01:57:16 +0530  (9ef3a73)
<!--    Last-commit  : 2026-08-17 01:57:16 +0530  (9ef3a73)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 01:57:16 +0530  9ef3a73  (ker07-dev)
<!--        Record exact GST V2 physical crossing mathematics
<!-- ====================================================================== -->

# GST Graph V2 — Physical Crossing Mathematics Ledger

## Status discipline

This note records the mathematical frontier only. It does **not** claim the prefix-one lift, the residual Navigation lift, or the Erdős theorem is proved. Every item is classified as exact algebra, experimental evidence, disproved shortcut, or remaining theorem.

No global mirror, terminal-NULL principle, unrestricted affine lift, or residual-Ω termination is used.

---

## 1. Exact canonical phase rectangle

Fix `s ≥ 1`, put

- `N = 3^s`,
- `D = 3^(s+1)`,
- `M = 3*D = 3^(s+2)`,
- `A = 4^N = 1 + D*c`,
- `c = 1 + 3*z`,
- `K = 3^(s+1)*n`,
- `E_i = 4^(K+i)`.

For every horizontal column `i`, write uniquely

`E_i = P_i + M*H_i`, with `0 ≤ P_i < M`.

Then

`P_{i+1} = (4*P_i) mod M`,

`H_{i+1} = 4*H_i + floor(4*P_i/M)`.

At the left phase boundary,

`P_0 = 1`, hence `floor(4*P_0/M)=0`, and

`H_0 = Q(s+1,n)`.

At the phase-one boundary `i=N`, LTE gives

`P_N = 1 + D`,

and therefore

`floor(4*P_N/M)=1`.

Thus column `0` is exactly the seed-zero child wave and column `N` is exactly the seed-one parent wave. The prefix-one theorem is therefore a physical statement inside one rectangle of **consecutive perfect powers**, not an arbitrary affine statement.

---

## 2. Exact local GST cell

At horizontal column `i` and ternary row `p`, let

`d_{i,p}` be the current ternary digit and `C_{i,p}` the horizontal multiply-by-four carry.

Every cell satisfies

`C_{i,p} + 4*d_{i,p} = d_{i+1,p} + 3*C_{i,p+1}`.

Equivalently the local map is

`(C,d) ↦ ((C+4d)/3, (C+4d)%3)`.

This is the V2 local re-coordinate map. It is local; it is **not** a global GST+/ALT− mirror.

---

## 3. BIG2 local orbit — exact mod-11 identity

Define the local cell mass

`m = C + 4*d ∈ {0,...,11}`.

Under one local V2 re-coordinate, the new mass obeys

`m' ≡ 4*m (mod 11)`.

The state permutation has two fixed masses `0,11` and two five-cycles:

- `{1,3,4,5,9}`,
- `{2,6,7,8,10}`.

The second five-cycle is exactly the set of nonzero quadratic nonresidues modulo `11`. Together with the fixed SURVIVE mass `11`, it is precisely the existing V2 BIG2 species

`{2,6,7,8,10,11}`.

For the NULL Happy Gate `(C,d)=(0,2)`, the exact cycle is

`(0,2) → (2,2) → (3,1) → (2,1) → (2,0) → (0,2)`

with masses

`8 → 10 → 7 → 6 → 2 → 8`.

Its event realization is

`SURVIVE → DESTROY → NEITHER → NEITHER → CREATE → SURVIVE`.

Thus CREATE/DESTROY/SURVIVE are different local realizations of the same BIG2 orbit. This is an exact local statement. It does **not** by itself transport BIG2 between distinct physical cells.

---

## 4. One shared carrier contains the whole coupled state

For the prefix-one affine square, define at row `q`

`S_q = affineCarry(4*A, 1+4*z, T, q)`.

The existing information identities give two exact decompositions

`S_q = D_q + 4*Z_q = W_q + A*C_q`.

Therefore:

- `S_q % 4 = D_q` is the parent seeded carry,
- `S_q / 4 = Z_q` is the low affine quotient,
- `S_q % A = W_q` is the high remainder,
- `S_q / A = C_q` is the child carry,
- `0 ≤ S_q < 4*A`.

The vertical recurrence is exactly

`S_{q+1} = (S_q + 4*A*r_q)/3`,

where `r_q = digit(T,q)`.

This is already represented by the green information-state recurrence.

---

## 5. Carry word = base-4 digits of the shared carrier

The existing carry-word bridge proves that `S_q` is literally the horizontal carry word through the `N+1` consecutive ×4 columns of the phase rectangle.

If

`C_{0,q}, C_{1,q}, ..., C_{N,q}`

are the horizontal carries at row `q`, then the base-4 expansion of `S_q`, from most significant to least significant, is exactly

`[C_{0,q}, C_{1,q}, ..., C_{N,q}]_4`.

Consequently the vertical recurrence has a concrete radix interpretation:

prepend the child ternary digit `r_q` to that base-4 carry word and perform long division by `3`.

The successive division remainders are exactly the ternary digits across the horizontal power row, and the quotient base-4 digits are exactly the carries in the next vertical row.

So GST Graph V2 is an exact base-3/base-4 radix-conversion tableau of one shared information word.

---

## 6. Origin trits are the three phase subspaces

Let `Q_s(b)` denote the canonical Navigation constant. For `r ∈ {0,1,2}` the canonical origin recurrence gives

`Q_s(3*n+r) = Q_s(r) + 3*A_s^r*Q_{s+1}(n)`.

Since `Q_s(r) ≡ r (mod 3)`, write

`Q_s(3*n+r) = r + 3*H_r(s,n)`.

After stripping the first ternary graph row, the incoming GST carry seed is exactly `r`, and the remaining word is `H_r(s,n)`.

Therefore the three phase seeds `0,1,2` are literally the first ternary origin trit. Repeating the recurrence produces nested phase addresses indexed by the full ternary origin prefix. This is the precise arithmetic meaning of the infinitely nested V2 subspaces.

The hard prefix-one theorem is exactly the `r=1` phase lift.

---

## 7. Why the canonical restriction is indispensable

An unrestricted affine theorem

`seed-0 gate in T  ⇒  seed-1 gate in z + A*T`

is false for **every** level `s`.

Let `A=4^(3^s)` and `z=(c_s-1)/3`. Since `c_s ≡ 7 (mod 9)`, one has `z ≡ 2 (mod 3)`. Also `A` is a power of two and `3` is invertible modulo `A`.

Choose `r` satisfying

`1 + 3*r ≡ z (mod A)`.

Let `h` be the multiplicative order of `3` modulo `A`, and define the finite ternary Cantor word

`X = 1 + Σ_{j=0}^{r-1} 3^(1+j*h)`.

All ternary digits of `X` are `0/1`, so the seed-one word `X` has no Happy Gate. But every summand `3^(1+j*h)` is congruent to `3` modulo `A`, hence

`X ≡ 1+3r ≡ z (mod A)`.

Thus `X=z+A*T` for a natural `T`. Modulo three,

`T ≡ X-z ≡ 1-2 ≡ 2 (mod 3)`, because `A ≡1 (mod3)`.

So `T` has an immediate NULL Happy Gate at row zero while `z+A*T` is completely gate-free.

This construction permanently forbids replacing the canonical pure-power theorem by an arbitrary affine lift.

It also explains why brute force at high `s` can miss affine counterexamples: the first constructed examples may be astronomically large.

---

## 8. The 6^k / scale-intersection coordinate

Equation 11 in Boss's equation set is

`Σ(x) = v3(x) - v2(x)`.

Its zero set is the equal-valuation locus `6^k*m` with `gcd(m,6)=1`.

For the physical GST lattice, a horizontal ×4 step contributes two powers of `2`, while one ternary vertical scale contributes one power of `3`. Thus the equal-scale diagonal is represented by

`vertical depth = 2 * horizontal exponent`.

This recovers the old bridge boundary `p=2k` for `4^k`, where the high carry vanishes because `4^(k+1) < 3^(2k)` for the relevant range.

Important: the bridge boundary alone does **not** force a Happy Gate. The old oscillation attempt failed precisely because a final carry-zero can occur after the last digit-two. The scale intersection must be coupled to the V2 information/subspace state; it cannot be used as a terminal-NULL shortcut.

---

## 9. Disproved / rejected shortcuts

The following were tested and must not be resurrected as proof premises:

1. same-row phase-0 → phase-1 gate transport;
2. a fixed mod-5 winding law between child and parent gate positions;
3. literal injection of the word `12102` into every mature canonical parent;
4. the 7/8 bad-language magnitude bound by itself;
5. Euclidean nearest-neighbor propagation of BIG2 cells;
6. one phase stride equals one local V2 rotation;
7. additive or parity edge charges depending only on carry/digit values;
8. `6^k` bridge carry-zero implies a zero occurs between relevant digit-twos;
9. unrestricted affine reflection;
10. terminal or absorbing NULL;
11. conservation identities treated as exclusion theorems.

The local BIG2 five-cycle remains valid; what fails is promoting it to a physical cross-rectangle transport without an additional intersection theorem.

---

## 10. Bad-prefix tree and finite-origin issue

Canonical causality makes the first `q` GST vertices depend only on the first `q` ternary origin trits. Hence the hypothetical bad canonical origins form an exact ternary prefix tree.

Because the canonical `Q_s` map is a 3-adic tree isometry, this bad-prefix tree has infinite non-natural 3-adic rays. Therefore there can be no universal fixed witness depth and no bounded local pattern that separates all canonical prefixes from arbitrary affine bad rays.

The required distinction is global:

- a natural origin has an eventually-zero ternary origin ray;
- a noncanonical affine counterexample pulls back to a genuinely infinite 3-adic origin ray.

Experiments show canonical finite prefixes can shadow bad rays for arbitrarily long depths before exiting, so a fixed synchronizer-length argument is not sufficient.

---

## 11. Stronger full-power observation

For the full-power cell `R=4^k`, exact computation through large ranges shows a common digit-two collision between `4^k` and `4^(k+1)` for every tested `k` except

`k = 1,2,3,4,7`.

This is the old `gst_four_power_creation_certificate_inline` target. Its old proof fails in the exact hard case where the highest input digit-two is destroyed with carry `1` or `2`, and the eventual `6^k` carry-zero occurs only after the last digit-two. No theorem is claimed here from the experiment.

A second experiment on the gate-free language shows unusually low 2-adic divisibility compared with pure powers. For exact ternary length `L`, observed maximal `v2` values include

- `L=9  -> max v2=14`, attained by exceptional `4^7`,
- `L=13 -> max v2=15`,
- `L=16 -> max v2=21`.

This suggests a possible scale/dimension route: prove a 2-adic growth bound for the GST bad language strictly below the extremal slope `log_2(3)` attained by powers of two. This remains an experimental research direction, not a proved bound.

---

## 12. Exact remaining mathematical theorem

The final missing statement must use **both** ingredients:

1. the physical consecutive-perfect-power / canonical-origin certificate;
2. the V2 shared-information dynamics.

A safe formulation is:

> A canonical eventually-zero origin cannot generate a phase-zero BIG2/SURVIVE occurrence while its phase-one boundary remains a complete seeded bad trace.

Equivalently, in the physical power rectangle,

> if the left boundary contains a SURVIVE cell, then the right phase-one boundary contains a SURVIVE cell.

The proof may allow the vertical position to move. It may not assume a same-row reflection.

The currently most promising two exact representations of this theorem are:

- **radix-tableau form:** use the base-4 carry word `S_q`, its divide-by-3 vertical evolution, and the pure-power boundary geometry;
- **scale-separation form:** combine the regular GST bad language with the extremal 2-adic geometry of a pure power at the `v2/v3` intersection.

Until one of these gives genuine exclusion, the mathematics is not complete and the monolith must remain frozen.
