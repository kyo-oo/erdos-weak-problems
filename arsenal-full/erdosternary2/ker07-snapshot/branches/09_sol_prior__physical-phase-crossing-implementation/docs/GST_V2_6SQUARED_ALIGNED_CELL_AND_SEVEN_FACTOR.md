<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0745 / 1132
<!--    Path         : branches/sol_physical-phase-crossing-implementation/docs/GST_V2_6SQUARED_ALIGNED_CELL_AND_SEVEN_FACTOR.md
<!--    Ref          : origin/sol/physical-phase-crossing-implementation
<!--    First-commit : 2026-08-17 03:19:46 +0530  (24bc230)
<!--    Last-commit  : 2026-08-17 03:19:46 +0530  (24bc230)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 03:19:46 +0530  24bc230  (ker07-dev)
<!--        Record 6-squared aligned GST cell and canonical factor seven
<!-- ====================================================================== -->

# GST Graph V2 — The 6²-Aligned Cell and the Canonical Factor 7

## Status

This note records exact arithmetic discovered by grouping the GST graph at the genuine equal 2-adic/3-adic microscopic scale. It does **not** claim the global prefix-one crossing is proved.

No global mirror, terminal NULL, unrestricted affine lift, or hidden exclusion theorem is used.

---

## 1. The correct equal-scale microscopic GST cell

One physical horizontal GST step multiplies by `4=2²`.

To match that binary valuation on the vertical ternary axis, group **two** ternary rows, whose radix is `9=3²`.

Let

- incoming carry `C` satisfy `0 ≤ C < 4`,
- two-trit input block `w` satisfy `0 ≤ w < 9`.

The exact two-row multiply-by-four law is

`C + 4*w = e + 9*C'`

with

`e = (C+4*w) % 9`,
`C' = (C+4*w) / 9`.

There are exactly

`4 * 9 = 36 = 6²`

legal local states.

Thus the first literal equal-valuation GST block is a **6²-state cell**.

---

## 2. Aligned re-coordinate mass law

Define the block mass

`m = C + 4*w`, so `0 ≤ m ≤ 35`.

The opposite coordinate reading of the same block is `(C',e)`. Its mass is

`m' = C' + 4*e`.

Since

`m = e + 9*C'`,

one gets

`m' = C' + 4*(m-9*C') = 4*m - 35*C'`.

Therefore

`boxed: m' ≡ 4*m (mod 35)`

with

`35 = 6² - 1`.

This is the aligned analogue of the microscopic mod-11 local rotation, but now the 2-adic and 3-adic scales are exactly matched.

---

## 3. Exact orbit decomposition

On the 36 legal states the aligned re-coordinate permutation has:

- fixed mass `0`;
- fixed mass `35`;
- cycles of lengths `2`, `3`, and `6` on the remaining masses.

The nonzero cycles that contain **no** Happy realization at either of the two ternary rows are exactly

`{7,28}`

and

`{14,21}`.

Together with zero, these are exactly the masses

`m ≡ 0 (mod 7)`

below `35`.

The maximum mass `35` is itself the fixed state

`(C,w)=(3,8)`.

Since `8=(22)_3`, this is an all-`22` GST+ Happy state.

Hence:

> among nonzero aligned 6² orbits, the only re-coordinate orbits that never realize a Happy block are the proper multiples of `7`.

Equivalently, every nonzero mass not divisible by `7` reaches a Happy realization under aligned subspace rotation.

This statement is finite and can be kernel-proved by explicit enumeration of the 36 states.

---

## 4. Why the number 7 is canonical, not accidental

For the canonical GST tower

`A_s = 4^(3^s) = 1 + 3^(s+1)*c_s`.

For every `s≥1`, the exponent `3^s` is divisible by `3`. Since

`4^3 = 64 ≡ 1 (mod 7)`,

one has

`A_s ≡ 1 (mod 7)`.

Therefore

`7 | (A_s-1)`.

Because `3^(s+1)` is invertible modulo `7`, division by `3^(s+1)` preserves divisibility by `7`, and therefore

`boxed: 7 | c_s` for every `s≥1`.

Since

`c_s = 1 + 3*z_s`,

we also get

`3*z_s ≡ -1 (mod 7)`,

hence

`boxed: z_s ≡ 2 (mod 7)`.

Together with the already-known `z_s ≡2 (mod3)`, this yields

`z_s ≡2 (mod21)`.

So the same prime `7` appears in two independently derived structures:

1. the unique proper no-Happy orbit divisor of the equal-scale 6² block;
2. the canonical LTE/c-tower coefficient `c_s` at every level.

This is an exact structural coincidence and is a serious candidate for the missing intersection mechanism.

---

## 5. Canonical deeper tails inherit the factor 7

For `t≥1`, every canonical Navigation constant has repunit form

`Q_t(n) = c_t*(1 + A_t + ... + A_t^(n-1))`.

Hence

`7 | Q_t(n)`

for every positive `n`.

In the prefix-one phase

`X_s(n)=z_s+A_s*Q_(s+1)(n)`,

we have

`A_s ≡1 (mod7)`,
`Q_(s+1)(n) ≡0 (mod7)`,
`z_s ≡2 (mod7)`.

Therefore

`boxed: X_s(n) ≡2 (mod7)`.

Its microscopic seed-one output is

`1+4*X_s(n)`,

and

`1+4*2 = 9 ≡2 (mod7)`.

Thus

`boxed: 1+4*X_s(n) ≡ X_s(n) ≡2 (mod7)`.

So the input and output of the hard seed-one wave occupy the same canonical residue `2 mod7`.

This condition is absent from the smallest unrestricted affine counterexamples, although divisibility/residue modulo 7 alone is not sufficient to prove the theorem: explicit noncanonical bad affine controls satisfying the same mod-7 conditions exist.

Therefore factor 7 is a genuine coordinate, not a standalone separator.

---

## 6. Two-row block evolution of the shared high endpoint

Write the shared carrier at row `q` as

`S_q = W_q + A*C_q`,

with

`0 ≤ W_q < A`, `0 ≤ C_q < 4`.

Let

`w_q = (T/3^q) % 9`

be the next two child ternary digits as a base-nine block.

The exact two-row carrier recurrence is

`S_(q+2) = (S_q + 4*A*w_q)/9`.

Write

`C_q + 4*w_q = e_q + 9*C_(q+2)`

with `0≤e_q<9`.

Then

`S_(q+2)
 = (W_q + A*(C_q+4w_q))/9
 = A*C_(q+2) + (W_q + A*e_q)/9`.

Because `W_q<A` and `e_q<9`,

`(W_q+A*e_q)/9 < A`.

Therefore the high/top carry coordinate evolves **exactly** by the 36-state aligned transducer:

`boxed: C_(q+2) = floor((C_q+4*w_q)/9)`.

The companion high remainder remains below `A` and retains the rest of the shared information.

This is a physical block-scale statement, not merely a formal re-coordinate orbit.

---

## 7. Block-Happy classification

A 6² block `(C,w)` is called Happy if either of its two microscopic ternary rows contains a GST Happy Gate.

Writing

`w=d0+3*d1`,

this means either

- `d0=2` and `C∈{0,3}`, or
- after the first row, `C1=floor((C+4*d0)/3)`, one has `d1=2` and `C1∈{0,3}`.

The finite aligned-orbit classification above shows:

- every proper nonzero mass not divisible by `7` belongs to an orbit containing such a Happy state;
- masses `7,14,21,28` belong to the only non-Happy nonzero re-coordinate orbits;
- mass `35` is fixed and Happy.

This is a much sharper BIG2 species decomposition at the equal 2/3 scale than the earlier microscopic mod-11 five-cycle.

---

## 8. What remains to turn the factor-7 phenomenon into the final theorem

The finite orbit result concerns **all aligned subspace readings of one 6² cell**. The comparator theorem needs a Happy realization in the **physical phase-one orientation**.

Therefore it is not legitimate to say:

`mass not divisible by7 -> parent physical gate`.

That would repeat the old global-mirror mistake.

The missing bridge must prove one of the following from the canonical pure-power geometry:

1. at the `6^k` intersection, the relevant aligned subspace reading coincides with the physical phase-one orientation; or
2. the canonical factor-7 residue forces a transition between the proper `7`-multiple no-Happy orbits and the nonzero fixed/Happy sector; or
3. under the nested `F_s^3(3Y)=3F_(s+1)(Y)` renormalization, indefinite avoidance of the physical Happy orientation would require an infinite chain of proper `7`-multiple aligned masses incompatible with the finite canonical origin.

The arithmetic coincidence `7 | c_s` means this route is no longer speculative numerology; the same divisor is present in both the canonical tower and the exact equal-scale V2 orbit structure.

But the orientation/intersection implication must still be explicitly derived before claiming closure.