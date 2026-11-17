<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #1102 / 1132
<!--    Path         : branches/sol_5c579-final-bigN-right-chord-atomic/docs/GST_V2_BASE6_BRIDGE_UNIVERSE_AND_TRUE_K1_RESIDUAL.md
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

# GST Graph V2 — Base-6 Bridge Universe and the True k=1 Residual

## Status discipline

Exact algebraic discoveries only. No final prefix-one theorem is claimed here. No global mirror, no terminal NULL, no legacy residual-Omega activation, and no heuristic classifier is used as a proof premise.

---

## 1. The fundamental GST bridge cell is a 6-state x2/base-3 cell

Before multiplication by four, factor it as two consecutive multiplications by two.

For one multiplication-by-two cell in base three, let

- `a ∈ {0,1}` be the incoming binary carry;
- `d ∈ {0,1,2}` be the input ternary digit;
- `e ∈ {0,1,2}` be the output ternary digit;
- `a' ∈ {0,1}` be the next binary carry.

The exact cell equation is

`a + 2*d = e + 3*a'`.

There are exactly

`2*3 = 6`

possible input states `(a,d)`.

Define the microscopic bridge mass

`m = a + 2*d ∈ {0,...,5}`.

The opposite reading is `(a',e)`, with

`m = e + 3*a'`.

Thus one state has two exact mixed-radix decompositions, a `2×3` reading and a `3×2` reading.

This is the elementary 2-world/3-world bridge cell.

---

## 2. Multiplication by four is two bridge layers

A GST multiplication-by-four cell is the composition of two multiplication-by-two bridge cells.

Let the two binary carries be `a,b ∈ {0,1}`. The ordinary GST carry is exactly

`C = 2*a + b`.

Hence the four GST carry states are literally the two-bit binary words

`00,01,10,11`.

The three GST spaces become:

- `NULL = 00`;
- `ALT− = 01 or 10`;
- `GST+ = 11`.

This gives a literal binary geometry for the three GST spaces.

For the normalized ternary prefix

`x_p = (R mod 3^p)/3^p ∈ [0,1)`,

the two binary bits are

`a_p = floor(2*x_p)`,

`b_p = floor(2*{2*x_p})`,

and

`gstCarry(R,p) = floor(4*x_p) = 2*a_p+b_p`.

Therefore a digit-two vertex is Happy exactly when its two bridge bits agree:

`d_p=2 and a_p=b_p`.

It is bad at a digit-two vertex exactly when

`d_p=2 and a_p≠b_p`.

Equivalently, at a bad digit-two position,

`x_p ∈ [1/4,3/4)`.

The good spaces NULL/GST+ are the two outer binary quarters; ALT− is the middle binary half.

---

## 3. Microscopic x2 bridge mass has a closed pure-power formula

For the power column `2^n` and ternary row `p`, let `m_(n,p)` be the one-layer bridge mass.

The exact formula is

`m_(n,p) = floor(2^(n+1)/3^p) mod 6`.

Equivalently, `m_(n,p)` is the base-6 digit at position `p` of

`2^(n+p+1)`.

Thus every equal-index diagonal `n+p=S` in the full 2/3 bridge graph is literally a base-6 expansion of the single power

`2^(S+1)`.

This is the precise arithmetic meaning of the base-6 universe: horizontal movement changes the binary exponent; vertical movement changes ternary depth; the diagonal combines them into a base-6 digit coordinate.

---

## 4. Original x4 Happy Gate in two x2 layers

For `R=2^(2K)=4^K`, the original GST Happy Gate at row `p` is the statement that the input digit of `R` and the output digit of `4R` are both two.

In the two microscopic x2 layers, the only bridge-mass pairs producing this are

`(m_(2K,p), m_(2K+1,p)) = (4,2)`

or

`(m_(2K,p), m_(2K+1,p)) = (5,5)`.

The first pattern is a DESTROY/CREATE rerouting through the intermediate x2 world; the second is a SURVIVE/SURVIVE realization.

Therefore the full x4 gate condition is exactly

`exists p,`

`(floor(2^(2K+1)/3^p) mod6, floor(2^(2K+2)/3^p) mod6)`

`∈ {(4,2),(5,5)}`.

This is an exact 2-world/3-world/6-world intersection equation.

---

## 5. EQ11 is the scale axis of the microscopic formula

EQ11 is

`Σ(n)=v3(n)-v2(n)`.

In the bridge formula the two competing scales are exactly powers of two and powers of three:

`2^(n+1)/3^p`.

The equal-scale locus is therefore the natural diagonal coordinate of the microscopic base-6 bridge graph. This makes EQ11 the scale coordinate of the actual x2 bridge transducer, not merely an analogy.

---

## 6. EQ5 is the half-phase all-BIG2 bridge sheet

Fix `s≥1` and put

`N=3^s`.

At ternary depth `s+2`, multiplication by two modulo `3^(s+2)` has order

`2*3^(s+1)=6N`.

The physical x4 phases occur at binary-exponent displacements

`0, 2N, 4N, 6N`.

The half-period lies at displacement

`3N`,

exactly halfway between physical phase one and physical phase two.

EQ5 gives

`2^(3N) = 8^N ≡ -1 (mod 3^(s+2))`.

Hence the half-period residue is

`3^(s+2)-1`,

whose first `s+2` ternary digits are all `2`.

Thus EQ5 is the exact all-BIG2 bridge sheet sitting half a physical x4 phase off-grid in the x2 world.

This explains why the earlier global mirror picture was wrong: the genuine finite complement sheet is not itself a physical x4 phase boundary.

---

## 7. True final residual does not contain origin trit zero

The residual strong-induction factorization has the exact form

`b = 1 + 3^k*m`,

with

`k≥1`, `m≥1`, and `m mod3 ≠0`.

Therefore in the genuine `k=1` residual branch,

`m mod3 ∈ {1,2}`.

The origin-trit-zero branch is impossible there.

This matters because the previously derived prefix-one event law is:

- origin trit `0` -> DESTROY;
- origin trit `1` -> NEITHER and parent seed `1->0` (NULL);
- origin trit `2` -> CREATE and parent seed remains `1`.

For the actual final `k=1` residual, only the last two branches occur:

`1 -> NULL/NEITHER`,

`2 -> CREATE`.

So the standalone `GSTPrefixOneNavigationLift`, which quantifies over every positive `n`, asks for more mathematics than the residual strong-induction chain truly needs.

A final implementation may therefore profit from a residual-only prefix-one theorem carrying the exact hypothesis

`n mod3 ≠0`.

This does not weaken the universal result: the omitted `n mod3=0` cases correspond to a larger factor `3^k` with `k≥2` and belong to the deeper-cut branches of the strong-induction factorization.

---

## 8. Exact two surviving branch formulas

Let

`H_s(n)=z_s + A_s*Q_(s+1)(n)`,

with `A_s=4^(3^s)` and `c_s=1+3*z_s`.

### Branch `n=3u+1`

The first parent-tail event is NEITHER and the incoming parent seed regenerates from `1` to `0`.

The exact suffix has the form

`H_s(3u+1)/3 = w_s + A_s*H_(s+1)(u)`,

where

`w_s=(z_s+A_s)/3`.

This is a nested prefix-one state with a new finite outer offset and NULL seed.

### Branch `n=3u+2`

The first parent-tail event is CREATE and the parent seed remains `1`.

Writing the exact phase-two tail at level `s+1` as `H2_(s+1)(u)`, one has

`H_s(3u+2)/3 = (z_s+2*A_s-1)/3 + A_s*H2_(s+1)(u)`.

These two formulas are the true next targets. No DESTROY branch remains at `k=1`.

---

## 9. Current surgical consequence

The final mathematical search should no longer attempt a symmetric three-origin proof for the residual `k=1` seam.

It should prove only:

1. NULL branch (`m mod3=1`): the regenerated nested prefix-one offset cannot remain completely bad;
2. CREATE branch (`m mod3=2`): the created BIG2 information cannot avoid a later SURVIVE in the canonical phase surface.

The exact x2/base-6 bridge universe, EQ5 half-phase sheet, EQ6 origin address, and the universal origin-modulus theorem are now available as coordinates for these two cases.
