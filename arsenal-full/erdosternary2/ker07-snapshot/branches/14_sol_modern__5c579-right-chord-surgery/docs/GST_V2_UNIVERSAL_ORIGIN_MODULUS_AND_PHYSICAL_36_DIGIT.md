<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0779 / 1132
<!--    Path         : branches/sol_5c579-right-chord-surgery/docs/GST_V2_UNIVERSAL_ORIGIN_MODULUS_AND_PHYSICAL_36_DIGIT.md
<!--    Ref          : origin/sol/5c579-right-chord-surgery
<!--    First-commit : 2026-08-17 04:13:07 +0530  (5377aca)
<!--    Last-commit  : 2026-08-17 04:13:07 +0530  (5377aca)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 04:13:07 +0530  5377aca  (ker07-dev)
<!--        Record universal origin modulus and physical base-36 digit bridge
<!-- ====================================================================== -->

# GST Graph V2 — Universal Origin Modulus and Physical 36-Digit Bridge

## Status discipline

Exact algebra only. This note also records the correction that a physical base-36 diagonal is not the vertical word of one fixed consecutive-power pair.

---

## 1. Universal canonical origin modulus theorem

Let

`A_t = 4^(3^t)`,

`c_t = (A_t-1)/3^(t+1)`,

and

`Q_t(b)=c_t*(1+A_t+...+A_t^(b-1))`.

For every `m>0` and every `b`, write

`b=q*m+r`, `0≤r<m`.

Split the geometric sum into `q` complete blocks of width `m` plus the final block of width `r`:

`Q_t(b)`

`= Q_t(r) + A_t^r * Q_t(m) * (1 + A_t^m + ... + A_t^((q-1)m))`.

Therefore

`Q_t(b) ≡ Q_t(r) (mod Q_t(m))`.

Since `Q_t` is strictly increasing and `r<m`,

`0≤Q_t(r)<Q_t(m)`.

Hence the exact remainder is

`boxed: Q_t(b) mod Q_t(m) = Q_t(b mod m)`.

This holds for **every** origin modulus `m`.

Consequences:

- `m=2^k` gives an exact binary-origin coordinate;
- `m=3^k` gives the exact ternary/cascade coordinate;
- `m=6^k` gives the simultaneous binary/ternary origin coordinate;
- the residue `Q_t(b) mod Q_t(m)` uniquely recovers `b mod m` because the representatives `Q_t(0),...,Q_t(m-1)` are strictly ordered below `Q_t(m)`.

Thus `Q_t` is an exact modular embedding of every finite origin universe into canonical physical integer space.

---

## 2. Physical phase motion is translation in every origin universe

The exact recurrence

`Q_t(b+1)=c_t+A_t*Q_t(b)`

is the physical one-phase step.

Under the universal modulus coordinate with `m=6^k`, it acts simply as

`b mod6^k -> (b+1) mod6^k`.

Therefore the three phase sectors are literally

`3n -> 3n+1 -> 3n+2 -> 3(n+1)`

inside the same finite origin universe.

This gives the correct physical phase action. It does not identify local GST re-coordinate rotations with phase translation.

---

## 3. One physical 6² information digit

Fix a real integer `R` and a two-row ternary block beginning at row `p`.

Let

`x = (R mod 3^p)/3^p`,

`C = floor(4x)`,

and let

`w = (R / 3^p) mod 9`

be the two input ternary digits treated as one base-9 symbol.

The normalized residue two rows higher is

`x2 = (R mod 3^(p+2))/3^(p+2) = (x+w)/9`.

Therefore

`36*x2 = 4*x + 4*w`.

Write `4x=C+y`, `0≤y<1`. Then

`36*x2 = C + 4*w + y`.

Hence

`boxed: floor(36*x2)=C+4*w`.

Define

`m=C+4*w`.

Since `0≤C<4` and `0≤w<9`,

`0≤m≤35`.

This is the exact physical origin of the 36 GST states.

---

## 4. Same information digit, two exact subspace readings

The two-row multiply-by-four algorithm also writes

`C+4*w = e + 9*C'`,

where

- `e` is the two-trit output block of `4R`, `0≤e<9`;
- `C'` is the carry after the two input rows, `0≤C'<4`.

Thus the same physical information digit has two exact factorizations:

`boxed: m = C+4*w = e+9*C'`.

Interpretation:

- `(C,w)` is the `4 × 9` input-space reading;
- `(C',e)` is the `9 × 4` output-space reading;
- `m` is the invariant information object.

This is the precise finite arithmetic realization of PATTERN's statement that one information object has multiple space realizations.

---

## 5. Physical equal-scale diagonal map

Let

`q_i=P-2i`,

`R_i=4^i R`,

and

`x_i=(R_i mod 3^q_i)/3^q_i`.

Then one horizontal multiply-by-four step together with removal of two ternary rows gives

`boxed: x_(i+1) = fractional_part(36*x_i)`.

So the real equal-scale diagonal dynamics is the expanding map

`x -> 36x mod1`.

The 36-state information digit at each diagonal point is `floor(36x)`.

This is the correct physical appearance of `6²=36`.

---

## 6. Critical interpretation correction

Advancing the base-36 digit sequence moves diagonally:

`(R,p+2) -> (4R,p)`.

It does **not** move vertically through successive two-row blocks of the same fixed `R`.

Therefore the base-36 expansion obtained from repeated `x -> {36x}` is a word along a **power/depth diagonal**, not the complete vertical event word of the single pair `(R,4R)`.

A previous tentative equivalence between the base-36 digits of a power such as `16^K` and the complete fixed pair `4^K -> 4^(K+1)` is false and must not be used.

What survives exactly is:

- each individual 36-state mass is physical;
- repeated base-36 shift is physical diagonal motion;
- the two decompositions of each digit are exact subspace readings of the same information;
- phase translation remains the separate canonical origin action `b->b+1`.

---

## 7. Exact physical/subspace intersection coordinate

At one block define

- `C_v = C'`, the carry two rows upward in the current multiplication;
- `C_h = gstCarry(4R,p)`, the carry entering the same two-row block in the next horizontal power column.

The alternate output reading `(C_v,e)` is exactly the physical next-column input state iff

`boxed: C_v = C_h`.

This equality is the correct local intersection condition between the subspace re-coordinate and the neighboring physical power surface.

The final phase-crossing theorem may therefore be attacked either through this intersection equation or through the universal origin-modulus coordinate above, but the equality cannot be assumed globally.
