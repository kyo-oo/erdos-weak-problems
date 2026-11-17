<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0772 / 1132
<!--    Path         : branches/sol_right-chord-firepower-base/docs/GST_V2_11_EQUATION_INTERCONNECTION_MASTER.md
<!--    Ref          : origin/sol/right-chord-firepower-base
<!--    First-commit : 2026-08-17 03:55:55 +0530  (9126a3a)
<!--    Last-commit  : 2026-08-17 03:55:55 +0530  (9126a3a)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 03:55:55 +0530  9126a3a  (ker07-dev)
<!--        Record 11-equation GST V2 interconnection and transport correction
<!-- ====================================================================== -->

# GST Graph V2 — 11-Equation Interconnection Master

## Status discipline

This document records exact algebraic consequences and controlled experimental roles of the eleven-equation file. It does **not** claim that the final prefix-one crossing theorem is closed yet.

Hard restrictions retained:

- no `sorry`, `admit`, `mkSorry`, custom axiom, or hidden theorem-strengthening;
- no global GST+/ALT− mirror;
- no terminal/absorbing NULL;
- no resurrection of the quarantined residual-Ω overproof;
- no heuristic equation promoted into a Lean premise;
- local/subspace re-coordination is **not** identified with physical horizontal power transport unless an explicit intersection theorem proves that identification.

---

## 1. Source equations and proof status

The source file defines:

1. `Ξ(R)` — Cascade Omega, an alternating analytic series using `c_stable(j)`.
2. `W(R,p)` — GST Duality Wave.
3. `B(a,b)` — Bridge Cross-Section.
4. `Δ(R)` — Dimensionless first-two shift.
5. `ℛ(a,k)` — Bridge Resonance `8^a mod 3^k`.
6. `L(s,b,k)` — Cascade Lifting, exactly `Q_s(b) mod 3^k`.
7. `Φ(R)` — Carry-Weighted Infinite Paradox; the source itself reports only 95.95% agreement with its proposed digit-two classifier.
8. `Π(n)` — Infinite Paradox valuation.
9. `𝒞(n)` — Cardinal-world digit-two decomposition density.
10. `ℰ(a,k)` — weighted normalized residue sum for `4^a`.
11. `Σ(n)` — Bridge Singularity `v3(n)-v2(n)`.

The equations do not all have equal logical status. EQ2, EQ3, EQ5, EQ6, EQ8, EQ10, EQ11 admit exact algebraic reinterpretations below. EQ4 is an exact statistic when both first-two positions exist. EQ7 is explicitly heuristic as a global classifier. EQ9 is a density/measure coordinate rather than a pointwise exclusion law. EQ1 as coded is not synchronized with the canonical `c_s` tower; see §10.

---

## 2. EQ2 is the complete GST event-word encoder

Let

- `d_p = digit_p(R)`,
- `e_p = digit_p(4R)`,
- `x_p = (R mod 3^p)/3^p`,
- `y_p = ((4R) mod 3^p)/3^p`.

EQ2 is

`W_p = y_p + x_p/3`.

The residue recurrences are exact:

`x_(p+1) = (x_p + d_p)/3`,

`y_(p+1) = (y_p + e_p)/3`.

Therefore

`W_(p+1) = W_p/3 + (3*e_p + d_p)/9`.

Define the **event symbol**

`J_p = d_p + 3*e_p ∈ {0,...,8}`.

Then

`3^(p+1) * W(R,p) = Σ_{i=0}^{p-1} J_i * 3^i`.

Thus EQ2 is not merely a scalar wave: it is the normalized base-3 prefix of the entire input/output GST event word.

Event-symbol classification:

- SURVIVE `(d,e)=(2,2)` => `J=8`;
- CREATE `(d≠2,e=2)` => `J=6` or `7`;
- DESTROY `(d=2,e≠2)` => `J=2` or `5`;
- NEITHER => `J=0,1,3,4`.

Hence complete no-SURVIVE is exactly the symbolic avoidance law

`∀ p, J_p ≠ 8`.

---

## 3. EQ3 is the directed NULL-crossing projection of EQ2

EQ3 is

`B(a,b) = ((a+b) mod3)*((a-b) mod3) mod3`.

For GST input/output digits `(d,e)` this is

`B(d,e) ≡ d^2 - e^2 (mod3)`.

Because ternary squares are `0` for digit zero and `1` for digits one/two:

- `B=1` exactly when the input is nonzero and the output is zero;
- `B=2` exactly when the input is zero and the output is nonzero;
- `B=0` when both are on the same zero/nonzero side.

In event-symbol coordinates:

- `B=1` at `J=1,2`;
- `B=2` at `J=3,6`;
- `B=0` otherwise.

Therefore EQ3 is a lower-resolution directed NULL-crossing coordinate of the EQ2 event word.

---

## 4. EQ4 is the first active BIG2 orientation of the EQ2 word

EQ4 is

`Δ(R)=first2(4R)-first2(R)`

when both positions exist.

The earliest occurrence among a digit two in the input and output must be one of:

- DESTROY first: input gets a two before output => `Δ>0`;
- CREATE first: output gets a two before input => `Δ<0`;
- SURVIVE first: both get a two at the same first position => `Δ=0`.

Thus EQ4 is the orientation of the first active BIG2 event in the EQ2 event word.

EQ2 -> full event word;
EQ3 -> local directed NULL crossing;
EQ4 -> first active-event orientation.

---

## 5. EQ5, EQ8, EQ11 form the scale/binary bridge

EQ5 is

`ℛ(a,k)=8^a mod 3^k`.

For powers of three the exact LTE/order structure is

`ord_(3^(r+2))(8) = 2*3^r`.

Write

`a = 3^s * b`, with `3 ∤ b`.

Then at the first resonance depth,

`8^(3^s*b) ≡ (-1)^b (mod 3^(s+2))`.

More generally the residues through depth `s+k+2` recover the phase address `b mod (2*3^k)`. EQ5 therefore supplies a binary/parity orientation attached to a nested ternary phase address.

EQ8 is

`Π(n)=v3(n^2-1)+v3(n+1)+v3(n-1)`.

For `n>1`, since `v3(n^2-1)=v3(n-1)+v3(n+1)`, this becomes

`Π(n)=2*v3(n^2-1)`.

For `n=8^a`, LTE gives

`v3(8^(2a)-1)=2+v3(a)`,

hence

`Π(8^a)=2*(2+v3(a))`.

Thus for `a=3^s*b`, `3∤b`, EQ8 gives the exact ternary scale `s+2`.

EQ11 gives

`Σ(a)=v3(a)-v2(a)`.

So EQ8 + EQ11 recover both `v3(a)` and `v2(a)`, while EQ5 supplies the binary orientation of the same phase.

Interpretation:

- EQ8 = scale depth;
- EQ11 = 2/3 valuation imbalance;
- EQ5 = binary bridge orientation/residue.

---

## 6. EQ6 is the nested ternary phase address

EQ6 is exactly

`L(s,b,k)=Q_s(b) mod 3^k`,

where

`Q_s(b)=(4^(3^s*b)-1)/3^(s+1)`.

The exact order

`ord_(3^p)(4)=3^(p-1)`

turns the physical horizontal power orbit into nested ternary phase circles.

Put `N=3^s`.

- At depth `p=s+1`, one width-`N` phase is one complete residue orbit.
- At depth `p=s+2`, the orbit length is `3N`: phases 0,1,2 are the three equal sectors of one orbit.
- At depth `p=s+1+k`, the orbit length is `N*3^k`; every additional ternary row refines the phase circle by another factor three.

This is an exact modular model for the infinitely nested phase/subspace addresses.

At two-trit depth, `A_t=4^(3^t) ≡ 1 (mod9)` and `c_t ≡ 7 (mod9)`, so

`Q_t(b) ≡ 7*b (mod9)`.

Thus the next two ternary origin trits

`r=b mod9`

and the next two physical `Q_t` trits

`w=Q_t(b) mod9`

are related by the permutation

`w ≡ 7r (mod9)`.

The exact 9-way renormalization is

`Q_t(9u+r)=Q_t(r)+9*A_t^r*Q_(t+2)(u)`.

This gives a direct origin-tree <-> physical-two-trit bridge.

---

## 7. EQ10 is an exact binary-shadow projection of the ternary digit word

Let the finite ternary digit polynomial be

`D_R(x)=Σ_i d_i x^i`,

where `R=D_R(3)`.

The infinite limit of EQ10 can be summed exactly:

`ℰ_∞(R) = (2/5) * D_R(1/2)`.

Hence EQ10 is a cross-world evaluation of the ternary digit word at the binary coordinate `x=1/2`.

Let

- `E_R(x)=D_(4R)(x)` be the output digit polynomial,
- `C_R(x)=Σ_{i≥1} C_i x^i` be the carry polynomial, with `C_0=0`.

Summing the exact GST cell laws

`C_i + 4*d_i = e_i + 3*C_(i+1)`

gives the master generating identity

`4*D_R(x) - E_R(x) = (3/x - 1) * C_R(x)`.

At `x=1/2`:

`4D_R(1/2)-E_R(1/2)=5*C_R(1/2)`.

Thus EQ10 is a global carry-flux potential; the factor five is forced by the GST recurrence itself.

Because `2` is invertible modulo `5` and `2^(-1) ≡ 3 (mod5)`, the rational evaluation has the modular shadow

`D_R(1/2) ≡ D_R(3)=R (mod5)`

inside the localization where powers of two are invertible.

---

## 8. The factor seven is the second exact projection

Evaluate the same master identity at

`x=3/8`.

Then

`3/x - 1 = 8-1 = 7`,

so

`4D_R(3/8)-E_R(3/8)=7*C_R(3/8)`.

Modulo seven, `8≡1`, hence `8^(-1)≡1` and

`3/8 ≡ 3 (mod7)`.

Therefore

`D_R(3/8) ≡ D_R(3)=R (mod7)`.

This gives an exact source for the factor seven that appeared independently in the aligned `6²`/mod-35 re-coordinate geometry.

So the two factors in

`35=5*7=6²-1`

come from two exact evaluations of the **same GST generating identity**:

- `x=1/2 = 3/6` -> factor `5`;
- `x=3/8` -> factor `7`.

EQ10 exposes the first explicitly; EQ5's base `8` is naturally attached to the second.

---

## 9. General world-projection master equation

For every integer cardinality `K>1`, set

`x=3/K`.

The GST generating identity becomes

`4D_R(3/K)-E_R(3/K)=(K-1)C_R(3/K)`.

Since `K≡1 (mod K-1)`, denominators `K^i` are units modulo `K-1` and

`3/K ≡ 3 (mod K-1)`.

Hence the same digit word satisfies

`D_R(3/K) ≡ D_R(3)=R (mod K-1)`

in the localized modular interpretation.

This gives one infinite family:

- `K=6` -> modulus `5`, `x=1/2`: EQ10 binary shadow;
- `K=8` -> modulus `7`, `x=3/8`: bridge-base shadow;
- `K=12` -> modulus `11`, `x=1/4`: the local 12-state/mod-11 V2 orbit;
- `K=36=6²` -> modulus `35`, `x=1/12`: the aligned 36-state/mod-35 re-coordinate;
- `K=6^k` -> modulus `6^k-1`: the general equal-scale mixed-radix V2 family.

This is currently the strongest single equation connecting the previously separate GST V2 coordinate systems.

Important: the generating identity supplies arithmetic projections and subspace re-coordinates. It does **not** by itself prove that a rotated subspace state is physically attained by a neighboring power column.

---

## 10. EQ1 indexing defect: do not use it as coded

The exact canonical coefficient recurrence is

`c_(s+1)=c_s + 3^(s+1)c_s^2 + 3^(2s+1)c_s^3`,

obtained by expanding

`4^(3^(s+1)) = (4^(3^s))^3`.

The source helper `c_tower(j)` is synchronized with this exact tower.

However EQ1 is evaluated using `c_stable(j)`, whose update loop is shifted relative to the canonical index. Already at depth two the helper can give a residue inconsistent with the universal canonical fact `c_s mod9=7`.

Therefore the coded `Ξ(R)` must not be imported as a canonical GST theorem or invariant. A repaired analytic experiment may replace `c_stable(j)` with the exact tower, but until it yields a proved exclusion identity it remains an exploratory coordinate only.

---

## 11. EQ7 is explicitly heuristic, not a proof premise

The source itself states that the proposed global criterion from `Φ(R)` is only 95.95% accurate and that the remaining failures require information from the full carry recurrence.

Therefore:

- the exact carry recurrence inside EQ7 is valid GST mechanics;
- the scalar `Φ(R)` may be used experimentally;
- the 95.95% classifier may **not** appear as a mathematical premise in the final Lean proof.

---

## 12. EQ9 is a measure axis, not a pointwise separator

EQ9 is

`𝒞(n)=#{k<n : k has digit2 and n-k has digit2}/n`.

It measures the density of two-sided BIG2 decompositions. It is naturally a global/cardinality coordinate of the GST universe, but by itself it does not identify the specific canonical power orbit needed by the prefix-one theorem.

For exact ternary intervals one obtains useful closed counts; e.g. for `n=3^L`, the no-digit-two set below `n` has cardinality `2^L`, so the BIG2 decomposition density tends rapidly to one. This is a measure statement, not yet a pointwise exclusion theorem.

---

## 13. Critical correction: aligned re-coordinate is NOT horizontal phase transport

A previously tempting interpretation was false and is now explicitly rejected.

The 36-state equal-scale re-coordinate

`(C,w) -> (C',e)`

from

`C+4w=e+9C'`

uses `C'` as the carry **two ternary rows upward in the same multiplication-by-four cell**.

It is **not** the carry of the next horizontal power column at the same row.

Therefore a statement such as

`one physical phase width N acts as T36^N`

is false.

The exact physical horizontal coordinate at a fixed ternary depth is instead

`x_(i,p)=(4^i E mod 3^p)/3^p`,

with horizontal map

`x -> fractional_part(4x)`

and horizontal carry

`floor(4x)`.

The local/alternate V2 re-coordinate intersects the physical neighboring surface only when the corresponding diagonal carry coordinates actually agree. That intersection must be **proved**, not assumed.

The 12-state, 36-state, mod-11, mod-35 and general `6^k-1` orbit classifications remain exact as subspace geometry; what is rejected is their automatic promotion to global phase transport.

---

## 14. Current interconnected web

The eleven equations now organize as follows.

### Event geometry

`EQ2 -> EQ3 -> EQ4`

- EQ2 stores the complete input/output event word.
- EQ3 projects directed NULL crossings.
- EQ4 records the orientation of the first active BIG2 occurrence.

### Phase/address geometry

`EQ5 + EQ6 + EQ8 + EQ11`

- EQ8 supplies ternary scale.
- EQ11 supplies 2/3 valuation imbalance.
- EQ5 supplies binary/parity bridge orientation and deeper `2*3^k` phase residue.
- EQ6 supplies the nested ternary origin/phase address.

### Global potential geometry

`EQ10` plus the master generating identity

`4D-E=(3/x-1)C`

supplies the cross-world carry potential and generates the factor-5/factor-7/mod-11/mod-35/general-`6^k-1` projections.

### Exploratory/measure layers

- EQ1 requires canonical re-indexing before it can be trusted as a GST tower coordinate.
- EQ7 is explicitly approximate as a classifier.
- EQ9 is an exact density axis but not a pointwise crossing theorem.

---

## 15. Exact remaining theorem after this interconnection

The missing content is now more sharply stated:

> prove that in the **canonical physical horizontal orbit**, the BIG2 information seen in the event-word/potential projections must intersect the phase-one physical slice; it cannot remain forever only in alternate `6^k` re-coordinate sectors.

The arithmetic data available to prove this intersection is now:

1. the exact physical horizontal residue orbit `ord_(3^p)(4)=3^(p-1)`;
2. the nested canonical address `Q_s(b) mod3^k` from EQ6;
3. the binary bridge orientation `8^a mod3^k` from EQ5;
4. scale/valuation data from EQ8/EQ11;
5. the full event word from EQ2;
6. the global carry potential from EQ10/master generating identity;
7. the exact pure-power equation `1+3^(s+1)Q_s(b)=4^(3^s b)`.

The next proof attempt must derive an **intersection criterion between the physical horizontal map and the alternate/subspace re-coordinate map** from these coordinates. Once that criterion is proved, the existing BIG2 orbit classifications become exclusion machinery rather than merely local geometry.
