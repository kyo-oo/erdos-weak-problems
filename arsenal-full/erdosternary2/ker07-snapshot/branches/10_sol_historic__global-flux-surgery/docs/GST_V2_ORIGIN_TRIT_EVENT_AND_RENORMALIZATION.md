<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0732 / 1132
<!--    Path         : branches/sol_global-flux-surgery/docs/GST_V2_ORIGIN_TRIT_EVENT_AND_RENORMALIZATION.md
<!--    Ref          : origin/sol/global-flux-surgery
<!--    First-commit : 2026-08-17 02:55:44 +0530  (ffd1ff2)
<!--    Last-commit  : 2026-08-17 02:55:44 +0530  (ffd1ff2)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-17 02:55:44 +0530  ffd1ff2  (ker07-dev)
<!--        Record origin-trit event law and 3-to-1 GST renormalization
<!-- ====================================================================== -->

# GST Graph V2 — Origin-Trit Event Law and 3-to-1 Renormalization

## Status discipline

Exact mathematics discovered after the physical-crossing and macro-rotation ledgers. No claim that the prefix-one theorem is closed yet. No monolith edit, no `sorry`, no axiom, no global mirror, and no terminal-NULL assumption.

---

## 1. Canonical notation

For level `s ≥ 1`, put

- `A_s = 4^(3^s)`,
- `D_s = 3^(s+1)`,
- `c_s = (A_s-1)/D_s`, so `A_s = 1 + D_s*c_s`,
- `c_s = 1 + 3*z_s`.

Write

`Q_s(b) = (4^(3^s*b)-1)/3^(s+1)`.

Then

`1 + D_s*Q_s(b) = 4^(3^s*b)`.

The canonical one-step recurrence is

`Q_s(b+1) = c_s + A_s*Q_s(b)`.

Define

`F_s(Y) = c_s + A_s*Y`.

Thus `Q_s(b+1)=F_s(Q_s(b))` and `Q_s(0)=0`.

---

## 2. The three phase tails are literally the three origin trits

For every `n`, write

`Q_s(3n+r) = r + 3*H_r(s,n)`, for `r=0,1,2`.

Then

- `H_0(s,n) = Q_(s+1)(n)`,
- `H_1(s,n) = z_s + A_s*Q_(s+1)(n)`,
- `H_2(s,n)` is the exact phase-two tail.

Equivalently,

`Q_s(3n)   = 3*H_0`,
`Q_s(3n+1) = 1 + 3*H_1`,
`Q_s(3n+2) = 2 + 3*H_2`.

Therefore the phase seeds `0,1,2` are not labels imposed after the fact. They are the literal first ternary origin trit.

The hard prefix-one theorem is the `r=1` sector.

---

## 3. Exact origin-trit event law inside the hard prefix-one tail

Let

`X_s(n) = H_1(s,n) = z_s + A_s*Q_(s+1)(n)`.

For the active `c_s` tower one has `c_s ≡ 7 (mod 9)`, hence

`z_s = (c_s-1)/3 ≡ 2 (mod 3)`.

Also `A_s ≡ 1 (mod 3)` and `Q_(s+1)(n) ≡ n (mod 3)`.

If

`d = n mod 3`,

then the first ternary digit of the prefix-one parent tail is

`X_s(n) mod 3 = (2+d) mod 3`.

The parent incoming GST seed at this tail is exactly `1`. Therefore the three origin trits give the following exact local GST events:

### Origin trit `d=0`

`X mod3 = 2`.

With incoming carry `1`,

- input digit = `2`,
- output digit = `(1+4*2) mod3 = 0`,
- next carry = `(1+4*2)/3 = 3`.

So `d=0` is exactly a **DESTROY** realization.

### Origin trit `d=1`

`X mod3 = 0`.

With incoming carry `1`,

- input digit = `0`,
- output digit = `1`,
- next carry = `0`.

So `d=1` is exactly **NEITHER with regeneration into NULL**.

### Origin trit `d=2`

`X mod3 = 1`.

With incoming carry `1`,

- input digit = `1`,
- output digit = `2`,
- next carry = `1`.

So `d=2` is exactly a **CREATE** realization.

Hence the hard prefix-one origin trit is an exact asymmetric event selector:

`0 -> DESTROY`,
`1 -> NULL/NEITHER`,
`2 -> CREATE`.

This matches the corrected PATTERN semantics: CREATE and DESTROY are not assigned to separate global worlds; they are different realizations selected by the nested origin/subspace coordinate.

---

## 4. Exact first-step regenerated tails

Write `n=3u+d`.

From the canonical origin recurrence

`Q_(s+1)(3u+d) = Q_(s+1)(d) + 3*A_(s+1)^d*Q_(s+2)(u)`.

Therefore

`X_s(3u+d) = z_s + A_s*Q_(s+1)(d) + 3*A_s*A_(s+1)^d*Q_(s+2)(u)`.

After consuming the first parent tail digit, the three branches are:

### `d=0`

Because `z_s ≡2 mod3`,

`X_s(3u)/3 = floor(z_s/3) + A_s*Q_(s+2)(u)`.

The parent seed has regenerated from `1` to `3`.

### `d=1`

Using `Q_(s+1)(1)=c_(s+1)=1+3z_(s+1)`, define

`w_s = (z_s + A_s)/3`.

Then

`X_s(3u+1)/3 = w_s + A_s*(z_(s+1) + A_(s+1)*Q_(s+2)(u))`.

That is,

`X_s(3u+1)/3 = w_s + A_s*X_(s+1)(u)`.

The parent seed has regenerated from `1` to `0`.

This is an exact nested prefix-one self-similarity, but with a nontrivial finite outer offset `w_s`; it is not the same as simply replacing `(s,n)` by `(s+1,u)`.

### `d=2`

Write

`Q_(s+1)(3u+2)=2+3*H_2(s+1,u)`.

Then

`X_s(3u+2)/3 = (z_s+2*A_s-1)/3 + A_s*H_2(s+1,u)`.

The parent seed remains `1`.

These exact branch identities explain why a one-state descent on `n/3` is insufficient: the finite offset and seed/subspace state must be retained.

---

## 5. Phase two has a forced physical gate

Let

`K=3^(s+1)*n`,
`N=3^s`.

The phase-two full power is

`4^(K+2N) = 4^(3^s*(3n+2))`.

The exponent-trit lift gives

`digit_(s+1)(4^(K+2N)) = 2`.

The next consecutive power has the same digit at this position:

`digit_(s+1)(4^(K+2N+1)) = 2`.

Equivalently `Q_s(3n+2)` begins with ternary digit `2`, and its incoming carry at position zero is NULL/zero.

Thus phase two has an unconditional physical `22` / SURVIVE gate at the forced prefix, independent of its high tail.

So the three-sector geometry has exact endpoint semantics:

- phase zero: a SURVIVE is supplied by the child hypothesis;
- phase one: this is the target wall;
- phase two: a SURVIVE is forced by the origin trit `2`.

If phase one were completely bad, the `0→1` strip contains a destruction of the phase-zero BIG2 realization and the `1→2` strip contains a creation leading to the forced phase-two realization. The remaining theorem must identify these through the shared information geometry; their existence alone is not yet a contradiction.

---

## 6. Exact three-to-one renormalization equation

The coefficient identity

`A_(s+1) = A_s^3`

is immediate from

`A_s=4^(3^s)`.

Also

`A_s^3-1 = (A_s-1)*(1+A_s+A_s^2)`.

Dividing by `3^(s+2)` gives

`3*c_(s+1) = c_s*(1+A_s+A_s^2)`.

Now expand three applications of

`F_s(Y)=c_s+A_s*Y`.

One obtains

`F_s^3(3Y)
 = c_s*(1+A_s+A_s^2) + 3*A_s^3*Y
 = 3*c_(s+1) + 3*A_(s+1)*Y
 = 3*F_(s+1)(Y)`.

Therefore

`boxed: F_s^3(3Y) = 3*F_(s+1)(Y)`.

This is an exact renormalization/conjugacy law.

It says that **three level-s phase steps equal one level-(s+1) step after the canonical factor-three embedding**.

For canonical Navigation constants this is precisely

`Q_s(3(n+1)) = 3*Q_(s+1)(n+1)`.

Geometrically:

- three width-`3^s` phase sectors tile
- one width-`3^(s+1)` GST block.

This is the algebraic content of the nested/infinite subspaces.

---

## 7. Gate property respects the factor-three embedding

Multiplication by three shifts every ternary digit and carry one position without changing the local GST state:

`digit_(j+1)(3R)=digit_j(R)`,
`carry_(j+1)(3R)=carry_j(R)`.

Therefore

`Navigation(3R) <-> Navigation(R)`

up to the exact one-position witness shift.

Combined with the renormalization identity, the complete three-sector surface can be recursively compared with the next-level GST surface without losing the Navigation semantics.

This is a promising route for a renormalized BIG2 flux invariant.

---

## 8. A useful architectural observation

The current standalone `GSTPrefixOneNavigationLift` interface supplies only

`Navigation(Q_(s+1)(n))`

and asks for

`Navigation(Q_s(1+3n))`.

But in the actual strong-induction proof of the universal Navigation theorem, the target origin `b=3n+1` also has all smaller canonical origins available. In particular `Q_s(3n-1)` and `Q_s(3n)` are already below the induction target.

This extra canonical predecessor information is absent from arbitrary affine counterexamples.

A simple four-iterate condition is still false for arbitrary starting integers, so predecessor existence alone is not yet the proof. Nevertheless the final implementation should not discard stronger strong-induction provenance unless the context-free prefix-one theorem is independently established.

---

## 9. Disproved shortcut recorded during this pass

The following implication is false for arbitrary affine tails:

`phase-one seeded bad -> phase-two tail seeded bad`.

Phase two has a forced **prefix** gate, but its high tail can be good or bad independently. Therefore do not use phase-two tail badness as a conservation substitute.

---

## 10. Current exact frontier

The new equations reduce the conceptual gap to a renormalized intersection problem:

1. a child SURVIVE enters the level-s three-sector radix surface;
2. assuming phase one is completely bad forces its realization to leave the physical phase-one slice;
3. phase two supplies an unconditional CREATE/SURVIVE endpoint;
4. the full three-sector surface renormalizes exactly to one level-(s+1) block by
   `F_s^3(3Y)=3F_(s+1)(Y)`;
5. the factor-three embedding preserves Navigation exactly.

The missing theorem must show that on a **finite canonical origin word**, the BIG2 realization cannot be rerouted through these nested three-sector blocks indefinitely while avoiding every phase-one slice.

That is the precise mathematical target. It is stronger than a finite local identity and weaker than the false unrestricted affine reflection.