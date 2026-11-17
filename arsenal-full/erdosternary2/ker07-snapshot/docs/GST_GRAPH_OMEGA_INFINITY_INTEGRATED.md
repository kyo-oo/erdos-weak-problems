<!-- ======================================================================
<!-- CHRONOLOGICAL LABEL -- #0035 / 1132
<!--    Path         : docs/GST_GRAPH_OMEGA_INFINITY_INTEGRATED.md
<!--    Ref          : main
<!--    First-commit : 2026-08-14 21:44:31 +0530  (83dd56f)
<!--    Last-commit  : 2026-08-14 21:44:31 +0530  (83dd56f)
<!--    Total commits: 1
<!-- ======================================================================
<!-- GIT HISTORY (chronological, oldest first)
<!-- ======================================================================
<!-- [01/1] 2026-08-14 21:44:31 +0530  83dd56f  (ker07-dev)
<!--        Import Sol inline surgery handoff and GST graph workspace
<!-- ====================================================================== -->

# GST Graph: construction and operation

## 1. Purpose

The GST graph is the exact directed carry graph generated when a natural
number `R` is multiplied by four while its ternary digits are read from low to
high. It simultaneously records digit position, ternary descent, input digit,
output digit, carry, graph space, and distance from a chosen boundary.

It is not a plotted approximation. Every vertex and edge is determined by
integer division and remainder equations.

## 2. Fundamental coordinates

For a natural number `R` and position `p`, define

```text
digit(R,p)   = floor(R / 3^p) mod 3
carry(R,p)   = floor(4(R mod 3^p) / 3^p)
descent(R,p) = floor(R / 3^p)
window9(R,p) = floor(R / 3^p) mod 9.
```

In Lean these are

```lean
def gstDigit (R p : Nat) : Nat := R / 3^p % 3
def gstCarry (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p
def gstDescent (R p : Nat) : Nat := R / 3^p
def gstWindow9 (R p : Nat) : Nat := R / 3^p % 9
```

For every positive position, `carry(R,p) < 4`; therefore the carry state is
exactly one of `0,1,2,3`. Every ternary digit is exactly one of `0,1,2`.

## 3. The three GST spaces

The carry coordinate determines three disjoint spaces:

```text
NULL : carry = 0
ALT− : carry = 1 or carry = 2
GST+ : carry = 3.
```

The Lean classifier is

```lean
def gstSpaceAt (R p : Nat) : GSTSpace :=
  if gstCarry R p = 0 then .null
  else if gstCarry R p = 3 then .gstPlus
  else .altMinus
```

NULL is a genuine space. It is not merged with GST+. The wave terminates at
carry zero, which is why NULL must remain explicit.

## 4. One graph vertex

For a boundary parameter `N`, the canonical vertex at position `p` is the
seven-axis state

```text
(x, x′, y, y′, z, z′, n→n′)
```

with

```text
x      = p
x′     = p+1
y      = carry(R,p)
y′     = space(R,p)
z      = digit(R,p)
z′     = N-p
n→n′   = (descent(R,p), descent(R,p+1)).
```

The descent axis is exact:

```text
descent(R,p+1) = floor(descent(R,p)/3).
```

Thus every edge moves forward by one ternary position and divides the moving
future by three.

## 5. Exact edge equation

If the current carry is `C` and the current input digit is `d`, define

```text
output(C,d) = (C + 4d) mod 3
next(C,d)   = floor((C + 4d)/3).
```

Then the forward edge obeys

```text
digit(4R,p)  = output(carry(R,p), digit(R,p))
carry(R,p+1) = next(carry(R,p), digit(R,p)).
```

The complete transition table is

| carry `C` | digit `d` | output digit of `4R` | next carry |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |
| 0 | 1 | 1 | 1 |
| 0 | 2 | 2 | 2 |
| 1 | 0 | 1 | 0 |
| 1 | 1 | 2 | 1 |
| 1 | 2 | 0 | 3 |
| 2 | 0 | 2 | 0 |
| 2 | 1 | 0 | 2 |
| 2 | 2 | 1 | 3 |
| 3 | 0 | 0 | 1 |
| 3 | 1 | 1 | 2 |
| 3 | 2 | 2 | 3 |

This table constructs the entire graph locally.

## 6. Happy Gate and bad language

A Happy Gate is a digit-two vertex in GST+ or NULL:

```text
digit(R,p) = 2 and carry(R,p) ∈ {0,3}.
```

Equivalently, it is a digit-two whose carry vanishes modulo three. In Lean a
Navigation witness is

```lean
def GSTNavigationWitness (R : Nat) : Prop :=
  ∃ p, gstDigit R p = 2 ∧
    (gstSpaceAt R p = .gstPlus ∨ gstSpaceAt R p = .null)
```

A vertex belongs to the bad language when it is not a Happy Gate:

```lean
def GSTBadPair (C d : Nat) : Prop :=
  ¬ (d = 2 ∧ (C = 0 ∨ C = 3))
```

Consequently, absence of a Navigation witness is exactly an infinite word in
which every graph vertex is a `GSTBadPair`.

## 7. Direct construction algorithm

Given `R` and a position ceiling `N`:

1. Set `p = 0`.
2. Compute `3^p`.
3. Compute `d = floor(R/3^p) mod 3`.
4. Compute `C = floor(4(R mod 3^p)/3^p)`.
5. Classify `C` as NULL, ALT−, or GST+.
6. Record the seven-axis vertex.
7. Mark the vertex as a Happy Gate exactly when `d=2` and `C∈{0,3}`.
8. Advance to `p+1` using the exact edge equations.
9. Continue until the requested ceiling. For a finite number, the descent
   eventually becomes zero; this creates a zero tail but does not by itself
   prove that an earlier Happy Gate existed.

Equivalent reference pseudocode:

```python
def gst_digit(R, p):
    return (R // (3 ** p)) % 3

def gst_carry(R, p):
    return (4 * (R % (3 ** p))) // (3 ** p)

def gst_space(R, p):
    C = gst_carry(R, p)
    return "NULL" if C == 0 else "GST+" if C == 3 else "ALT-"

def gst_graph(R, N):
    nodes = []
    for p in range(N + 1):
        C = gst_carry(R, p)
        d = gst_digit(R, p)
        nodes.append({
            "x": p,
            "x_next": p + 1,
            "carry": C,
            "space": gst_space(R, p),
            "digit": d,
            "distance": max(N - p, 0),
            "descent": (R // (3 ** p), R // (3 ** (p + 1))),
            "happy_gate": d == 2 and C in (0, 3),
        })
    return nodes
```

## 8. Power-of-four graph and Navigation Constant

For the structured exponent

```text
R = 4^(3^s b),  s≥1,
```

LTE gives a forced prefix and exposes the exact tail

```text
Q(s,b) = gstNavigationConstant(s,b)
       = floor(4^(3^s b) / 3^(s+1)).
```

The graph of `Q(s,b)` transports back to the full power by shifting every
position by `s+1`.

Let

```text
A_s = 4^(3^s)
c_s = (A_s-1)/3^(s+1).
```

For `b = 1 + 3^k m`, the exact generalized-cascade recurrence is

```text
Q(s,1+3^k m) = c_s + 3^k A_s Q(s+k,m).
```

This equation constructs the residual graph progressively: a finite prefix
from `c_s`, a cut at depth `k`, an affine multiplier `A_s`, and the deeper
child graph `Q(s+k,m)`.

## 9. Affine residual graph

After cutting at depth `k`, define

```text
T = Q(s+k,m)
z = c_s / 3^k
δ = 4(c_s mod 3^k)/3^k
X = z + A_s T.
```

The affine carry is

```text
affineCarry(A,z,T,j) = floor((z + A(T mod 3^j))/3^j).
```

Its exact equations are

```text
digit(z+AT,j)
  = (affineCarry(A,z,T,j) + A·digit(T,j)) mod 3

affineCarry(A,z,T,j+1)
  = floor((affineCarry(A,z,T,j) + A·digit(T,j))/3).
```

The nonlinear block-echo form is

```text
z + 4^(3^s)T = z + T + 3^(s+1)c_sT.
```

This expresses equation creation and destruction across blocks: the child
tail remains present while a new shifted echo is created.

## 10. Ω∞ coupled graph

The Ω∞ state evolves all necessary coordinates together:

```text
perfect-power origin energy
ternary descent
child carry and digit
affine carry
parent carry and digit
bridge residue
cascade depth.
```

Its conserved origin equation is

```text
1 + 3^(t+1+j)(T/3^j) + 3^(t+1)(T mod 3^j)
  = 1 + 3^(t+1)T.
```

The Happy Gate is the zero set of

```text
(parentDigit-2)^2 + (parentCarry(parentCarry-3))^2 = 0.
```

The polynomial vanishes exactly at a parent digit-two in GST+ or NULL.

## 11. Two-wave product graph

For consecutive powers, use the product graph of

```text
R = 4^(a-1),   4R = 4^a.
```

A complete two-wave bad trace is

```text
∀ p,
  BadPair(carry(R,p),  digit(R,p)) and
  BadPair(carry(4R,p), digit(4R,p)).
```

The current minimal universal target is that, beyond the verified base range,
two adjacent power waves cannot both remain complete bad traces.

## 12. Verification boundary

The coordinate definitions, transition table, Navigation recurrence, affine
equations, block echo, Ω∞ evolution, and gate polynomial are formalized in
`ErdosTernary2.lean`.

The remaining mathematical obligation is global termination/exclusion for the
canonical finite-natural perfect-power origin. A finite carry table, terminal
zero tail, same-position child transport, or conserved identity alone does not
establish this exclusion.


---

# 13. Ω∞ INFINITE-SPACE UPGRADE — control infinity as a GST space

This section integrates the infinite-space construction directly into the
original GST graph.  It does **not** truncate an infinite bad trace and does
not make graph position itself the well-founded quantity.

The central object is now the complete infinite ternary ray.

For an initial carry `C`, let `B_C` be the set of infinite ternary digit
streams whose GST multiplication-by-four trajectory never meets a Happy Gate.

Write a stream as

```text
d₀ + 3(d₁ + 3(d₂ + ...)).
```

The exact GST transition table gives the following greatest-fixed-point
equations:

```text
B₀ = 3 B₀ ∪ (1 + 3 B₁)

B₁ = 3 B₀ ∪ (1 + 3 B₁) ∪ (2 + 3 B₃)

B₂ = 3 B₀ ∪ (1 + 3 B₂) ∪ (2 + 3 B₃)

B₃ = 3 B₁ ∪ (1 + 3 B₂)
```

These are exact coinductive equations.  They describe **all infinite bad GST
paths simultaneously**.

A Happy Gate is absent from the `B₀` and `B₃` digit-2 branches because
`digit=2` with carry `0` or `3` is exactly the Happy Gate.

## 13.1 Structural transition matrix

Ordering the carry spaces as `(0,1,2,3)`, the graph-directed bad-space matrix is

```text
M =
[1 1 0 0]
[1 1 0 1]
[1 0 1 1]
[0 1 1 0].
```

Its characteristic polynomial is

```text
(λ - 1)(λ^3 - 2λ^2 - 2λ + 2).
```

The Perron root is

```text
ρ ≈ 2.481194304092 < 3.
```

Therefore the number of length-`N` bad prefixes grows like `O(ρ^N)`, whereas
the full ternary space has `3^N` prefixes.

The corresponding base-3 graph entropy / dimension parameter is

```text
log₃ ρ ≈ 0.827170811633 < 1.
```

So GST bad infinity is a strict thin invariant subspace of the full ternary
space.  Infinity is controlled by the graph itself; no finite witness bound is
needed for this statement.

---

# 14. Perfect-power causality theorem

Put

```text
A_s = 4^(3^s)

Q_s(b) = (A_s^b - 1) / 3^(s+1).
```

For `n ≥ 0`, define the exponent prefix

```text
p_n = b mod 3^(n+1).
```

Then

```text
b = p_n + 3^(n+1)k
```

for some natural `k`.

Using the exact 3-adic valuation identity

```text
v₃(A_s^(3^(n+1)k) - 1)
  ≥ s+n+2,
```

we obtain

```text
Q_s(b) ≡ Q_s(p_n)  (mod 3^(n+1)).
```

Hence:

```text
∀ j ≤ n,
digit(Q_s(b), j) = digit(Q_s(p_n), j).
```

**Future exponent digits cannot rewrite an already-created GST layer.**

This is the Ω∞ causality law.

---

# 15. Perfect-power tree-isometry theorem

For positive distinct natural exponents `x,y`,

```text
Q_s(x) - Q_s(y)
  =
A_s^min(x,y) *
(A_s^|x-y| - 1) / 3^(s+1)
```

up to sign.

Because `A_s` is a 3-adic unit and LTE gives

```text
v₃(A_s^h - 1) = s+1+v₃(h),
```

we obtain the exact identity

```text
v₃(Q_s(x) - Q_s(y))
  =
v₃(x-y).
```

Equivalently, for every `N`,

```text
Q_s(x) ≡ Q_s(y) (mod 3^N)
    ↔
x ≡ y (mod 3^N).
```

Thus the canonical perfect-power map is a rooted ternary-tree isometry.

This upgrades the informal "origin energy" coordinate: the exponent-origin
tree and the Navigation-Constant tree are not merely correlated.  Their
3-adic prefix distances are identical.

---

# 16. General GST affine-space automorphism

The exact origin-digit recurrence is

```text
Q_t(3u+d)
  =
K_t(d) + 3 A_t^d Q_(t+1)(u)
```

where

```text
K_t(d) = (A_t^d - 1) / 3^(t+1)
d ∈ {0,1,2}.
```

For a general GST-space point

```text
Y = z + m Q_t(u)
```

with

```text
u = 3u' + d,
```

put

```text
E  = z + m K_t(d)
r  = E mod 3
z' = (E-r)/3
m' = m A_t^d.
```

Then exactly

```text
Y = r + 3(z' + m' Q_(t+1)(u')).
```

Simultaneously the GST carry evolves by

```text
C' = floor((C + 4r)/3).
```

Therefore one Ω∞ edge consumes, in one operation:

```text
one exponent-origin ternary digit
one number-space ternary digit
one GST carry transition
one affine-residual transition.
```

This is the natural infinite transition law of the General Space Theory graph.

---

# 17. Ω∞ canonical state

A canonical infinite state can be represented by

```text
Ω =
(
  level,
  origin ray,
  origin prefix,
  perfect-power scale,
  affine offset,
  GST carry,
  GST space
).
```

Its transition is not an approximation:

```text
origin digit d := origin mod 3
origin'         := floor(origin/3)
level'          := level+1

E               := offset + scale*K_level(d)
digit            := E mod 3
offset'          := floor(E/3)
scale'           := scale*A_level^d

carry'           := floor((carry + 4*digit)/3)
space'           := classify(carry').
```

The Happy Gate remains exactly

```text
digit = 2 ∧ carry ∈ {0,3}.
```

The previous seven-axis GST graph is recovered by projecting the Ω∞ orbit onto

```text
(position,
 carry,
 space,
 digit,
 descent,
 bridge,
 cascade depth).
```

So Ω∞ is an extension of the original GST graph, not a competing graph.

---

# 18. Two-wave Ω∞ product-space control

For the two-wave product graph, track both carries

```text
(C₀,C₁)
```

for

```text
R → 4R → 16R.
```

A product edge is allowed only when neither adjacent wave has a Happy Gate.

The resulting product bad-space graph has 16 carry states.

Its transition matrix has characteristic polynomial

```text
λ^6 (λ-1)^2 (λ+1)^2
(λ^6 - 2λ^5 - 2λ^4 + 3λ^3 + λ + 1).
```

Its Perron root is

```text
ρ₂ ≈ 2.236693879327 < ρ₁.
```

The corresponding base-3 dimension parameter is

```text
log₃ ρ₂ ≈ 0.732741511413.
```

Thus coupling two consecutive bad waves makes the allowed infinite GST space
strictly thinner than the one-wave bad space.

This is a structural infinite-space result, not the experimental
creation/destruction ratio.

---

# 19. The exact global closure criterion

The old wording

```text
"prove global termination/exclusion"
```

is replaced by an invariant-space intersection theorem.

Let

```text
C_s
```

be the canonical perfect-power Ω∞ manifold generated by `Q_s`.

Let

```text
B₀
```

be the greatest-fixed-point GST bad space starting from carry zero.

Let

```text
W_nat
```

be the natural-origin component: exponent rays that are eventually zero.

Then the universal GST closure theorem has the exact form

```text
C_s ∩ B₀ ∩ W_nat = E_s
```

where `E_s` is the explicitly handled exceptional/base component.

For the two-wave theorem, replace `B₀` by the 16-state two-wave bad product
space.

This is the precise statement that must be discharged to turn the infinite
space control into the universal theorem.

---

# 20. What is now closed

```text
✓ infinite GST bad traces have an exact greatest-fixed-point description
✓ the GST bad infinity has a strict spectral/entropy bound
✓ future exponent digits cannot rewrite lower GST layers
✓ the perfect-power origin map preserves every 3-adic prefix distance
✓ the affine residual recurrence is the Ω∞ transition law
✓ one-wave and two-wave bad spaces are exact graph-directed invariant spaces
✓ the old "force infinity finite" strategy is no longer required
```

# 21. What is not yet logically implied by the above

The spectral bound says the bad invariant space is thin; it does **not** by
itself say that the canonical natural-origin orbit never enters it.

The tree-isometry says canonical origin prefixes are preserved exactly; it
does **not** by itself prove the intersection with the bad space is empty.

Therefore the remaining theorem is specifically the canonical invariant-space
separation:

```text
C_s ∩ B₀ ∩ W_nat = E_s
```

(or its two-wave product analogue).

A green Lean theorem for the universal result requires a proof of that
intersection statement.  The Ω∞ integration itself is complete.

---

# 22. Lean-facing theorem architecture

Suggested definitions:

```lean
def GSTBadStream (C : Nat) (d : Nat → Nat) : Prop :=
  ∀ n,
    let Cn := gstStreamCarry C d n
    GSTBadPair Cn (d n)

def GSTBadSpace (C : Nat) : Set (Nat → Nat) :=
  {d | GSTBadStream C d}

def gstOriginDigit (b n : Nat) : Nat :=
  b / 3^n % 3

def gstOriginPrefix (b n : Nat) : Nat :=
  b % 3^(n+1)
```

Causality:

```lean
theorem gst_navigation_constant_causality
    (s b n : Nat) :
    gstNavigationConstant s b % 3^(n+1)
      =
    gstNavigationConstant s (b % 3^(n+1)) % 3^(n+1) := by
  ...
```

Tree isometry in congruence form:

```lean
theorem gst_navigation_constant_prefix_iff
    (s x y N : Nat)
    (hs : 1 ≤ s) :
    gstNavigationConstant s x % 3^N
      =
    gstNavigationConstant s y % 3^N
    ↔
    x % 3^N = y % 3^N := by
  ...
```

Coinductive one-step law:

```lean
theorem gst_badSpace_unfold
    (C : Nat) (d : Nat → Nat) :
    d ∈ GSTBadSpace C
    ↔
    GSTBadPair C (d 0)
      ∧
    (fun n => d (n+1))
      ∈ GSTBadSpace
          ((C + 4*(d 0))/3) := by
  ...
```

Final separation theorem:

```lean
theorem gst_canonical_omega_separation :
    ∀ s b,
      1 ≤ s →
      1 ≤ b →
      canonicalOmegaRay s b ∈ GSTBadSpace 0 →
      GSTExceptionalOrigin s b := by
  ...
```

Once this last theorem is proved, Navigation follows immediately by
contraposition and the existing downstream transport can consume it.
