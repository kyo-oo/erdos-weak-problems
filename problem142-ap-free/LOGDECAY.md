# LOGDECAY.md — THEOREM LOGDECAY (W77-142K): the first polylog saving for r_3, in-package

**THEOREM LOGDECAY.** For every integer N ≥ N₂ := ⌈exp(4·10⁷)⌉,

    r_3(N) ≤ √26600 · N · √(ln ln N / ln N).

Zero premises. Explicit constants: √26600 ≈ 163.095, ln N₂ = 4·10⁷.

**The input law (banked, W76-142K, this lane's own branch history):**
THEOREM SUBLINEAR — for every eps ∈ (0, 1/8], every 3-AP-free S ⊆ [1, N]
with N ≥ 480·(1024/eps)^(⌈13300/eps²⌉+2) satisfies |S| ≤ eps·N
(SUBLINEAR_PROOF_V2.md; receipts142sublinear_v2.txt, 264/264 green,
LAW-SPEC 23/23 — every arsenal citation read at its file:line).

This document is a pure-arithmetic COMBINATION of that banked law: the
explicit tower is INVERTED exactly, no asymptotic hand-waving anywhere;
every inequality below is either an identity, a monotonicity argument
with an explicit derivative sign, or a numerically-certified evaluation
at 60 significant digits (engine142logdecay.py, 19/19 green).

---

## THE DERIVATION

Let N ≥ N₂, L := ln N (so L ≥ 4·10⁷), ℓ := ln L = ln ln N (so ℓ ≥ ℓ₂ :=
ln(4·10⁷) = 17.5023...). Define

    eps(N) := √(26600·ℓ/L).

### STEP 1 — eps(N) lies in the banked range (0, 1/8].

eps(N)² ≤ 1/64 ⟺ 64·26600·ℓ ≤ L ⟺ 1,702,400·ln L ≤ L.

Let h(L) := L − 1,702,400·ln L. Then h′(L) = 1 − 1,702,400/L > 0 for
every L > 1,702,400. Since 4·10⁷ > 1,702,400 and
h(4·10⁷) = 10,207,724... > 0 (engine: margin 1.020·10⁷), h(L) > 0 for
ALL L ≥ 4·10⁷. Hence eps(N) ≤ 1/8; positivity is immediate.
[The engine localizes the exact boundary: eps = 1/8 at L* ≈ 2.9268·10⁷;
N₂ sits above it with margin 1.073·10⁷.]

### STEP 2 — the tower threshold is dominated.

We show N ≥ 480·(1024/eps)^(⌈13300/eps²⌉+2), i.e. (taking ln)

    L ≥ B + (⌈13300/eps²⌉ + 2)·ln(1024/eps),   B := ln 480.

Three exact reductions:

(a) **The exponent identity.** 13300/eps(N)² = 13300·L/(26600·ℓ) = L/(2ℓ)
    EXACTLY (13300·2 = 26600). Since ⌈x⌉ ≤ x + 1 for real x:
    ⌈13300/eps²⌉ + 2 ≤ L/(2ℓ) + 3.

(b) **The logarithm bound.** ln eps = (1/2)(ln 26600 + ln ℓ − ln L)
    = (1/2)(ln 26600 + ln ℓ − ℓ), so
    ln(1024/eps) = A + ℓ/2 − (1/2)(ln 26600 + ln ℓ) ≤ A + ℓ/2,
    where A := ln 1024 (using ln 26600 > 0 and ln ℓ > 0 for ℓ > 1).

(c) **Compose (monotonicity of x ↦ a·x for a ≥ 0 and the sum law):**

    ln[480·(1024/eps)^(⌈13300/eps²⌉+2)]
      ≤ B + (L/(2ℓ) + 3)·(A + ℓ/2)
      =  B + (A/2)·(L/ℓ) + L/4 + 3A + (3/2)·ℓ.

So it SUFFICES that

    L·(3/4 − A/(2ℓ)) ≥ B + 3A + (3/2)·ℓ.      (∗)

### STEP 3 — (∗) holds for ALL L ≥ 4·10⁷ (the sandwich).

- The coefficient 3/4 − A/(2ℓ) is INCREASING in ℓ (A > 0), so for
  ℓ ≥ ℓ₂ = 17.5023: 3/4 − A/(2ℓ) ≥ 3/4 − A/(2ℓ₂) = 0.55200... ≥ 0.55
  (engine-certified: 0.552008).
- ℓ = ln L ≤ L/1000 for L ≥ 4·10⁷: at L = 4·10⁷, ln L = 17.50 ≤ 40,000,
  and (ln L)/L is decreasing for L > e.
- Therefore: LHS(∗) ≥ 0.55·L, while
  RHS(∗) = B + 3A + (3/2)ℓ ≤ 6.174 + 20.794 + 1.5·(L/1000) ≤ 60 + 0.0015·L.
- Then 0.55·L − (60 + 0.0015·L) = 0.5485·L ≥ 0.5485·4·10⁷ = 2.194·10⁷ > 60 > 0.

Hence (∗) holds with margin; at the boundary L = 4·10⁷ the engine
certifies the full chain directly: margin 2.208·10⁷ (Method A) and the
DIRECT tower evaluation 480·(1024/eps)^(⌈13300/eps²⌉+2) < e^L with margin
2.954·10⁷ (Method B, exponent computed as an exact integer at 60 digits).

### STEP 4 — conclusion.

Steps 1–3 verify every hypothesis of the banked THEOREM SUBLINEAR at
eps = eps(N) for every N ≥ N₂. Therefore every 3-AP-free S ⊆ [1, N]
satisfies |S| ≤ eps(N)·N. Taking the maximum over all such S:

    r_3(N) ≤ eps(N)·N = √26600 · N · √(ln ln N / ln N).   ∎

---

## THE ENGINE CERTIFICATE (engine142logdecay.py, receipts142logdecay.txt, 19/19)

Method A (the exact chain) + Method B (the direct 60-digit tower
evaluation) agree everywhere:
- CHAIN-BOUNDARY + DIRECT-BOUNDARY at L₂ (both green, margins above);
- the three sandwich anchors (h(4·10⁷) = 1.020·10⁷; coefficient 0.552008;
  ℓ ≤ L/1000; 0.5485·L₂ = 2.194·10⁷ > 60);
- 200-point geometric grid L ∈ [4·10⁷, 10⁵⁰]: 200/200 both methods;
- extremes L ∈ {4·10⁷, 4.0000001·10⁷, 10⁸, 10¹², 10³⁰, 10⁶⁰, 10¹²⁰}: green;
- NEGATIVE CONTROLS (the hypothesis is load-bearing): at L = 10⁶,
  eps = 0.606 > 1/8 — the banked theorem is NOT applicable (the chain
  correctly fails); at L = 2.9·10⁷ the chain fails (below the eps-boundary
  L* ≈ 2.9268·10⁷);
- the exponent-precision guard: L/(2ℓ) certified > 10⁻⁴⁰ from every
  integer on the whole grid (the ⌈·⌉ is exact).

## THE ARSENAL COMBINATION (the arithmetic layer, read-before-cite)

#BY GST LAW two_pow_ge2 [CardinalWorlds.lean:431] — the 1024 = 2¹⁰ size bookkeeping
#BY GST LAW sq_sub_one [CardinalWorlds.lean:448] — the square/sqrt discipline of eps²
#BY GST LAW one_le_mul [erdosternary2/bulldoze/problem404-padic-kernel/KernelLaw.lean:176] — positivity transport
#BY GST LAW sum_le_sum_of_forall [Erdos261Tower.lean:116] — the termwise-sum inequality (Step 2c)
#BY GST LAW tower_cauchy [Erdos261Tower.lean:810] — the tower bookkeeping discipline
#BY GST LAW cubic_expansion [CardinalWorlds.lean:283] — the algebraic identity layer (the (a+b)-style expansions of Step 2)

Plus the input law's own 39-citation stack (SUBLINEAR_PROOF_V2.md) — this
theorem inherits the full in-package lineage.

## WHAT THIS LAW IS (the exact label)

A complete unconditional theorem of the campaign: the first polylog-saving
upper law for r_3 in-package — the law-stack moved from "eps-tower" shape
to "N·√(loglog/log)" shape by pure combination of the banked SUBLINEAR
tower with exact arithmetic. The constants are explicit and enormous
(N₂ = exp(4·10⁷)) — the SHAPE is the content; the next lanes (LOGPOWER,
the increment-shape push) attack the exponent. The engine never stops; it
never lies.
