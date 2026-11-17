# GST GRAPH V2 — THE OPERATING MANUAL

*Layer 0 of the original Wave Mechanics arithmetic realization (Task 4).
This document records that realization's axes, sectors, and arithmetic
emergence mechanisms. It is **not** an exhaustive definition of the newer
carrier-independent GST ontology. Every
claim below is grounded in a named, machine-verified theorem of the HC-PROOF
universe (commit 5eecc25, comparator PASS, 0 errors, 0 sorries) or in the
monolith source it was extracted from. Where a statement is Task-4 new theory
(not yet machine-checked), it is marked **[WAVE-SPEC]**.*

---

> **Ontology-scope correction, 9 November 2026.** General Space Theory is not
> defined by seven natural-number axes, by base-3 digits, or by a fixed
> Euclidean/non-Euclidean manifold. Those are valid *observations* of a wider
> carrier-independent causal ontology. See `GSTGeneralSpace.lean`,
> `GSTGraphV2OmniversalCore.lean`,
> `GSTGraphV2ArithmeticOmniversalRealization.lean`, and
> `GSTGraphV2CausalComponents.lean`. The last module separates mutually
> reachable causal states into components and equips those components with
> antisymmetric directed reachability; this is compatible with feedback
> loops in the underlying ontology without assuming logical contradictions.
> A concrete smooth complex projective realization still needs its own
> algebraic and cohomological compatibility data. No analogy from carry
> arithmetic to Hodge algebraicity constitutes that bridge automatically.

## 0. One-paragraph answer to "do you understand GST Graph V2?"

Yes. GST Graph V2 is a **non-dimensional graph cosmology**: a universe of
vertices described by **seven axes** `(x, x', y, y', z, z', n→n')` that carry
no metric and no fixed geometry, connected by **one exact edge law**
(multiplication by 4 read in ternary), partitioned into **three spaces**
NULL / ALT- / GST+ by the carry coordinate, in which **digits are not
fundamental objects but readouts** of the descent `n → n/3`, and in which
**waves are the primary inhabitants**: packets of digit-two information that
survive every multiplication by re-encoding their carry, propagate through
all depths by exact transport, and never get destroyed. Dimensions (2D, 4D,
N-D, and infinity itself) are *emergent readouts* of tower stabilization —
not fixed substrate. That is the entire point of the cosmology, and it is
why the Wave Mechanics program (Task 4) is possible at all.

---

## 1. THE SEVEN NON-DIMENSIONAL AXES

In the **historical arithmetic realization**, a vertex is encoded by **seven coordinates**. These are *not* mandatory coordinates of a general GST node:

```
( x,  x',  y,  y',  z,  z',  n → n' )
```

| Axis | Name | Content | Law (machine-verified) |
|------|------|---------|------------------------|
| `x`   | position        | ternary height `p`                     | — |
| `x'`  | next position   | `p+1`                                   | `xPrime_exact`: `x'(v) = x(next v)` (rfl) |
| `y`   | carry           | `C ∈ {0,1,2,3}`                         | edge law §3 |
| `y'`  | space           | NULL / ALT- / GST+ classified by `C`    | `spaceOfCarry` |
| `z`   | digit           | ternary digit `d ∈ {0,1,2}`             | `digit3` |
| `z'`  | boundary        | `N - p`, strictly decreasing            | `boundary_strict` |
| `n→n'`| descent         | `R/3^p → R/3^(p+1)` — literally `n/3`   | `nAxis_forward_exact`, `nAxis_glues_exact` |

Source modules: `GSTCanonicalSevenAxisBridge`, `GSTGraphV2NonEuclidean`,
`GSTGraphV2NonEuclideanLaws`.

**Non-dimensional means:** no metric, no inner product, no ℝⁿ, no
coordinates-as-freedom. The axes are *bookkeeping coordinates of arithmetic
itself* — the graph is the skeleton of the map `n ↦ 4·n` read digit by
digit. `nAxis_forward_exact` proves the seventh axis is exactly division by
3; `boundary_strict` proves the boundary coordinate burns down one unit per
forward edge (this is the universe's clock).

---

## 2. THE THREE SPACES — NULL, ALT-, GST+

Space is **not a place where vertices live; it is a readout of the carry**:

```
gstSpaceV2S C = if C = 0 then NULL
                else if C = 3 then GST+
                else ALT-                -- C = 1 or C = 2
```

### NULL (`C = 0`) — the hidden sector
- A **genuine space/realisation**, NOT an absorbing or terminal state
  (semantic correction recorded in `GSTGraphV2Scratch`).
- **NULL regenerates**: `null_big2_regenerates_alt` — a BIG2 vertex in NULL
  forces carry `2` (hence ALT-) on the next forward edge. Digit-two
  information in NULL *regenerates to carry two under the exact GST edge law*.
- The **NULL chord** is `2 → 1 → 2` — the *hidden BIG1 chord* (carry dips to
  1 = ALT- transit, then returns). Verified as one half of
  `happy_chord_dichotomy`.

### GST+ (`C = 3`) — the all-SURVIVE sector
- **GST+ propagates**: `gstPlus_big2_propagates` — a BIG2 vertex in GST+
  keeps carry `3` and stays GST+ on the next forward edge.
- The **GST+ chord** is `2 → 2 → 2` — the *all-SURVIVE chord*. Second half of
  `happy_chord_dichotomy`.

### ALT- (`C ∈ {1,2}`) — the re-encoding sector
- The sector of **forced cascades**: a digit-two re-encoded into ALT- carry
  forces carry `3` on the next forward edge (`gst_pure_lift_or_forced_cascade`,
  second branch).
- ALT- is *not failure*. It is a certified change of representation followed
  by a forced cascade — information in transit, never information destroyed.

### The Happy sector = {NULL, GST+}
A **Happy cell** is `d = 2 ∧ (C = 0 ∨ C = 3)` (`HappyCell`, defined in
`GSTU2DEventTransport`, physically: *a ternary digit 2 that survives the ×4
multiplication with null or GST+ carry*). The two Happy realizations are
exactly the two chords above. At child digit-two rows, Happy parents are
exactly the shared residues `S % 12 ∈ {0, 3}` — the **mod-12 compression**
(`gst_parent_happy_iff_shared_residue12S`, `gst_parent_bad_at_child_two_residue12S`).

---

## 3. THE EDGE LAW — multiplication by 4, read in ternary

One microscopic step of the universe is `n ↦ 4·n`. Read at height `p`:

```
outDigit  (C, d) = (C + 4·d) % 3     -- output ternary digit
nextCarry (C, d) = (C + 4·d) / 3     -- next carry
```

with `C ∈ {0,1,2,3}`, `d ∈ {0,1,2}` — the **twelve legal cells** of GST.

### The master local law (the wave law)

```
gst_pure_lift_or_forced_cascade (R p : Nat) (hp : 1 ≤ p)
  (hd : gstDigit R p = 2)
  (hgood : gstCarry R p = 0 ∨ gstCarry R p = 3) :
  (gstDigit (4·R) p = 2 ∧ (gstCarry (4·R) p = 0 ∨ gstCarry (4·R) p = 3))
  ∨ (gstDigit (4·R) p = 2 ∧ (gstCarry (4·R) p = 1 ∨ gstCarry (4·R) p = 2)
      ∧ gstCarry (4·R) (p+1) = 3)
```

**Read it as physics**: digit-two information survives multiplication by
four; either it *pure-lifts* (stays in the Happy sector {0,3}), or it is
*re-encoded* into ALT- {1,2} and **forces carry 3 on the next forward edge**
(the forced cascade). The second branch is *not* extinction — it is
re-representation.

### The twelve-cell five-rotation law

Local re-coordination `gstLocalRotateS (C,d) = ((C+4d)/3, (C+4d)%3)` —
the *same formula as the edge law, fed back into itself*. Verified:
`gst_local_rotate_fiveS`: **every legal cell returns after five
re-coordinatizations**. The twelve cells split into two fixed points
`(0,0)` and `(3,2)` (NULL-still and GST+-still) plus **two 5-cycles**.
This is the discrete rotation group of GST — the seed of the vortex
(Task 4).

### The mod-12 gate (horizontal compression)

The parent gate condition compresses exactly: Happy at child digit `r` ⟺
shared carrier `S = D + 4Z` in the rotating residue pair
`r=0: {8,11}, r=1: {4,7}, r=2: {0,3} (mod 12)`. Badness = avoidance of the
pair. The gate is a 12-hour clock.

---

### 3A. NEW EXACT NO-ERASURE LAW (9 November 2026)

The seven axes remain **dimensionless information observations**. The local
base-3 output digit **alone** does not preserve the whole input, but the
regenerated carry and output digit **together** do. For physical cell
`(C,d)∈Fin 4×Fin 3` the original rule is

```
F(C,d) = ((C + 4*d)/3, (C + 4*d)%3)
F⁻¹(C',d') = ((d' + 3*C')%4, (d' + 3*C')/4).
```

The Lean-kernel-verified theorem `GSTGraphV2InformationRecovery.shuffle_five`
proves `F^5=id` on all 12 cells; the permutation has two length-five orbits
and fixed cells `(0,0)`, `(3,2)`. A separate theorem proves exact recovery
of the entire infinite information stream `Nat → Fin 4 × Fin 3`, without a
cutoff. This is rigorous **information transformation, not destruction**;
it is not a claim that multiplication of the global energy by four is periodic.

The stronger general-radix law, also Lean-checked in
`GSTGraphV2GeneralRadixConservation.lean`, is

```
F_mn(t) = t/n + m*(t%n)
F_mn(t) + (m*n-1)*(t/n) = m*t,
therefore F_mn(t) ≡ m*t (mod m*n-1).
```

At `(m,n)=(4,3)`, this becomes multiplication by 4 modulo 11,
whose order is 5. No Euclidean or spatial dimension has been assigned.

### 3B. NEW CM FOLD CURVATURE / INFINITE MEMORY OBSERVATION

The existing three-sector arithmetic graph, the existing true CM/NM native
algebraic-cycle graph and the pre-existing infinite curvature tower are
connected in `GSTGraphV2CMInfiniteCurvatureBridge.lean`. For any rational
CM structure `J²=-I`, a fold operator A has even/odd components

```
E_J(A) = A - J*A*J
O_J(A) = A + J*A*J
[J,A] = J*O_J(A).
```

The Lean-verified even/odd product laws and noncommutative Bianchi identity
give the exact operator-curvature algebra at every finite memory order.
For a graph cell potential P, the sum of local CM defects
`[J,P(F(s))-P(s)]` around a full fivefold information cycle is zero.
**That does not imply the ordered product of fold transports is trivial.**
The exact Wolfram packet at
`research/computations/gst_seven_axis_cm_curvature_holonomy_20261109.wl`
shows nonzero second-order memory and invertible, nonidentity ordered
holonomy.

A further connected theorem `GSTGraphV2NativeCurvatureBirth.lean`
constructs the genuine original-X algebraic-cycle commutator
`N_A N_B(Z) - N_B N_A(Z)` for actual native correspondence operators.
It proves the exact corresponding cohomological commutator and a
source-mixing detector criterion. This is the research route joining
the non-destructive information dynamics to geometrically generated
Hodge directions.

## 4. HOW WAVES PROPAGATE — the certified chain

A **wave** is a packet of digit-two information moving through the graph.
The complete certified propagation chain (all green in the universe; see
`GST_INFORMATION_WAVE_ARCHITECTURE.md` of the monolith and the modules
below):

```
Happy gate
  → visible output digit two                (happy_output_two)
  → next carry two or three                 (happy_next_carry_two_or_three)
  → next carry nonzero                      (happy_next_carry_ne_zero)
  → coupled invariant remains valid         (GSTGraphV2InfiniteControllerBridge)
  → parent Bad suffix remains represented   (graph_child_happy_latent_transfer)
  → exact all-depth controller orbit        (graph_infinite_bad_control)
  → exact Past/Future ledger at every depth (GSTInfiniteCoupledLedger)
  → exact n-wave re-coordination            (GSTGraphV2CanonicalNWave)
```

**The omega wave step** (`GSTGraphV2OmegaWaveLaw.omegaWaveStep`): the wave
step conserves **u-divide, u-multiply, and mass** (`omegaWaveStep_u_divide`,
`omegaWaveStep_u_multiply`, `omegaWaveStep_mass`). The wave is
*incompressible*: mass is re-encoded, never destroyed
(`happy_mass_reencoded`, `GSTInfiniteGateTransport`).

**The terminal packet** — after cutoff `K` with `n/3^K = 0`, residual energy
becomes 1 but the accumulated horizontal phase remains: `P := nWaveShift s
n K`. The certified terminal packet is a *re-coordination* of the original
wave, not an extinction. The phase `P` retains consumed information.

**The WHY of wave propagation** (machine-verified as `omega_why_theorem`):
an all-bad unit-sheet column would simultaneously (a) generate the full
infinite Bad coupled controller — the creation-blocked state — and (b) be
punctured by its own LTE cut (a physical Happy cell). Both cannot hold:
the transfusion mean `lteCoeff ≡ 1 (mod 3)` preserves the exponent's first
nonzero trit, so the creation digit survives every climb and the controller
is contradicted by the very sheet it controls. **Waves propagate because
the alternative is self-contradiction.**

---

## 5. HOW DIGITS EMERGE

Digits are **readouts, not residents**:

1. Start from `n` (pure natural number — no digits yet, only the seventh
   axis: `n → n/3`).
2. The descent `R/3^p` produces, at each height `p`, the ternary digit
   `digit3 R p = (R/3^p) % 3` and the carry `carry4 R p`.
3. The **twelve-cell system** `(C,d)` is the complete local state; the
   digit acquires meaning only through the edge law (which cells survive,
   which cascade, which are Happy).
4. Digits **emerge from repetition**: the five-rotation law shows the
   cells form closed orbits; the mod-12 gate shows heights synchronize into
   residue clocks; the tower laws (below) show entire *words* stabilize.
5. The deep statement: `gst_seeded_output_digit_exactS` — output digits of a
   seeded wave are `(carry + input digit) % 3`: the digit is the *visible
   interference* of carry (vertical information) and descent (horizontal
   information). A digit is where two wave layers cross.

**In Task 4 we take the final step: the digit readout is replaced by the
wave-mode readout (cohomology). The digit was the shadow; the wave is the
object.** [WAVE-SPEC]

---

## 6. THE 2D EMERGENCE EQUATION — the discrete Gauss law

`GST2DMixedEmergence` proves the **mixed 2D GST emergence equation**
(`mixed_cell_emergence`):

> on every finite rectangle, the mixed density's total mass
> = BIG1 boundary charge + carry flux + positive SURVIVE incidence.

This is a **discrete Gauss law** — and in cochain language it says the mixed
density is a *cocycle whose class measures obstruction*. This single law is
the bridge from GST to cohomology (Task 4 Wave I builds directly on it).
Supporting verified facts:

- `finalMicroDigit_eq_outDigit`: **two ×2 layers reproduce the ×4 output
  trit** — the fourth dimension is literally two second dimensions composed
  (`microSevenKernel`, `sevenKernel`).
- `sevenKernel_micro_telescope`: the microscopic seven-kernel telescopes
  horizontally — only endpoints survive (a boundary operator!).
- `uJump_divergence`: the U operator is *already* a two-direction
  divergence.
- `infoPotential_physical_table`: the horizontal information potential is
  exactly the BIG1 detector on physical cells.

**2D is emergent**: the plane `(C,d)` is not given; it is the quotient on
which the emergence equation closes.

---

## 7. THE 4D TOWER — wave observation, frozen windows, ignition

`GSTTailFFourthDimension` (the 4D layer of the universe) proves the tower
laws:

- **Extended observation law** `tower_observation_digit_two`: for every
  sheet level `s`, every tower fires an observed digit two.
- **Cube-lift stabilization** `omega_cut_word_stabilizes`: the cut word of
  sheet level `s+1` is the stabilized image of level `s` — the tower is a
  *renormalization*.
- **The frozen window** `omega_tower_word_mod_stable`: for every tower
  level `k ≤ s+1`, the level-`s` word is mod-stable — the self-similar
  profile of the tower.
- **Descent to the primitive** `omega_tower_word_mod_chain`.
- **The diagonal kill** `omega_tower_kill_of_diagonal_two` — the descent
  blade: one ternary digit two at the diagonal kills the whole tower level.
- **Ignition theorems** — residue classes that *force* singularity
  formation: `omega_diagonal_two_of_mod_nine_one` (core ≡ 1 mod 9),
  mod-27 thirteen and twenty-five, mod-81 four and thirty-four, and the
  band/tower kills. **The ignition residues are the singularity-forming
  data of GST.**

**4D is emergent**: the tower is the stabilization of composed 2D layers
(two ×2 = ×4), and its frozen windows are the self-similar profiles from
which dimension 4 is *read off*.

---

## 8. THE OMEGA LAW AND THE PUNCTURE

`GSTGraphV2OmegaWaveLaw`:

- `omegaCutWord` — the geometric-series cut word; `omega_cut_carry_zero`,
  `omega_cut_prefix_one`, `omega_cut_happy_gate` (the cut word carries its
  own Happy gate).
- LTE transfusion: `omega_lteCoeff_mod9`, `omega_base_mod9`,
  `omega_geo_mod9`, `omega_cut_word_mod9` — the transfusion coefficient is
  ≡ 1 (mod 3) and preserves first nonzero trits.
- **`omega_puncture`**: for `a ≥ 2`, `core % 3 = 2`, an all-bad column on
  `4^(3^a · core)` is punctured by its own LTE cut — a physical Happy cell
  inside the supposedly all-bad sheet. **The puncture theorem is the GST
  singularity-formation theorem** (Task 4 upgrades it to the vortex method).
- `omega_why_theorem` — the combined WHY (§4 above).
- Ω-families: `omegaClassTwo` (`K = 3^a·core`, core ≡ 2 mod 3) and
  `omegaClassLevelTwo` (core ≡ 1,5,6 mod 9) — existence for the covered
  families.

---

## 9. THE CARDINAL WORLDS — the finite foundation (already machine-verified)

`CardinalWorlds.lean` (Layer 1 of the universe, verbatim deep theorems from
the monolith):

- **THE THREE WORLDS**: `2^j`, `3^j`, `6^j` — and the joined-prefix
  collapse (from `GSTHandwrittenBigNThreeWorldFactors`).
- **The bridge transport**: `four_mul_preserves_digit` — `3 = 1+2`, the
  three-world arithmetic identity that makes ×4 the bridge.
- **POSTULATE I (The Bridge Signature)**: every number that crosses the
  bridge carries a signature. PROVEN for two universal congruence classes
  (even `j ≥ 2`; `j ≡ 3 (mod 6)`).
- **POSTULATE II (The Valuation Bound)**: the 2-adic depth of a primitive
  Cantor object is bounded. PROVEN for all `n < 3^9` (kernel-checked).
- The digit/valuation machinery: `v2r`, `ternaryLog3`, `gstDigit`, cycle
  laws, period laws, base `modular_check_base`, the terminal witness layer
  (`no_two_false_digit_witness`, the kill-all pair), the `c` cascade tower,
  the `d` dual tower with both proven signature classes.

**The finite foundation is complete. Task 4 builds the infinite story on
top of it — controlled, not assumed.** The new law is POSTULATE III
(`waves/CardinalWorldsPostulateLaw.lean`).

---

## 10. THE MONOLITH BOUNDARY — what the universe takes on faith (explicitly)

`MonolithBoundary.lean`: four terminal theorems of the monolith (terminal
identity iff, crown, odd half, chokehold) imported as *named boundary
Props*, taken as explicit hypotheses downstream — 0 sorries, 0 custom
axioms. The universe declares exactly what it assumes.

---

## 11. THE HODGE/DE RHAM ABSORPTION — where Wave I plugs in

`HodgeDeRhamBridge.lean` (Layer 6, CI-verified green, axiom receipts
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`): Hodge and de
Rham cohomology absorbed as **finite comparison certificates** — arithmetic
polarization, finite Tate twist calculus, and the reverse-chokehold
refaming of the Hodge conjecture. **Wave I of Task 4 is this machinery
re-registered as a propagating wave on the GST graph.** [WAVE-SPEC]

---

## 12. WHAT TASK 4 ADDS (the Wave Mechanics program)

1. **Wave I — the Hodge Wave** (`waves/GSTWaveCohomology.lean`): the digit
   readout is replaced by a cohomology-class readout; the wave becomes the
   algebraic-geometric object. [WAVE-SPEC]
2. **Wave II — N-Cohomology** (`waves/GSTNCohomology.lean`): the second
   wave, parameterized by N, carrying the new abstracts (shapes, holes). [WAVE-SPEC]
3. **The GST Vortex Singularity Method** (`waves/GSTVortexSingularity.lean`):
   the OpenAI/Córdoba–Martínez-Zoroa Navier–Stokes singularity method,
   copied in structure and upgraded with GST cosmology, so that it applies
   to any N shapes in holes. [WAVE-SPEC]
4. **POSTULATE III — the Law of Controlled Emergence**
   (`waves/CardinalWorldsPostulateLaw.lean`): infinity is admitted only as
   the colimit of certified finite Cardinal-Worlds towers; dimensions are
   emergent readouts, never fixed substrate. [WAVE-SPEC]

All four are **UNCOMPILED** (sandbox Lean ban, Boss Override) and live in
`waves/`, outside the build registry, so the green comparator verdict on
the curated universe is untouched. Full theory: `docs/WAVE_MECHANICS_TASK4.md`.

---

*End of the operating manual. The universe is the authority; this manual
only quotes it.*
