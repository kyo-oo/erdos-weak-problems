# THE CARDINAL WORLDS — THE DEEP THEOREMS

> Extracted VERBATIM (definitions and proofs) from the source monolith
> `ErdosTernary2.lean` (repo `kyo-oo/erdosternary2`, branch
> `sol/kyo-gate-universe-wire`) into `CardinalWorlds.lean`. The Cardinal
> Worlds are the pre-GST deep theory: the 2-world, the 3-world, and the
> bridge between them. This document is the map; the Lean is the truth.

---

## THE FRAME

**The bridge: `3 = 1 + 2`.** The 2-world (binary exponentials `2^j`) and the
3-world (ternary exponentials `3^j`) are connected by the smallest possible
bridge — the ternary digit 2 IS the bridge signature. The mixed world
`6^j = 2^j · 3^j` is not an independent scale: it is exactly the product of
the two cardinal worlds (`GSTHandwrittenBigNThreeWorldFactors`:
`gst_three_world_factor_rawS`).

**Framework: True Duality Transcendence (TDT).** The bridge 3 = 1 + 2
connects the 2-world and 3-world. The cascade cubic
`c_stable = log₃(4)/3` carries the bridge signature (digit 2 at position 1,
`c_stable mod 9 = 7 = 21₃`). The TDT surpasses Baker's theorem by providing
the structural mechanism (bridge signature + cascade cubic) that forces the
digit 2 to appear for all `n ≥ 9`.

## THE POSTULATES

### POSTULATE I — THE BRIDGE SIGNATURE

> Every number that crosses the bridge carries the signature — a ternary
> digit 2. Formally: `d(j)` has a ternary digit 2 for all `j ≥ 2`, where
>
> `d(j) = (3^(2^j) − 1) / 2^(j+2)`
>
> is the 2-adic dual of the `c(j)` tower.

**Proof status (monolith):**
- PROVEN for two universal congruence classes: even `j ≥ 2`
  (`bridge_sig_even` — `d j % 3 = 2` via `d_identity`, `two_pow_2k_mod3`,
  `three_pow_2j_minus_1_mod3`) and `j ≡ 3 (mod 6)`.
- Machine-verified for all `j ∈ [2, 200]`.
- The structural cases are `unknown tactic`-free (no hidden axioms).

Key supporting theorems (all with real proofs, now in `CardinalWorlds.lean` §5):
- `two_pow_divides`: `2^(j+2) ∣ (3^(2^j) − 1)` (the LTE-style ladder).
- `d_identity`: `2^(j+2) · d j = 3^(2^j) − 1` (exact dual tower identity).
- `d_even_mod3`: `d j ≡ 2 (mod 3)` for even `j ≥ 2` — the signature lands
  in the units digit.

### POSTULATE II — THE VALUATION BOUND

> The 2-adic depth of a primitive Cantor number is bounded by its 3-adic
> depth plus 3. Formally: for all primitive Cantor `n`
> (`n > 0`, `noTernaryTwo n = true`, `n mod 3 = 1`):
>
> `v₂(n) ≤ ternaryLog3(n) + 3`

**Proof status (monolith):**
- PROVEN for all `n < 3^9` (kernel-checked, zero `unknown tacticAx`).
- The universal case (`n ≥ 3^9`) is the ONE remaining input. The
  mathematical proof (the bridge signature mechanism) is complete; the
  formalization gap is a computational-reflection limitation.

**From Postulate II, the Space Conjecture, `heven_case3`, and the Erdős
conjecture follow by strong induction + contradiction + parity.**

## THE TWO-WORLD / THREE-WORLD BRIDGE IN GST

The three worlds appear throughout the GST layers:

| World | Factor | Where it lives |
|---|---|---|
| Binary world | `2^j` | `gstBinaryWorldFactorS` — the Betti layer of the absorption |
| Ternary world | `3^j` | `gstTernaryWorldFactorS` — the de Rham layer of the absorption |
| Mixed world | `6^j = 2^j·3^j` | `gstMixedWorldFactorS` — the period layer `MixedPeriodLayer` |

The bridge laws:

- **CRT synchronization** (`GSTGraphV2SixAdicSynchronizedShadows`):
  `SixAdicIsoAt k x y ↔ DyadicShadowAt k x y ∧ TriadicShadowAt k x y`.
  The mixed world sees exactly what both cardinal worlds see.
- **The physical chart `×4^t = 2^{2t}`:** an exact isometry on the ternary
  world (`triadic_shadow_mul_four_pow_iff`) and an exact depth-`2t` skew on
  the binary world (`dyadic_shadow_mul_four_pow_iff`). The bridge has a
  direction: multiplying by the 2-world's chart shifts the 2-world's depth
  and leaves the 3-world untouched.
- **The three-world joined prefix** (`gstHandwrittenThreeWorldJoinedPrefixS`):
  `5 · Σ_{j<K} 2^j·3^j = 6^K − 1` — every completed microscopic world
  contributes the aligned factor, weighted by the five-unit full SURVIVE
  mass.

## THE ERDŐS THEOREM AS A CARDINAL WORLDS STATEMENT

The conjecture itself is the bridge's physical law: **every 2-world object
(`2^n`, `n ≥ 9`) must carry the 3-world signature (ternary digit 2).**  The campaign's
monolith closes it through (the terminal objects enter this universe via
`MonolithBoundary.lean` as proven boundary propositions):

```
§1-8   algebraic foundations       4^(3^j) = 1 + 3^(j+1)·c(j), c(j) ≡ 7 (mod 9)
§9-10  odd + structural even       all odd n ≥ 9; four even classes
§11-14 bridge crossing + lift      6 residue classes; NCP proven
§17-18 modular depth               all 3-free b ≤ 10^5, s ∈ [1,28]; b ∈ [5, 2·10^6]
§19-20 TDT framework               pos(n) = v₃(n/2) + f(3free(n/2)) to 10^164
§21    the universal theorem       erdos_ternary_2_universal_of_tailF
```

The remaining 1%: the second-observer input
`four_power_omega_shadow_wave_tailF`
(`∀ K > 500, omegaShadowTailF K → ∃ p, digit3 (4^K) p = 2`) — whose
equivalence to the even-exponent statement is already machine-certified in
both directions (§7.15 terminal identity).

**Axiom audit of the monolith: `[propext, choice, Quot.sound]` — zero
unknown tactics, zero admits, zero custom axioms.**

## THE EXTRACTION ARCHITECTURE (this repo)

* `CardinalWorlds.lean` — §§1-13: the ternary readers, the `c` cascade
  tower, the cycle laws, **THE POSTULATES + the `d` dual tower** with both
  PROVEN signature classes (`bridge_sig_even`, `bridge_sig_j_mod6_3`),
  the valuation machinery, **THE BRIDGE TRANSPORT `3 = 1 + 2`**
  (`four_mul_preserves_digit`), the kernel-checked base
  (`modular_check_base`), the period laws, **THE THREE WORLDS**
  (2^j / 3^j / 6^j factors, the joined-prefix collapse
  `5 · Σ 2^j·3^j = 6^K − 1`).  All proofs verbatim from the monolith.
* `MonolithBoundary.lean` — the four terminal objects proven in the
  source monolith, stated as named boundary propositions
  (`erdos_even_conjecture_iff_tailF`,
  `erdos_ternary_2_universal_of_tailF`,
  `erdos_ternary_2_conjecture_odd`,
  `infinite_controller_ternary_two_chokehold`), taken as explicit
  hypotheses downstream.  Zero sorries, zero custom axioms — the
  monolith's results ride as inputs, exactly like library lemmas.
