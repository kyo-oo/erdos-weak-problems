# DISCOVERY — Task 2-f: the affine-channel provider `FourPowerDirectNoBadAffineChannelOne`

Curated mirrors in `/home/z/agent-work/src/` were diff-verified byte-identical to the live
Lean project `/home/z/erdosternary2/` (diff run on `GSTFourPowerAffineChannelAutomaton.lean`,
`GSTFourPowerDirectExistenceProviderPipeline.lean`, `GSTFourPowerAffineBadState.lean`: IDENTICAL).
Files only present live (peel/classifier/renormalization/period files) are cited at their live
path. All signatures below are verbatim from source.

Toolchain: Lean 4.33 (`leanprover/lean4:v4.33.0`) + Mathlib, per `lean-toolchain`.

---

## 1. The BadChannel predicate (the thing to negate)

`/home/z/erdosternary2/GSTFourPowerAffineChannelAutomaton.lean` lines 27–29
(mirror `/home/z/agent-work/src/GSTFourPowerAffineChannelAutomaton.lean:27-29`):

```lean
/-- Global badness of one affine channel. -/
def BadChannel (c x : Nat) : Prop :=
  ¬ PairCommonTwo x (4*x + c)
```

`PairCommonTwo`, `/home/z/erdosternary2/GSTFourPowerAffineBadState.lean` lines 14–16
(mirror `src/GSTFourPowerAffineBadState.lean:14-16`):

```lean
/-- Common ternary digit two at one coordinate of an arbitrary pair. -/
def PairCommonTwo (x y : Nat) : Prop :=
  ∃ j : Nat, digit3 x j = 2 ∧ digit3 y j = 2
```

with `digit3 (R p : Nat) : Nat := R / 3^p % 3`
(`/home/z/erdosternary2/GSTFourPowerDirectResidue.lean:9`).

So `BadChannel 1 (affineOrbit K)` means: the pair `(affineOrbit K, 4*affineOrbit K + 1)`
has **no** ternary coordinate `j` at which **both** numbers carry digit `2`.

## 2. The affine orbit

`/home/z/erdosternary2/GSTFourPowerAffineOrbit.lean` lines 11–14 (mirror identical):

```lean
/-- Affine orbit attached to the four-power exponent: A_0 = 0 and A_{K+1} = 4 A_K + 1. -/
def affineOrbit : Nat → Nat
  | 0 => 0
  | K + 1 => 4 * affineOrbit K + 1
```

Key verified identities (same file):
- `theorem four_pow_eq_one_plus_three_affineOrbit (K : Nat) : 4^K = 1 + 3 * affineOrbit K` (lines 22–23)
  — the orbit is the **principal-triadic-unit chart** of `4^K`.
- `theorem four_pow_digit_affine_shift (K q : Nat) : digit3 (4^K) (q + 1) = digit3 (affineOrbit K) q` (lines 32–33)
  — the orbit's digits are the digits of `4^K` above row 0, verbatim.
- `theorem affineOrbit_forward (K : Nat) : affineOrbit (K+1) = 4 * affineOrbit K + 1` (lines 70–72).

## 3. The channel automaton (states, edges, transitions)

`/home/z/erdosternary2/GSTFourPowerAffineChannelAutomaton.lean` (mirror identical):

```lean
/-- Least ternary digit of a channel source. -/
def lowDigit (x : Nat) : Nat := x % 3                                    -- line 12
/-- One-digit ternary tail. -/
def tail3 (x : Nat) : Nat := x / 3                                        -- line 15
/-- Low output digit of the affine channel `x ↦ 4x+c`. -/
def channelOut (c a : Nat) : Nat := (4*a + c) % 3                         -- line 18
/-- Carry/channel state passed to the next ternary digit. -/
def channelNext (c a : Nat) : Nat := (4*a + c) / 3                        -- line 21
/-- The low pair is already a common two. -/
def lowSuccess (c x : Nat) : Prop :=
  lowDigit x = 2 ∧ channelOut c (lowDigit x) = 2                          -- lines 24–25
```

The four channel states are exactly the carry values `{0,1,2,3}` of the base-3 ×4
multiplication machine (`directCarry4 R p = (4 * (R % 3^p)) / 3^p < 4`,
`/home/z/erdosternary2/GSTFourPowerDirectAdditionCarry.lean:11-12,25`;
`digit3 (4*R) p = (digit3 R p + directCarry4 R p) % 3`, same file line 97).

Verified transition table (all in `GSTFourPowerAffineChannelAutomaton.lean`):

```lean
theorem badChannel_iff (c x : Nat) :
    BadChannel c x ↔
      ¬ lowSuccess c x ∧
        BadChannel (channelNext c (lowDigit x)) (tail3 x)                -- lines 149–152

theorem badChannel_zero_iff (x : Nat) :
    BadChannel 0 x ↔
      (lowDigit x = 0 ∧ BadChannel 0 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 1 (tail3 x))                          -- lines 158–161

theorem badChannel_one_iff (x : Nat) :
    BadChannel 1 x ↔
      (lowDigit x = 0 ∧ BadChannel 0 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 1 (tail3 x)) ∨
      (lowDigit x = 2 ∧ BadChannel 3 (tail3 x))                          -- lines 168–172

theorem badChannel_two_iff (x : Nat) :
    BadChannel 2 x ↔
      (lowDigit x = 0 ∧ BadChannel 0 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 2 (tail3 x)) ∨
      (lowDigit x = 2 ∧ BadChannel 3 (tail3 x))                          -- lines 179–183

theorem badChannel_three_iff (x : Nat) :
    BadChannel 3 x ↔
      (lowDigit x = 0 ∧ BadChannel 1 (tail3 x)) ∨
      (lowDigit x = 1 ∧ BadChannel 2 (tail3 x))                          -- lines 190–193
```

Master recursion (lines 111–115):

```lean
theorem pairCommonTwo_channel_iff (c x : Nat) :
    PairCommonTwo x (4*x+c) ↔
      lowSuccess c x ∨
        PairCommonTwo (tail3 x)
          (4 * tail3 x + channelNext c (lowDigit x))
```

Gate arithmetic (from the defs): `channelOut c 2 = (8 + c) % 3 = 2 ↔ c % 3 = 0`, i.e. with
`c < 4` exactly `c ∈ {0, 3}` — **the digit-2 gate: digit 2 with carry ∈ {0,3}**, the unique
right chord of the maximal 36-state base-6 cell `55₆ = 35 = 6² − 1` (masses (5,5)) in the
six-adic universe (monolith lore verified by sibling slice 2-b:
`gst_scoped_two_digit_happy_gate_right_chordS`).

## 4. The provider (DECLARED FINAL TARGET)

`/home/z/erdosternary2/GSTFourPowerDirectExistenceProviderPipeline.lean` lines 63–66
(mirror `src/GSTFourPowerDirectExistenceProviderPipeline.lean:63-66`):

```lean
/-- Goal C / Chat-2 gate: kill exactly the bad affine channel that is equivalent
    to a direct `CommonTwo` counterexample. -/
def FourPowerDirectNoBadAffineChannelOne : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬ BadChannel 1 (affineOrbit K)
```

## 5. The provider→existence bridge (exact signature)

Same file, lines 101–105:

```lean
/-- Chat-2 production gate in the final affine-automaton language. -/
theorem fourPowerDirectExistence_noAxiom_from_no_bad_affine_channel_one
    (hNoBad : FourPowerDirectNoBadAffineChannelOne) :
    FourPowerDirectExistence := by
  exact chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one.mpr hNoBad
```

(`FourPowerDirectExistence := ∀ K : Nat, 5 ≤ K → K ≠ 7 → CommonTwo K`,
`/home/z/erdosternary2/GSTFourPowerDirectExistence.lean:26-27`;
`CommonTwo K := ∃ p : Nat, 1 ≤ p ∧ digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2`, same file lines 19–22.)

Underlying equivalence, `/home/z/erdosternary2/GSTFourPowerDirectChat2Application.lean` lines 33–35 and 160–162:

```lean
theorem chat2_noCommonTwo_iff_bad_channel_one (K : Nat) :
    (¬ CommonTwo K) ↔ BadChannel 1 (affineOrbit K)

theorem chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one :
    FourPowerDirectExistence ↔
      ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬ BadChannel 1 (affineOrbit K)
```

Chain of equivalences making the provider *literally* the axiom in automaton language
(`GSTFourPowerAffineClassifierBridge.lean:25-38`):
`commonTwo_iff_channel_one : CommonTwo K ↔ PairCommonTwo (affineOrbit K) (4 * affineOrbit K + 1)`;
`noCommonTwo_iff_badChannel_one : (¬ CommonTwo K) ↔ BadChannel 1 (affineOrbit K)`.

## 6. Six-adic laws most relevant to channel goodness

All verbatim, `/home/z/erdosternary2/GSTGraphV2SixAdicSynchronizedShadows.lean` unless noted:

```lean
theorem six_iso_iff_synchronized_shadows
    {k : Nat} {x y : Int} :
    SixAdicIsoAt k x y ↔
      DyadicShadowAt k x y ∧ TriadicShadowAt k x y                    -- lines 44–47

theorem triadic_shadow_mul_four_pow_iff
    (k t : Nat) (x y : Int) :
    TriadicShadowAt k ((4 : Int)^t * x) ((4 : Int)^t * y) ↔
      TriadicShadowAt k x y                                           -- lines 68–71  ← ×4^t is an EXACT TRIADIC ISOMETRY (4 is a unit mod 3^k)

theorem dyadic_shadow_mul_four_pow_iff
    (k t : Nat) (hkt : 2*t ≤ k) (x y : Int) :
    DyadicShadowAt k ((4 : Int)^t*x) ((4 : Int)^t*y) ↔
      DyadicShadowAt (k-2*t) x y                                      -- lines 93–96  ← dyadic depth shifts by exactly 2t

theorem dyadic_shadow_mul_four_pow_of_saturated
    (k t : Nat) (hkt : k ≤ 2*t) (x y : Int) :
    DyadicShadowAt k ((4 : Int)^t*x) ((4 : Int)^t*y)                  -- lines 147–149 ← dyadic half saturated: no residual condition

theorem six_iso_mul_four_pow_iff_truncated_skew_shadows
    (k t : Nat) (x y : Int) :
    SixAdicIsoAt k ((4 : Int)^t*x) ((4 : Int)^t*y) ↔
      DyadicShadowAt (k-2*t) x y ∧ TriadicShadowAt k x y              -- lines 188–191 ← THE SKEW: triadic reflected, dyadic only shifted

theorem six_pow_dvd_four_pow_mul_sub_iff_truncated
    (k t : Nat) (x y : Int) :
    (6 : Int)^k ∣ (4 : Int)^t*(x-y) ↔
      (3 : Int)^k ∣ x-y ∧ (2 : Int)^(k-2*t) ∣ x-y                     -- lines 199–202
```

Base-6 resolution tree (`GSTGraphV2SixAdicOntologicalGeometry.lean` + `…Laws.lean`):

```lean
def SixAdicIsoAt (k : Nat) (x y : Int) : Prop :=
  ∃ q : Int, x - y = (6 : Int) ^ k * q                                -- Geometry lines 23–24
def sixChildCenter (k : Nat) (c : Int) (j : Fin 6) : Int :=
  c + (j.val : Int) * (6 : Int) ^ k                                   -- Geometry lines 40–41 (Fin-6 children)
def physicalEnergy (P) : Int := (4 : Int) ^ P.x4Phase * (P.sourceEnergy : Int)  -- Geometry lines 50–52

theorem six_child_center_in_parent (k : Nat) (c : Int) (j : Fin 6) :
    sixChildCenter k c j ∈ SixAdicBall k c                            -- Laws lines 166–167
theorem six_child_centers_injective (k : Nat) (c : Int) :
    Function.Injective (sixChildCenter k c)                           -- Laws lines 174–175
theorem x4_chart_preserves_six_iso (k t E F : Nat)
    (h : SixAdicIsoAt k (E : Int) (F : Int)) :
    SixAdicIsoAt k ((4 : Int) ^ t * (E : Int)) ((4 : Int) ^ t * (F : Int))  -- Laws lines 201–206
theorem six_iso_mul_iff_of_mod_inverse {k a b c x y : Int}
    (hinv : b * a = 1 + (6 : Int)^k * c) :
    SixAdicIsoAt k (a*x) (a*y) ↔ SixAdicIsoAt k x y                   -- UnitIsometry lines 46–49
theorem six_scale_exact_iff {k : Nat} {x y : Int} :
    SixAdicIsoAt (k+1) (6*x) (6*y) ↔ SixAdicIsoAt k x y               -- UnitIsometry lines 58–59
```

Production-lattice laws identifying the channel edges with the lattice's exact x4 edges
(`/home/z/erdosternary2/GSTGraphV2ProductionLaws.lean`):

```lean
theorem horizontal_digit_exact (E t p : Nat) :                        -- lines 17–21: the horizontal edge is the x4 DIGIT edge
    GST2DMixedEmergence.outDigit (…cell E t p…).seven.carry (…).seven.digit =
      (GSTGraphV2Production.cell E (t+1) p).seven.digit
theorem vertical_carry_exact (E t p : Nat) :                          -- lines 26–30: the vertical edge is the ternary CARRY edge
    GST2DMixedEmergence.nextCarry … = (…cell E t (p+1)…).seven.carry
theorem navigation_nullspace_flux_exact (E t p : Nat) :               -- lines 35–38: 4*(E % 3^p) = nullspace + 3^p*carry
theorem origin_frame_phased_state_exact (t n K x p : Nat) :           -- lines 45–50: full cell = re-phased U-tail cell (no re-phasing escape)
theorem residual_right_absolute_state_exact (s k m p : Nat) :         -- lines 134–150: right endpoint = absolute perfect-power sheet (cell 1 parentExponent p)
```

## 7. Third-wave machinery already verified (the new-maths layer the axiom drops into)

- **Lockstep (automaton reads the exponent's own trits)** —
  `/home/z/erdosternary2/GSTFourPowerAffineClassifierBridge.lean`:
  `theorem affineOrbit_mod_three (K : Nat) : affineOrbit K % 3 = K % 3` (lines 15–16);
  `theorem noCommonTwo_low_trit_branch (K : Nat) : (¬ CommonTwo K) ↔ (K % 3 = 0 ∧ BadChannel 0 (tail3 (affineOrbit K))) ∨ (K % 3 = 1 ∧ BadChannel 1 (tail3 (affineOrbit K))) ∨ (K % 3 = 2 ∧ BadChannel 3 (tail3 (affineOrbit K)))` (lines 49–53).
- **Exponent-trit peel** — `/home/z/erdosternary2/GSTFourPowerAffineExponentPeel.lean`:
  `peel0 x := x + 3*x^2 + 3*x^3` (line 12), `peel1 x := 4*x + 12*x^2 + 12*x^3` (line 15),
  `peel2 x := 1 + 16*x + 48*x^2 + 48*x^3` (line 18);
  `affineOrbit_three_mul : affineOrbit (3*q) = 3 * peel0 (affineOrbit q)` (21–22);
  `digit_peel_zero/one/two` (54, 65, 76); `peel0_affine_succ : peel0 (4*x+1) = 4*peel2 x + 3` (115–116).
- **Peel classifier** — `/home/z/erdosternary2/GSTFourPowerAffinePeelClassifier.lean`:
  `tail3 (affineOrbit (3*q)) = peel0 (affineOrbit q)` etc. (17–35);
  `lowDigit (peel0 (affineOrbit q)) = q % 3`, `lowDigit (peel1 …) = q % 3`,
  `lowDigit (peel2 …) = (q+1) % 3` (78, 84, 90 — branch 2 twists the read by one).
- **Two-trit row-two kill** — `/home/z/erdosternary2/GSTFourPowerAffineTwoTritClassifier.lean`:
  `commonTwo_three_mul_of_q_mod_three_two (q) (hq : q % 3 = 2) : CommonTwo (3*q)` (46–47);
  `commonTwo_three_mul_add_two_of_q_mod_three_one (q) (hq : q % 3 = 1) : CommonTwo (3*q+2)` (54–55);
  surfaced as `chat2_no_bad_affine_channel_one_of_mod9_five_or_six (K) (hK : K % 9 = 5 ∨ K % 9 = 6) : ¬ BadChannel 1 (affineOrbit K)` (Chat2Application lines 126–131).
- **Base band** — `/home/z/erdosternary2/GSTFourPowerDirectExistenceNoAxiom.lean`:
  `theorem commonTwo_five : CommonTwo 5` (line 57), `theorem commonTwo_six : CommonTwo 6` (line 62), both `norm_num` on `digit3`;
  `fourPowerDirectExistence_from_physical_happy_ge_three` (line 69) closes the 5–7 band internally.
- **Renormalization (star-crusher)** — `/home/z/erdosternary2/GSTFourPowerAffineRenormalizedOrbit.lean`:
  `renormOrbit q := peel0 (affineOrbit q)` (line 16);
  `theorem renormOrbit_succ (q : Nat) : renormOrbit (q+1) = 64 * renormOrbit q + 7` (36–37);
  `renorm_chain_closes : 4 * (16 * renormOrbit q + 1) + 3 = renormOrbit (q+1)` (61–64).
- **Multiscale self-similarity** — `/home/z/erdosternary2/GSTFourPowerMultiscaleRenormalization.lean`:
  `theorem scaleOrbit_exact (m : Nat) : ∀ q : Nat, 4^(3^m * q) = 1 + 3^(m+1) * scaleOrbit m q` (20–21);
  `scaleOrbit_one_succ : scaleOrbit 1 (q+1) = 64 * scaleOrbit 1 q + 7` (83–84).
- **Prefix isometry / exact exponent period** — `/home/z/erdosternary2/GSTFourPowerAffinePrefixIsometry.lean`:
  `theorem pow4_modeq_iff_exponent_modeq (p a b : Nat) : 4^a ≡ 4^b [MOD 3^(p+1)] ↔ a ≡ b [MOD 3^p]` (19–20);
  `theorem affineOrbit_residue_eq_iff_exponent_residue_eq (p a b : Nat) : affineOrbit a % 3^p = affineOrbit b % 3^p ↔ a % 3^p = b % 3^p` (99–104)
  — the affine orbit loses **no** ternary prefix information: it is an exact 3-adic prefix isometry of the exponent.
- **Obstruction bundle on any bad channel** — `Chat2Application.lean` lines 112–123:
  `chat2_bad_affine_channel_one_obstruction_bundle (K) (hBad : BadChannel 1 (affineOrbit K))`
  yields the row-two/row-three/row-four/parametric-prefix obstruction bundle.
- **Exception set (ground truth, slice 2-c, exact big-int computation)**:
  `{K : ¬ CommonTwo K} = {0,1,2,3,4,7}` — so `K = 7` is the *unique* genuine bad-channel-1 orbit
  in the range `K ≥ 5`, and `5 ≤ K` is exactly where source digit-twos first exist
  (`4^4 = 256 = 100111₃` has no digit 2 at all; `affineOrbit 5 = 341 = 110122₃` does).
