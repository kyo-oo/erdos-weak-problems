# PLAN — Task 2-f: THE THIRD-WAVE DERIVATION of `FourPowerDirectNoBadAffineChannelOne`

Target (verbatim, `GSTFourPowerDirectExistenceProviderPipeline.lean:65-66`):

```lean
def FourPowerDirectNoBadAffineChannelOne : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬ BadChannel 1 (affineOrbit K)
```

Proposed new file (live project): `/home/z/erdosternary2/GSTFourPowerAffineThirdWave.lean`.
All new names are prefixed `wavf_`. Lean 4.33 + Mathlib. No `sorry`/`admit`/`axiom`/`native_decide`;
`decide`/`interval_cases` only on bands < 501 (used bands: {5,6,7} and c < 4).

---

## 0. How the custom-axiom theorem sits in the six-adic universe (wave assignment)

Boss's directive: put `gst_four_power_direct_existence_inline` into the GST ontological V2
graph and watch it react. It reacts by *unfolding into three stacked waves*:

- **Wave 1 — the physical carry wave (x4 chart):** the channel automaton's states
  `{0,1,2,3}` are exactly the `×4` base-3 carry values (`directCarry4 < 4`,
  `digit3_four_mul : digit3 (4*R) p = (digit3 R p + directCarry4 R p) % 3`,
  `GSTFourPowerDirectAdditionCarry.lean:11,25,97`). Its edges are the production lattice's
  exact horizontal (digit) and vertical (carry) edges
  (`horizontal_digit_exact`, `vertical_carry_exact`, `GSTGraphV2ProductionLaws.lean:17,26`).
- **Wave 2 — the navigation/residue wave:** the row-2/3/4 towers and the parametric
  exponent-trit obstruction (`noCommonTwo_all_exponent_trit_laws`,
  `GSTFourPowerDirectExistence.lean:106`) — the survivor-tree shadow.
- **Wave 3 (NEW — this slice) — the synchronized six-adic shadow wave on the
  affine-unit chart:** `A_K = (4^K − 1)/3` is the principal-triadic-unit chart
  (`four_pow_eq_one_plus_three_affineOrbit`), the `K → K+1` phase step is the channel map
  `x ↦ 4x+1`, and the digit-2 gate is evaluated by walking this chart through the
  automaton while the six-adic universe watches: triadic shadow reflected exactly,
  dyadic shadow shifted one-way.

## 1. THE DISTINCTION THAT IMMEDIATELY PROVED ITSELF (and how it is written into Lean)

Under the established laws, the `K → K+1` phase map `×4` is:

- an **exact triadic isometry**: `triadic_shadow_mul_four_pow_iff (k t x y) :
  TriadicShadowAt k (4^t*x) (4^t*y) ↔ TriadicShadowAt k x y`
  (`GSTGraphV2SixAdicSynchronizedShadows.lean:68-71`) — because `4` is a unit mod `3^k`;
- a **one-way dyadic shift**: `dyadic_shadow_mul_four_pow_iff_truncated (k t x y) :
  DyadicShadowAt k (4^t*x) (4^t*y) ↔ DyadicShadowAt (k−2t) x y` (lines 171–174), saturated
  below (`dyadic_shadow_mul_four_pow_of_saturated`, lines 147–149);
- combined skew law: `six_iso_mul_four_pow_iff_truncated_skew_shadows (k t x y) :
  SixAdicIsoAt k (4^t*x) (4^t*y) ↔ DyadicShadowAt (k−2t) x y ∧ TriadicShadowAt k x y`
  (lines 188–191).

Consequence (the distinction proving itself): the digit-2 gate event
`digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2` is a statement about ternary digits only.
Its dyadic half is *vacuous* — `×4` can never destroy or create triadic resolution, and the
dyadic shadow it shifts is irrelevant to a ternary digit condition. Therefore any putative
bad channel-1 run is **purely triadic-shadow content** and must be killed by triadic laws
alone; the six-adic universe offers no dyadic escape hatch for a counterexample. The Lean
form of the distinction is `wavf_gate_chart_shift` (STEP 2): the gate event on the
powers equals verbatim the gate event on the affine-unit chart, transported by
`four_pow_digit_affine_shift` — the triadic isometry made concrete on the orbit.

## 2. STEP-BY-STEP DERIVATION

### STEP 0 — coordinate identification (all verified; zero risk)

```lean
theorem wavf_badChannel_one_iff_noCommonTwo (K : Nat) :
    BadChannel 1 (affineOrbit K) ↔ ¬ CommonTwo K :=
  (chat2_noCommonTwo_iff_bad_channel_one K).symm
```
Cites: `chat2_noCommonTwo_iff_bad_channel_one (K : Nat) : (¬ CommonTwo K) ↔ BadChannel 1 (affineOrbit K)`
(`GSTFourPowerDirectChat2Application.lean:33-35`), itself from
`noCommonTwo_iff_badChannel_one : (¬ CommonTwo K) ↔ BadChannel 1 (affineOrbit K)`
(`GSTFourPowerAffineClassifierBridge.lean:35-38`).
The provider is *definitionally* the direct theorem in automaton language: all content is
in closing the automaton.

### STEP 1 — base band `K ∈ {5, 6}` (norm_num; mirrors the green engine)

```lean
theorem wavf_no_bad_channel_five : ¬ BadChannel 1 (affineOrbit 5) := by
  intro hBad
  exact (chat2_noCommonTwo_iff_bad_channel_one 5).2 hBad commonTwo_five

theorem wavf_no_bad_channel_six : ¬ BadChannel 1 (affineOrbit 6) := by
  intro hBad
  exact (chat2_noCommonTwo_iff_bad_channel_one 6).2 hBad commonTwo_six
```
Cites: `commonTwo_five : CommonTwo 5` and `commonTwo_six : CommonTwo 6`
(`GSTFourPowerDirectExistenceNoAxiom.lean:57,62` — both proved by
`norm_num [GSTFourPowerDirectResidue.digit3]`).
(Ground truth: `affineOrbit 5 = 341 = 110122₃`, `4·341+1 = 1365 = 1212121₃` — common two at row 1.)

### STEP 2 — the affine orbit reacts to the x4 phase map (triadic isometry, concrete)

```lean
/-- The channel-1 target is the next power's unit chart, exactly. -/
theorem wavf_phase_target_chart (K : Nat) :
    4^(K+1) = 1 + 3 * (4 * affineOrbit K + 1) := by
  have h := four_pow_eq_one_plus_three_affineOrbit K
  rw [Nat.pow_succ, h]; ring

/-- THE DISTINCTION, WRITTEN: the gate event is transported verbatim onto the
affine-unit chart by the triadic isometry (digit shift by one row). -/
theorem wavf_gate_chart_shift (K q : Nat) :
    (digit3 (4^K) (q+1) = 2 ∧ digit3 (4^(K+1)) (q+1) = 2) ↔
      (digit3 (affineOrbit K) q = 2 ∧ digit3 (4 * affineOrbit K + 1) q = 2) := by
  rw [four_pow_digit_affine_shift K q, four_pow_digit_affine_shift (K+1) q,
    affineOrbit_succ]
```
Cites: `four_pow_eq_one_plus_three_affineOrbit (K : Nat) : 4^K = 1 + 3 * affineOrbit K`
(`GSTFourPowerAffineOrbit.lean:22-23`); `four_pow_digit_affine_shift (K q : Nat) :
digit3 (4^K) (q+1) = digit3 (affineOrbit K) q` (same file 32–33); `affineOrbit_succ`
(18–19). Interpretation: the phase step `×4` moves the whole gate event down one triadic
row *without distortion* — the exact finite shadow of `triadic_shadow_mul_four_pow_iff`.

### STEP 3 — the channel states ARE the ×4 carry machine; the gate is the {0,3} chord

```lean
/-- THE DIGIT-2 GATE: with source digit 2, the output digit is 2 exactly in
channel states {0, 3} — the unique right chord of the 36-state base-6 cell. -/
theorem wavf_digit2_gate_iff (c : Nat) (hc : c < 4) :
    channelOut c 2 = 2 ↔ (c = 0 ∨ c = 3) := by
  unfold channelOut
  interval_cases c <;> norm_num
-- (4*2 + c) % 3 = 2 ↔ c % 3 = 0; with c < 4: c ∈ {0, 3}. Matches the verified
-- digit-2 gate law (digit 2, carry ∈ {0,3}) of the six-adic universe.

theorem wavf_lowSuccess_iff (c x : Nat) :
    lowSuccess c x ↔ (lowDigit x = 2 ∧ (c = 0 ∨ c = 3)) := by
  unfold lowSuccess
  by_cases h : lowDigit x = 2
  · rw [h, wavf_digit2_gate c (by omega)]  -- c < 4 needed: obtain from channel context
  · simp [h]
```
Cites (interpretation level): `lowDigit_lt_three`, `channelOut`/`channelNext` defs
(`GSTFourPowerAffineChannelAutomaton.lean:18,21`), `directCarry4_lt_four`
(`GSTFourPowerDirectAdditionCarry.lean:25-26`) for the `c < 4` invariant, and the
production-lattice edge laws `horizontal_digit_exact` / `vertical_carry_exact`
(`GSTGraphV2ProductionLaws.lean:17-21, 26-30`) certifying that this digit/carry recursion
is the *exact* production-lattice walk — no re-phasing escapes it
(`origin_frame_phased_state_exact`, lines 45–50).

State table (from the four verified transitions, `badChannel_zero_iff` …
`badChannel_three_iff`, `GSTFourPowerAffineChannelAutomaton.lean:158-197`):

| state c | digit 0 → | digit 1 → | digit 2 → |
|---|---|---|---|
| 0 | 0 | 1 | **GATE (success)** |
| 1 | 0 | 1 | 3 |
| 2 | 0 | 2 | 3 |
| 3 | 1 | 2 | **GATE (success)** |

A bad channel-1 run must therefore avoid digit 2 *exactly when sitting in states {0,3}*,
and terminates badly once the source's nonzero digits are exhausted (`x = 0` has all-zero
digits, so `PairCommonTwo 0 _` is false).

### STEP 4 — lockstep: the automaton reads the exponent's own trits

```lean
theorem wavf_low_trit_is_exponent_trit (K : Nat) :
    lowDigit (affineOrbit K) = K % 3 :=
  lowDigit_affineOrbit K

theorem wavf_bad_run_first_branch (K : Nat) (hBad : BadChannel 1 (affineOrbit K)) :
    (K % 3 = 0 ∧ BadChannel 0 (tail3 (affineOrbit K))) ∨
    (K % 3 = 1 ∧ BadChannel 1 (tail3 (affineOrbit K))) ∨
    (K % 3 = 2 ∧ BadChannel 3 (tail3 (affineOrbit K))) :=
  (noCommonTwo_low_trit_branch K).1 ((chat2_noCommonTwo_iff_bad_channel_one K).2 hBad)

theorem wavf_peel_lockstep (q : Nat) :
    tail3 (affineOrbit (3*q)) = peel0 (affineOrbit q) ∧
    tail3 (affineOrbit (3*q+1)) = peel1 (affineOrbit q) ∧
    tail3 (affineOrbit (3*q+2)) = peel2 (affineOrbit q) :=
  ⟨tail3_affineOrbit_three_mul q,
   tail3_affineOrbit_three_mul_add_one q,
   tail3_affineOrbit_three_mul_add_two q⟩

theorem wavf_next_read_lockstep (q : Nat) :
    lowDigit (peel0 (affineOrbit q)) = q % 3 ∧
    lowDigit (peel1 (affineOrbit q)) = q % 3 ∧
    lowDigit (peel2 (affineOrbit q)) = (q+1) % 3 :=
  ⟨lowDigit_peel0_affineOrbit q, lowDigit_peel1_affineOrbit q,
   lowDigit_peel2_affineOrbit q⟩
```
Cites: `lowDigit_affineOrbit` (`GSTFourPowerAffineClassifierBridge.lean:42-44`);
`noCommonTwo_low_trit_branch` (same file 49–53);
`tail3_affineOrbit_three_mul` family (`GSTFourPowerAffinePeelClassifier.lean:17-35`);
`lowDigit_peel0/1/2_affineOrbit` (78, 84, 90).
Meaning: after consuming one exponent trit, the next automaton read is *the next exponent
trit itself* (twisted by +1 on branch 2). A bad run is an infinite walk of the **exponent's
trits** through the state table, i.e. the survivor tree of slice 2-c.

### STEP 5 — the third wave is self-similar (renormalization + multiscale)

```lean
theorem wavf_wave3_selfsimilar (q : Nat) :
    renormOrbit (q+1) = 64 * renormOrbit q + 7 :=
  renormOrbit_succ q

theorem wavf_multiscale_chart (m q : Nat) :
    4^(3^m * q) = 1 + 3^(m+1) * scaleOrbit m q :=
  scaleOrbit_exact m q
```
Cites: `renormOrbit_succ (q : Nat) : renormOrbit (q+1) = 64 * renormOrbit q + 7`
(`GSTFourPowerAffineRenormalizedOrbit.lean:36-37`); `scaleOrbit_exact (m : Nat) :
∀ q : Nat, 4^(3^m * q) = 1 + 3^(m+1) * scaleOrbit m q`
(`GSTFourPowerMultiscaleRenormalization.lean:20-21`).
Meaning: consuming one exponent trit multiplies the unit chart by `4^3 = 64` — the *same*
x4 phase isometry at the next triadic scale. The third wave recurses identically at every
scale `m`, so the gate analysis at scale 0 transports verbatim to all scales.

### STEP 6 — six-adic resolution-tree formulation (the orbit fills the tree)

```lean
/-- The orbit chart is an exact prefix isometry of the exponent: the bad run
decides nothing about resolution — it only selects child cells. -/
theorem wavf_orbit_prefix_isometry (p a b : Nat) :
    affineOrbit a % 3^p = affineOrbit b % 3^p ↔ a % 3^p = b % 3^p :=
  affineOrbit_residue_eq_iff_exponent_residue_eq p a b

theorem wavf_pow4_period (p a b : Nat) :
    4^a % 3^(p+1) = 4^b % 3^(p+1) ↔ a % 3^p = b % 3^p :=
  pow4_residue_eq_iff_exponent_residue_eq p a b
```
Cites: `affineOrbit_residue_eq_iff_exponent_residue_eq (p a b : Nat)` and
`pow4_residue_eq_iff_exponent_residue_eq (p a b : Nat)`
(`GSTFourPowerAffinePrefixIsometry.lean:99-104, 64-68`).
Meaning: at every triadic depth the orbit realizes every admissible residue class of the
exponent — combined with the base-6 tree laws (`sixChildCenter` Fin-6 children,
`six_child_centers_injective`, `six_child_center_in_parent`,
`GSTGraphV2SixAdicOntologicalGeometryLaws.lean:166-175`) a bad run is a descent choosing
one child cell per level in a tree whose every node has six distinct children; the gate
rows 2/3/4 remove exactly the measured branches (row-two: `chat2_no_bad_affine_channel_one_of_mod9_five_or_six`,
Chat2Application.lean:126-131; rows 3/4 + prefix: `chat2_bad_affine_channel_one_obstruction_bundle`,
lines 112-123).

### STEP 7 — TERMINAL GATE (the one open mathematical input; hypothesis form)

```lean
/-- Wave-3 terminal gate: above the base band the survivor tree is empty —
every exponent ≥ 8 realizes the digit-2 gate at some row. -/
def wavf_SurvivorTreeEmpty : Prop :=
  ∀ K : Nat, 8 ≤ K → ¬ BadChannel 1 (affineOrbit K)

/-- MAIN DERIVATION: provider = terminal gate + closed base band. -/
theorem wavf_provider_of_survivor_tree_empty
    (h : wavf_SurvivorTreeEmpty) :
    ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬ BadChannel 1 (affineOrbit K) := by
  intro K hK5 hK7 hBad
  rcases Nat.lt_or_ge K 8 with hK8 | hK8
  · interval_cases K
    · exact wavf_no_bad_channel_five hBad
    · exact wavf_no_bad_channel_six hBad
    · exact absurd rfl hK7
  · exact h K hK8 hBad

/-- The axiom's theorem, from the third wave. -/
theorem wavf_directExistence_of_survivor_tree_empty
    (h : wavf_SurvivorTreeEmpty) :
    GSTFourPowerDirectExistence.FourPowerDirectExistence :=
  (chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one).mpr
    (wavf_provider_of_survivor_tree_empty h)

/-- Axiom-site replacement: the creation certificate without the inline axiom. -/
theorem wavf_creation_certificate_thirdWave
    (h : wavf_SurvivorTreeEmpty) (K : Nat) (hK5 : 5 ≤ K) (hK7 : K ≠ 7) :
    GSTFourPowerOntologicalAdapter.CreationCertificate (4^K) :=
  (GSTFourPowerDirectCreationMaster.directExistence_to_creation_master
    (wavf_directExistence_of_survivor_tree_empty h)) K hK5 hK7
```
Cites: `chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one :
FourPowerDirectExistence ↔ ∀ K : Nat, 5 ≤ K → K ≠ 7 → ¬ BadChannel 1 (affineOrbit K)`
(`GSTFourPowerDirectChat2Application.lean:160-162`); `directExistence_to_creation_master
(hDirect : FourPowerDirectExistence) : FourPowerCreationMaster`
(`GSTFourPowerDirectCreationMaster.lean:50-52`). The base-band `interval_cases` uses only
`K ∈ {5,6,7}` (≪ 501). No `decide` over any band above 501 occurs anywhere.

## 3. WHY A BAD CHANNEL-1 STATE CONTRADICTS THE ESTABLISHED LAWS

Assembled from STEPS 0–6, a `BadChannel 1 (affineOrbit K)` with `K ≥ 5, K ≠ 7` would force,
simultaneously:

1. (STEP 3, state table) an infinite-or-terminating walk of the exponent's trits avoiding
   digit 2 in states {0,3} — the survivor tree;
2. (STEP 4, lockstep + `chat2_bad_affine_channel_one_obstruction_bundle`) the row-two,
   row-three, row-four and *parametric* exponent-prefix obstructions at every scale
   (`K % 9 ∉ {5,6}`, `K % 27 ∉ {14,18,19,25}`, `¬ RowFourClass (K % 81)`, and
   `exponentTrit K p ≠ 2 − digit3 (4^(exponentPrefix K p)) (p+1)` at all p);
3. (STEP 5, self-similarity) the same avoidance reproduced at every renormalization scale
   `Y → 64Y + 7` (`renormOrbit_succ`, `scaleOrbit_exact`);
4. (STEP 6, prefix isometry) an exponent that still realizes *every* triadic residue class
   through its orbit (`affineOrbit_residue_eq_iff_exponent_residue_eq`), i.e. a walk that
   must choose a surviving child of the six-child resolution node at every level;
5. (STEP 1 + ground truth) while *empirically* the full survivor walk closes to exactly
   `{0,1,2,3,4,7}` (slice 2-c, exact big-int computation) — so above 5 nothing but `7`
   survives, and `7` is excluded by hypothesis.

The tension between (4) (the orbit floods every resolution cell) and (2)+(3) (the survivor
constraints prune every measured branch) is exactly "the distinction immediately proved
itself": the gate is triadic-only content, the isometry is triadic-exact, so the bad run has
nowhere to hide except the one pruned branch `7 = 21₃`. Making that final pruning *theorem
backed* is the terminal gate `wavf_SurvivorTreeEmpty` — the single remaining input.

## 4. WHERE `K = 7` AND `K < 5` FALL OUT

- **`K < 5`:** outside the provider's quantifier (`5 ≤ K` hypothesis). Physically: the
  orbits below 5 have no gate with their successors (e.g. `4^4 = 256 = 100111₃` contains
  *no* digit 2 at all, so no common two can exist); `affineOrbit 5 = 110122₃` is the first
  orbit whose successor shares a digit 2 (row 1). The engine closes 5 and 6 by `norm_num`
  (`commonTwo_five`, `commonTwo_six`), mirrored by `wavf_no_bad_channel_five/six` (STEP 1).
- **`K = 7`:** the unique genuine bad channel-1 orbit in the range. The walk: exponent
  `7 = 21₃` (trits low→high `1,2`); orbit `affineOrbit 7 = 5461 = 21111012₃`? — precisely
  digits low→high `1,2,0,1,1,1,1,2`; channel-1 run `c₀ = 1`:
  `d=1 → c=1`, `d=2 → c=3`, `d=0 → c=1`, `d=1,1,1,1 → c=1`, `d=2 → c=3`, terminal
  (source exhausted). Digit 2 occurs only at rows where the state is `1` — never {0,3} —
  and `4^7 = 21110211₃` vs `4^8` share no digit-2 row. It falls out of the derivation in
  STEP 7's base band: `interval_cases` on `5 ≤ K < 8` yields the three cases and the
  `K = 7` case is discharged by the hypothesis `hK7 : K ≠ 7` (`absurd rfl hK7`). The
  terminal gate is then only stated for `K ≥ 8`, exactly matching the engine's split
  (`fourPowerDirectExistence_from_physical_happy_ge_three`, NoAxiom.lean:69-76).

## 5. RISK REGISTER (every gap)

- **RISK 1 — the terminal gate is genuinely open (Erdős-type).**
  `wavf_SurvivorTreeEmpty` is the whole remaining mathematical content: sibling slice 2-c
  proved the finite residue tower can *never* close it (survivor counts 7, 18, 44, 110,
  272, 676, 1676 grow ≈ 2.48^p; exception set exactly {0,1,2,3,4,7}; minimal witness row
  not O(log K)). The skeleton deliberately carries it as a `Prop` hypothesis; the provider
  does NOT compile unconditionally until someone proves it. Do not delete
  `gst_four_power_direct_existence_inline` before this closes.
- **RISK 2 — the survivor-tree contraction invariant is not yet formulated.** The third
  wave's natural finisher is a strictly decreasing measure on bad runs using
  `renormOrbit_succ` / `scaleOrbit_exact` (each trit consumption multiplies the chart by
  64, an exact x4^3 triadic isometry), showing every infinite bad walk is the `7 = 21₃`
  path. No such invariant exists in any read file; it is the one mathematical invention
  still owed, and unbounded `K` forbids any `decide` fallback.
- **RISK 3 — six-adic tree descent is not yet Lean-linked to `BadChannel`.** STEP 6 states
  the residue-level facts (`affineOrbit_residue_eq_iff_exponent_residue_eq`,
  `pow4_residue_eq_iff_exponent_residue_eq`) but there is no verified bridge from
  `BadChannel` to `SixAdicBall`/`sixChildCenter` descent; the Graph-V2 production laws
  (`horizontal_digit_exact` etc.) live in the monolith-side cell structures with different
  namespaces and are cited as interpretation, not as Lean-level steps.
- **RISK 4 — Int/Nat coercion shim.** The shadow laws are over `Int`; `affineOrbit`,
  `digit3`, `BadChannel` are over `Nat`. STEP 2/3 lemmas need a one-time cast
  (`(affineOrbit K : Int)`, `Int.ofNat_pow` etc.); routine, but must avoid `simp`
  unfolding `digit3` into `/ 3^p % 3` inside `Int` goals.
- **RISK 5 — base-case import placement.** `commonTwo_five/commonTwo_six` live in
  `GSTFourPowerDirectExistenceNoAxiom.lean`, which is absent from the curated
  `/home/z/agent-work/src/` subset; the new file must live in the live project
  `/home/z/erdosternary2/`, or re-prove the two base cases by the identical
  `norm_num [GSTFourPowerDirectResidue.digit3]` tactic (3 lines each, band ≤ 6 ≪ 501).
- **RISK 6 — the 36-state chord citation is monolith lore.** The "masses (5,5),
  5+6·5 = 35 = 6²−1, 55₆, right chord" identification comes from the monolith
  (`gst_scoped_two_digit_happy_gate_right_chordS`, mapped by slice 2-b), not from the
  curated affine files; the Lean skeleton re-proves the finite gate core as
  `wavf_digit2_gate_iff` (4 states × 3 digits, `interval_cases c < 4`) so no unverified
  name enters the proof.
- **RISK 7 — `wavf_lowSuccess_iff` needs the `c < 4` channel invariant carried in.** The
  state bound is available (`directCarry4_lt_four`, `channelNext` values ≤ 3 by
  computation) but must be threaded explicitly through any induction that unfolds
  `badChannel_iff`; omitted here because STEPS 4–7 route through the already-verified
  branch lemmas instead of raw unfolding.

## 6. Compliance

- Every named citation above was read verbatim in this slice (files listed in
  DISCOVERY.md); no signature is quoted from memory.
- Skeleton uses only: `chat2_noCommonTwo_iff_bad_channel_one`,
  `chat2_fourPowerDirectExistence_iff_no_bad_affine_channel_one`,
  `commonTwo_five`, `commonTwo_six`, `four_pow_eq_one_plus_three_affineOrbit`,
  `four_pow_digit_affine_shift`, `affineOrbit_succ`, `lowDigit_affineOrbit`,
  `noCommonTwo_low_trit_branch`, `tail3_affineOrbit_three_mul`(+`_add_one/_add_two`),
  `lowDigit_peel0/1/2_affineOrbit`, `renormOrbit_succ`, `scaleOrbit_exact`,
  `affineOrbit_residue_eq_iff_exponent_residue_eq`,
  `pow4_residue_eq_iff_exponent_residue_eq`,
  `directExistence_to_creation_master` — all verified green in the live project.
- No `sorry`/`admit`/`axiom`/`native_decide`; `interval_cases` only on bands {5,6,7} and
  `c < 4`; no `decide` on any `∀ k < N` with `N > 501`.
