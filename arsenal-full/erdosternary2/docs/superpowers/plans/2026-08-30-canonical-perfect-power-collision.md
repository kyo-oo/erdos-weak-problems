# Canonical Perfect-Power Collision Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox syntax for tracking.

**Goal:** Prove `canonical_perfect_power_block_collision` unconditionally by combining the existing green U2D/infinite-controller theorems with a lossless canonical renormalization state, then pass the unchanged V5 comparator.

**Architecture:** Preserve the complete lower ternary prefix and live horizontal/controller boundary instead of projecting to `(carry,digit)`. A child Happy cell creates a strictly positive crossing source. Complete right badness makes right local discharge nonpositive. Exact Equation III and the infinite controller ledger identify the remaining positive boundary with a canonical packet at the next origin digit. Iteration contradicts finite ternary support of `n`.

**Tech Stack:** Lean 4.33.0-rc2, Mathlib, Lake, GitHub Actions.

**Spec:** `LEAN_FINAL_COLLISION_HANDOFF.md` and the externally supplied `deep-research-report.md`.

## Global Constraints

- Work on `sol/gpt56-canonical-tail-escape-20260827`, never main/master.
- Do not install Lean locally.
- Do not alter the V5 comparator target list or success criteria.
- No `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide`.
- No import from a supporting module back into `ErdosTernary2.lean`.
- Every production theorem is preceded by a compile probe that fails for the expected missing declaration.
- Every green claim requires a fresh successful GitHub kernel workflow.
- Preserve restored surgery commit `f44ba0584d7b4e5f80a3522f8b40f340b8894e46` and its descendants.

---

## File structure

- Create `GSTGraphV2SeededPrefix.lean`: lossless vertical prefix state and exact strip laws.
- Create `GSTGraphV2CanonicalRenormalization.lean`: all-three-trit canonical-tail recurrence, canonical boundary adapters, and stable unit congruences.
- Create `GSTGraphV2CanonicalEscape.lean`: explicit escape packet, controller identification, renormalization step, and arbitrary-cutoff escape.
- Create `GSTGraphV2CanonicalEscapeProbe.lean`: test-first consumer of every new public interface and axiom audit.
- Create `.github/workflows/gpt56-canonical-escape-kernel.yml`: exact isolated kernel compile and forbidden-token audit.
- Modify `GSTGraphV2PerfectPowerBlockCollision.lean`: replace `trace_state; omega` with adapters plus the certified escape contradiction.
- Keep `GSTPrefixOneU2DCollisionProof.lean` unchanged unless a namespace-only adaptation is required.

### Task 1: Dedicated RED kernel probe

**Files:**
- Create: `GSTGraphV2CanonicalEscapeProbe.lean`
- Create: `.github/workflows/gpt56-canonical-escape-kernel.yml`

**Interfaces:**
- Consumes: the planned module names.
- Produces: one workflow whose only success condition is compilation and a clean axiom/token audit.

- [ ] Create the probe with imports:
  ```lean
  import GSTGraphV2SeededPrefix
  import GSTGraphV2CanonicalRenormalization
  import GSTGraphV2CanonicalEscape

  #check GSTGraphV2SeededPrefix.seedHappy_strip
  #check GSTGraphV2CanonicalRenormalization.canonicalTail_three_adic_strip
  #check GSTGraphV2CanonicalEscape.canonical_escape_beyond
  #check GSTGraphV2CanonicalEscape.canonical_seed_transport

  #print axioms GSTGraphV2CanonicalEscape.canonical_seed_transport
  ```
- [ ] Commit and run the dedicated workflow.
- [ ] Verify RED is specifically `unknown module GSTGraphV2SeededPrefix`, proving the test detects the missing implementation.

### Task 2: Lossless seeded-prefix ontology

**Files:**
- Create: `GSTGraphV2SeededPrefix.lean`
- Test: `GSTGraphV2CanonicalEscapeProbe.lean`

**Interfaces:**
- Consumes: `HappyCell` from `GSTGraphV2InfiniteControl`.
- Produces:
  ```lean
  seededResidue (D k x q : Nat) : Nat
  seededCarry (D k x q : Nat) : Nat
  seededDigit (x q : Nat) : Nat
  SeedHappy (D k x q : Nat) : Prop
  seededResidue_strip
  seededCarry_strip
  seededDigit_strip
  seedHappy_strip
  ```

- [ ] Define:
  ```lean
  def seededResidue (D k x q : Nat) : Nat :=
    D + 3^k * (x % 3^q)

  def seededCarry (D k x q : Nat) : Nat :=
    (4 * seededResidue D k x q) / 3^(k+q)

  def seededDigit (x q : Nat) : Nat :=
    (x / 3^q) % 3

  def SeedHappy (D k x q : Nat) : Prop :=
    HappyCell (seededCarry D k x q) (seededDigit x q)
  ```
- [ ] Prove `seededResidue_strip` by expanding `seededResidue`, rewriting `Nat.mod_mul`, `Nat.pow_succ`, and distributing `3^k`.
- [ ] Derive `seededCarry_strip` by rewriting `seededResidue_strip` and normalizing `k + (q+1) = (k+1)+q`.
- [ ] Prove `seededDigit_strip` using `Nat.pow_succ` and `Nat.div_div_eq_div_mul`.
- [ ] Prove `seedHappy_strip` by unfolding `SeedHappy` and rewriting the carry/digit strip theorems.
- [ ] Run the dedicated workflow. Expected next RED: missing `GSTGraphV2CanonicalRenormalization`.

### Task 3: Canonical ternary renormalization

**Files:**
- Create: `GSTGraphV2CanonicalRenormalization.lean`
- Test: `GSTGraphV2CanonicalEscapeProbe.lean`

**Interfaces:**
- Consumes: `canonicalTail`, `canonical_tail_decomposition`, `prefix_one_tail_shape`, and seeded-prefix definitions.
- Produces:
  ```lean
  phaseOffset (r a : Nat) : Nat
  canonicalTail_mod_three
  canonicalTail_three_adic_strip
  canonicalTail_zero_strip
  canonicalTail_one_strip
  canonical_left_seed_adapter
  canonical_right_seed_adapter
  ```

- [ ] Prove the closed quotient identity:
  ```lean
  theorem canonicalTail_eq_sub_div (r m : Nat) :
      canonicalTail r m =
        (4^(3^r * m) - 1) / 3^(r+1)
  ```
  by combining `canonical_tail_decomposition` with positive-denominator cancellation.
- [ ] Prove `canonicalTail_mod_three` for `a < 3` by cases `a=0,1,2`, using the existing LTE/unit-tail congruences where available and direct canonical decomposition for the three fixed exponents.
- [ ] Define `phaseOffset r a := canonicalTail r a / 3`.
- [ ] Prove:
  ```lean
  theorem canonicalTail_three_adic_strip
      (r a m : Nat) (ha : a < 3) :
      canonicalTail r (a + 3*m) =
        a + 3 *
          (phaseOffset r a +
            4^(a * 3^r) * canonicalTail (r+1) m)
  ```
  by expanding the exponent, applying `Nat.pow_add`, substituting the two canonical decompositions, and cancelling the positive factor `3^(r+1)`.
- [ ] Derive `canonicalTail_zero_strip` and identify `canonicalTail_one_strip` with existing `prefix_one_tail_shape`.
- [ ] Prove left/right seed adapters using `graph_prefix_slice_happy_iff`, `canonical_tail_decomposition`, and `prefix_one_tail_shape`.
- [ ] Run the dedicated workflow. Expected next RED: missing `GSTGraphV2CanonicalEscape`.

### Task 4: Explicit escape packet discovery and certification

**Files:**
- Create: `GSTGraphV2CanonicalEscape.lean`
- Test: `GSTGraphV2CanonicalEscapeProbe.lean`

**Interfaces:**
- Consumes:
  - `weightedCrossPrefix_positive_of_top_leading_happy`
  - `unified_equationIII_vertical_telescope`
  - `canonical_infinite_bad_control`
  - `canonical_infinite_ledger`
  - `weighted_cross_mixed_controller_exact`
  - `canonicalTail_three_adic_strip`
  - `seedHappy_strip`.
- Produces:
  ```lean
  EscapePacket
  canonical_escape_packet_positive
  canonical_controller_packet_exact
  canonical_controller_renorm_step
  canonical_escape_beyond
  canonical_bad_parent_forces_unbounded_origin_support
  nat_no_unbounded_ternary_support
  canonical_seed_transport
  ```

- [ ] Add a RED theorem statement for `canonical_controller_packet_exact` with every existing endpoint kept explicit; compile and capture its exact unsolved goal.
- [ ] Normalize the goal into the shared fields `parentSeed`, `parentOffset`, `childResidue`, full horizontal carry word, and lower prefix.
- [ ] Define `EscapePacket` as that normalized integer endpoint expression, not as an opaque proposition.
- [ ] Prove `canonical_escape_packet_positive` directly from the existing leading-Happy crossing theorem.
- [ ] Prove `canonical_controller_packet_exact` by rewriting the unified telescope, crossing rectangle, and infinite ledger, then use `ring` only after all endpoints are syntactically aligned.
- [ ] Prove `canonical_controller_renorm_step`: rewrite the surviving endpoint with `canonicalTail_three_adic_strip` and `seedHappy_strip`; use right-bad local nonpositivity to show the packet cannot disappear.
- [ ] Prove `canonical_escape_beyond` by induction on the requested cutoff, iterating the exact renormalization step rather than asserting same-row transport.
- [ ] Define `canonical_bad_parent_forces_unbounded_origin_support` as `intro K; exact canonical_escape_beyond ... K ...`.
- [ ] Prove `nat_no_unbounded_ternary_support` by evaluating the support claim at `K=n+1`, proving `n < 3^r`, and applying `Nat.div_eq_of_lt`.
- [ ] Prove `canonical_seed_transport` by composing unbounded support with `nat_no_unbounded_ternary_support`.
- [ ] Run the dedicated workflow until the module and axiom audit are green.

### Task 5: Close the production collision

**Files:**
- Modify: `GSTGraphV2PerfectPowerBlockCollision.lean`
- Test: exact module compile and probe workflow.

**Interfaces:**
- Consumes: `canonical_left_seed_adapter`, `canonical_right_seed_adapter`, `canonical_seed_transport`.
- Produces the unchanged public theorem signature `canonical_perfect_power_block_collision`.

- [ ] Import `GSTGraphV2CanonicalEscape`.
- [ ] Replace the disconnected diagnostic tail with:
  ```lean
  have hc := (canonical_left_seed_adapter s n q hs).mp hChild
  have hr : ∀ j, ¬ SeedHappy 1 1
      (prefixOffset s +
        4^(3^s) * canonicalTail (s+1) n) j := by
    intro j hj
    exact hRightBad j
      ((canonical_right_seed_adapter s n j hs).mpr hj)
  exact canonical_seed_transport s n q hs hn hc hr
  ```
- [ ] Compile the collision module and run `#print axioms`.
- [ ] Verify no existing public theorem signature changed.

### Task 6: Downstream and comparator verification

**Files:**
- Existing downstream modules and restored surgery script.

- [ ] Compile `GSTPrefixOneU2DCollisionProof.lean`.
- [ ] Apply `scripts/patch_live_hcreationcheck.py` exactly as CI does.
- [ ] Compile the transformed `ErdosTernary2.lean`.
- [ ] Run forbidden-token and axiom audits.
- [ ] Run the unchanged exact V5 comparator.
- [ ] Record final commit SHA and the successful comparator URL only after it completes with success.
