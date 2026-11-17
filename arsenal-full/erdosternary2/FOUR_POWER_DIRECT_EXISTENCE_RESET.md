# Four-Power Proof Architecture Reset

## Status

This note records a proof-architecture error discovered while implementing the four-power Graph V2 theorem. It supersedes the assumption that `FourPowerHappyPropagation` must be proved before the universal four-power theorem.

The mathematical target remains unchanged:

```lean
∀ K : Nat, 5 ≤ K → K ≠ 7 →
  ∃ p : Nat, 1 ≤ p ∧
    HappyCell (carry4 (4^K) p) (digit3 (4^K) p)
```

No weakening of the production theorem is intended.

## The blunder

Write

```text
H(K) := ∃ p ≥ 1, HappyCell (carry4 (4^K) p) (digit3 (4^K) p).
```

The proposed Task 3.3 propagation theorem was

```text
P := ∀ K p,
  8 ≤ K → 1 ≤ p → Happy(K,p) → H(K+1).
```

Because the conclusion `H(K+1)` does not depend on the supplied row `p`, this is propositionally the same induction edge as

```text
∀ K, 8 ≤ K → H(K) → H(K+1).
```

Given the already-planned concrete base `H(8)`, this propagation edge proves the entire infinite tail `∀ K ≥ 8, H(K)` by induction.

Conversely, the direct infinite-tail theorem

```text
∀ K, 8 ≤ K → H(K)
```

immediately proves the propagation theorem: for `8 ≤ K`, apply the tail theorem to `K+1`; the supplied source row and source-Happy hypothesis are unnecessary.

Therefore Task 3.3 was not a small remaining transport lemma. With the base case available, it is equivalent in strength to the complete infinite part of the target theorem.

## Consequence

The old implementation strategy accidentally made an optional proof architecture into a mandatory gate:

```text
source Happy row p
  -> local Happy-or-latent split
  -> follow the vertical future of that particular p
  -> force a relocated q
  -> induction
```

The public theorem does not require that causal story. Its witness `q` may be anywhere on the target sheet, and the final theorem merely asks that each admissible four-power sheet contain some Happy row.

Following the latent future of a supplied row is therefore extra structure. It may be mathematically interesting, and the exact local cascade remains valid, but it must not block the production proof.

## Correct primary target

The new primary route attacks the global exceptional-set statement directly.

Arithmetic form:

```lean
∀ K : Nat, 5 ≤ K → K ≠ 7 →
  ∃ p : Nat, 1 ≤ p ∧
    digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2
```

Equivalent contrapositive/classification form:

```lean
∀ K : Nat, 5 ≤ K →
  (¬ ∃ p : Nat, 1 ≤ p ∧
      digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2) →
  K = 7
```

The existing exact theorem

```lean
four_power_happy_iff_consecutive_digit_two
```

converts this arithmetic common-digit statement to the physical `HappyCell` statement.

## Fresh proof obligations

The fresh route should use only exact arithmetic facts whose own proof dependencies are clean. In particular:

1. exact ternary-digit periodicity of `4^K` in the exponent (`pow4_digit_period`);
2. exact finite residue classifications, beginning with the already-proved row-two mod-9 classification;
3. finite-support / ordinary natural-number facts proved without the quarantined navigation/controller theorem chain;
4. a direct classification showing that a globally overlap-free exponent `K ≥ 5` must be the exceptional exponent `7`.

The crucial new mathematics is item 4. It must not be hidden behind a theorem whose conclusion simply restates the desired Happy existential.

## What is demoted, not deleted

The following remain valid helper mathematics but are no longer the required spine:

- `four_power_happy_lifts_or_latent`;
- first-zero / extinction classifications;
- least-Happy-row normalizations;
- source-row vertical future packets;
- `four_power_happy_propagates` itself.

If the direct tail theorem is proved first, `four_power_happy_propagates` should be recovered afterward as the trivial corollary that ignores its source witness and applies direct existence to `K+1`.

## Acceptance rule

Production completion still means the original theorem is kernel-green and axiom-clean, the monolith is repaired without the quarantined creation route, and the unchanged comparator passes.

A green relocation helper is not completion. A green direct universal theorem is the mathematical milestone that unlocks the rest.
