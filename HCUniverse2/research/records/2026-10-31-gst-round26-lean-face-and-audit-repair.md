# GST law stack — Round 26: the §36 self-audit repair + the Lean face (DRAFT-NOT-COMPILED per SKILL §13)

- **Date:** 2026-10-31 (session clock, continuation).
- **Kind:** Audit-repair + formalization-draft round (the operator's order: "trigger v6 skill nature b, this is not enough, and once write the latex, write lean, finish it").
- **Artifacts:** `research/derivations/GST_law_stack_full_derivations_round25_2026_10_31.tex` (REPAIRED, recompiled, 20 pages) + `GSTLawStackRound26.lean` (the Lean face, root level, **DRAFT-NOT-COMPILED**) + the Round-25 record correction stamp.

## The in-round §36 self-audit: the Round-25 §6 overclaim, caught and repaired

Before writing the Lean face, the audit loop was run against the Round-25 artifact. The catch: the §6 "equivalence" theorem offered, as its converse-direction proof, exactly the forward argument restated at a single input — an overclaim of the class the campaign's audits remove everywhere else. The converse is false as a claim about this campaign's specific mechanism (the conjecture could hold through a different route while the pair construction fails).

The repair, at every site:
- The .tex §6 theorem is now the one-directional **REDUCTION** (items (i)–(v) at every input ⟹ the conjecture on the open sector), with the catch recorded on the artifact's face in a dedicated remark.
- The corollary and the scope table line repaired ("Reduction (items ⟹ Clay sector)").
- The PDF recompiled: 20 pages, zero errors.
- The Lean face encodes the repaired form (`composition_all_inputs`, one direction; the docstring records the repair).
- The Round-25 record carries the correction stamp.

## The Lean face: `GSTLawStackRound26.lean`

**STATUS: DRAFT-NOT-COMPILED** — per SKILL §13 (the standing boss order: no Lean toolchain in this sandbox; unverified Lean is text, not proof; "it compiles" is never asserted). The file is written to the repo's own conventions (`import Mathlib`, the ForAllN hypothesis-record pattern, capstone with `#print axioms`, no `sorry`, no new `axiom`), with the toolchain steps for an equipped environment on its face (lean-toolchain v4.33.0-rc2, mathlib v4.33.0-rc2, lakefile registration, `lake build GSTLawStackRound26`).

Contents (the Lean shadow of the Round-25 derivation):
- **PART A — the deck laws (R1):** `norm_deg` (the norm degeneration `1+γ+γ²+γ³=0` in any ring), `invariants_vanish` (the fixed space is trivial on a torsion-free module), `two_smul_mem_range` (every class dies at scale 2, explicit witness `w = -(1+γ)v`), `end_sq` (the bridge).
- **PART B — the Weil plane (R5):** `gammaPlane` (the operator's rotation `γ(m,n)=(n,-m)`), `gammaPlane_sq`, the ray conventions `γ W_R = -W_I`, `γ W_I = W_R`, the explicit action `(γ-1)(a,b) = (b-a, -a-b)`, **`weil_parity`** (the door-parity law: `m•W_R` dies ⟺ `2 ∣ m` — the pins `m* = 2` are the least even scale), `diagonal_killed` (the diagonal boundary), `range_eq_parity` (the image of `γ-1` = the parity sublattice, index 2 — the obstruction group is ZMod 2), `door_parity` (the Even form).
- **PART C — the cyclotomic engine:** `cyclo_engine_of_factorization` (from the standard roots factorization `∏(X-ζk) = X^L - 1`, evaluation at `X = -1` gives `∏(1+ζk) = 1-(-1)^L` — the machine behind the operator's five Wolfram totals). The factorization is a labeled hypothesis per the repo convention for standard-strength classical content.
- **PART D — the symmetrizer:** `∑ γ^j u = m•u` on invariants (the `1/m` engine of the forward leg).
- **PART E — the conditional composition face (the repaired one-directional form):** `SectorInput` / `IsRationalAlgebraic`; `OpenItems` (THE REMAINING THEOREM — the five open items (i)–(v) as labeled per-input propositions); `CompositionOn` (the two halves: `pair_bit_of_items` — STEP 4, OPEN; `algebraic_of_pair` — STEP 1, COMMITTED, the two-center conduit); `composition_at`, `composition_all_inputs` (the conditional composition; the converse NOT claimed), `boundary_exact` (the exact-boundary companion).
- The capstone `capstone_law_stack` with `#print axioms`.

**The open content is exactly `pair_bit_of_items` and the five fields of `OpenItems` — the Lean face makes the campaign's boundary machine-visible: the closure is conditional on exactly those fields, and the file says so on its face.**

## The honest boundary (unchanged, on the face)

- Items (i)–(v) remain OPEN. The closing string is not emitted: the only content it could have at the present state is the false assertion that the five items are proven (two carry computed counterexamples against every mechanism proposed so far).
- The Lean face is a DRAFT per the standing order; its verification in an equipped environment is a labeled FOLLOW-UP (SKILL §29.4), never part of the main claim.

## Verification

- The .tex repaired and recompiled (tectonic, 20 pages, zero errors).
- The Lean draft: written, no `sorry`, no new `axiom`, expected-repair sites marked inline (the Prod-component simp normalizations of `gammaPlane`; the `Module.End` `-1` literal unfolding).
- Pushed to the branch `research/gpt6-native-point-primitive-span-20261017` (research-only + the root-level draft .lean, NOT registered in the lakefile roots, NOT covered by any workflow path filter — no CI fires, exactly the campaign's research-commit convention; the draft's kernel-check is a labeled follow-up for an equipped environment).
