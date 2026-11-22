# AUDIT — W82-61B adversarial audit of sibling lane W82-61A (COMPLETE)

TARGET: problem61-erdos-hajnal/DM61_Proof_A.lean on branch w82-61a,
commit d2f606d (the commander-absorbed kernel). Audit executed by the
commander (the 61B finisher channel died; the audit is a 61B-lane
deliverable and is executed in-round, main-thread).

## A1 — STATEMENT BYTE-MATCH vs THE OFFICIAL SPEC

The kernel's §0 predicate definition (lines 55-60):

    def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
      (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
      ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
        (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

diff vs problem61-erdos-hajnal/DM61_Official.lean's verbatim block: EMPTY
(byte-identical — verified by direct string comparison this session). The
official block itself byte-matches google-deepmind/formal-conjectures
@ 2207c54d FormalConjectures/ErdosProblems/61.lean (verified at W82
foundation: the diff of deepmind-comparator/DM_61.lean vs the cloned repo
file is empty). VERDICT: PASS.

## A2 — SORRY / AXIOM SCAN

- `rg 'sorry|admit|native_decide' DM61_Proof_A.lean`: zero hits (the only
  "sorry" occurrences are inside the docstring's honesty notes — no tactic
  sorry anywhere).
- The kernel ends with #print axioms on the five headlines
  (erdos_61_family, isEH_compl, exists_isIndepSet_mul_ge,
  rpow_quarter_le_sqrt, arsenal_threshold); the CI greps wire
  `! grep sorryAx` + the axiom-print presence. The CI verdict (run
  44972616159, queued at audit time) is the binding check. VERDICT:
  PENDING-CI (no local lean — the campaign law).

## A3 — HIDDEN HYPOTHESES / DEFINITION DRIFT

- Every family theorem (eh_K2 … eh_K1) is stated with the official
  predicate on the CONCRETE official graphs (⊤/⊥ on Fin 2/Fin 3/Fin 1,
  Mathlib's pathGraph 3 and its complement) — no extra hypotheses, no
  custom graph representation, no weakened predicate.
- The board theorem erdos_61_family: ∃ c > 0, seven conjuncts — each
  conjunct the official statement for that H. The bound function is
  fun n => (n : ℝ) ^ c exactly as the official statement's shape.
- Mathlib dependency check: pathGraph is Mathlib's own
  (Mathlib.Combinatorics/SimpleGraph/Hasse.lean:108 — pathGraph n = hasse;
  its adj lemma at :111) — the official DM file's `pathGraph 5` reference
  resolves to the same Mathlib definition. VERDICT: PASS.

## A4 — FAMILY COVERAGE (every claimed H genuinely proven)

Seven claimed members, seven complete proofs in the kernel:
- eh_K2 (no_edge_of_no_induced_K2 → univ independent → α = n ≥ n^{1/4});
- eh_Kbar2 (complement transfer isEH_compl from eh_K2);
- eh_K3 (cliqueFree3_of_no_induced → neighborFinset-independent dichotomy
  + the greedy core exists_isIndepSet_mul_ge);
- eh_Kbar3 (transfer);
- eh_P3 (closedNbhd_clique_of_no_induced_P3 dichotomy + greedy core);
- eh_Pbar3 (transfer);
- eh_K1 (vacuous — the embedding always exists for n ≥ 1).
The transfer isEH_compl itself: the (X.comap g)ᶜ = Xᶜ.comap g identity via
injectivity + SimpleGraph.indepNum_compl + compl_compl — checked line by
line; the two conjunct directions are correctly split. VERDICT: PASS.

## A5 — SCOPE HONESTY

The kernel's HONEST SCOPE block names P4, erha89, bnss23, p5, c5 as NOT
claimed — matching the W82 state. No partial result is dressed as the
official open core. VERDICT: PASS.

## OVERALL VERDICT: PASS on A1/A3/A4/A5; A2 binds at CI (the kernel-61dm-a
run). No defects found requiring repair.
