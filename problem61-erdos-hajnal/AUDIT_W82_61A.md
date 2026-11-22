# AUDIT_W82_61A.md — the W82-61B adversarial audit of lane W82-61A

TASK ID: W82-61B, deliverable D1. Fresh-eyes adversarial audit of the
sibling lane's kernel `problem61-erdos-hajnal/DM61_Proof_A.lean` (branch
`w82-61a`). English only. CI is the only Lean verdict.

## AUDIT PROTOCOL (the five checks, per the W82-61B brief)

- **A1 — STATEMENT BYTE-MATCH.** Every theorem in DM61_Proof_A.lean that
  claims an official statement must carry a byte-identical statement
  signature to the spec block in `DM61_Official.lean` (the vendored
  google-deepmind/formal-conjectures @ 2207c54d text): the official
  predicate `IsErdosHajnalLowerBound` must be the DM61_Official.lean
  definition (or import/restate it byte-identically), the target
  statements must match the spec text verbatim, no renames, no
  re-parameterizations.
- **A2 — SORRY/AXIOM SCAN.** CI log grep (`error:|sorryAx|unknown
  identifier|unsolved goals|declaration uses .sorry.`) plus `#print
  axioms` on every headline theorem — the allowed axiom set is within
  `[propext, Classical.choice, Quot.sound]`.
- **A3 — HIDDEN HYPOTHESES / DEFINITION DRIFT.** The kernel must not
  strengthen the hypotheses (extra premises on G, restricted graph
  classes, decidability side-conditions beyond the official signature's
  instances, `n ≥ N` floors smuggled into the statement instead of the
  official `∀ᶠ n in atTop`) or weaken the conclusion (indepNum-only
  forms, min instead of max, different f).
- **A4 — FAMILY COVERAGE.** Every H named in the kernel's family
  theorem must be covered by a complete in-frame proof — no graph
  silently dropped from the claimed list, no member left `sorry`.
- **A5 — CI GROUNDING.** The kernel's CI job (the 61A lane's job in
  `.github/workflows/kills.yml`) must actually compile the file and grep
  the markers; the run must be green on the branch.

## STATUS AT AUDIT OPENING (timestamp: W82-61B lane start)

**The branch `w82-61a` does not exist on the remote at lane start**
(`git ls-remote origin` shows no `refs/heads/w82-61a`; `git fetch origin
w82-61a` fails: "couldn't find remote ref"). The sibling lane has not
pushed any work yet. The campaign tip `origin/campaign` (fbb34f9, the W82
foundation) contains `problem61-erdos-hajnal/DM61_Official.lean` (the
official spec, kernel-fc job) but **no `DM61_Proof_A.lean`**.

Consequently, at opening time the audit verdict on the 61A kernel is:

> **NOT YET AUDITABLE — the audited artifact does not exist.**

The audit protocol above is armed and will be executed against the lane's
artifact the moment it lands on the remote; this file will be updated with
the concrete findings (defects reproduced, documented, and fixed in the
W82-61B branch per the brief).

## WHAT THIS MEANS FOR THE W82-61B CLOSURE MAP (D2)

The brief directs D2 to build on 61A's lemmas (the F7+P4 floor). Since
61A's floor is not on the remote, **the W82-61B closure map is built
SELF-CONTAINED**: every lemma it uses is proved in
`problem61-erdos-hajnal/DM61_Closure.lean` itself (over the official
predicate, restated byte-identically from DM61_Official.lean, with the
gate string-checking the byte-match in both files). No dependency on an
unpushed branch can hold the lane hostage. If 61A lands before the
closure map ships, the audit above executes and any defect found is
reproduced, documented here, and fixed in the W82-61B branch.

## HONEST LEDGER (the W82-61B map's own scope — never dress partial as complete)

Claimed and closed in official form by W82-61B (each entry: complete Lean
proof, `∃ c > 0, IsErdosHajnalLowerBound H (fun n => (n:ℝ)^c)`):
see `DM61_Closure.lean` — the F7 family members, the Ramsey-route kills
(K5, E5), and the substitution-closure law as a conditional theorem in
the banked uniform blow-up frame (PROOF.md §4's Theorem 4A/4B package —
the campaign's honest in-frame law; the general-graph closure is the
Alon–Pach–Solymosi regularity theorem and is NOT claimed).

Open (named, not claimed): the official open core `erdos_61` (all H);
`erha89`/`bnss23` (the classical solved variants — research-solved, not
formalized here); the four 5-vertex primes P5/co-P5/bull/C5 at full EH
strength (the W81 lane banked the structural laws and the exponent caps
— the counting step remains); the 6-vertex world (26 primes); the
uniformization bridge (GENERAL-REDUCTION GR-2).

The engine never stops; it never lies.
