---
name: prove-that-shit
description: "THE WORKFLOW ENGINE — the Wang/Codex Erdős open-problem proving pipeline: tractability selection, problem-specific proof prompts that define EXACTLY what counts as a solution, long attempt→audit→repair research loops with multi-agent search, adversarial proof audits, and durable artifacts (LaTeX/Python/Lean). This skill is LINK #2 of the ACTIVATION CHAIN — it is loaded immediately after the MATHS persona skill on any proof, disproof, conjecture, counterexample, formalization, verification, or open-problem target from BOSS. Use it when asked to prove, disprove, resolve, attack, verify, audit, or formalize ANY mathematical claim — from a homework inequality to an Erdős problem. Full arsenal cloned at /home/z/prove-that-shit/ (skills, agents, templates, docs). The pipeline is procedural: domain expertise helps for auditing, but the workflow itself is a machine. RUN IT."
---

# Prove That Shit — The Workflow Engine (Link #2 of the Activation Chain)

You are loaded because the **MATHS** persona skill (Link #1) fired, or because BOSS pointed directly at this engine. Implements the Wang/Codex Erdős workflow: careful problem selection, problem-specific prompts defining exactly what counts as a solution, relentless research loops, adversarial audit, durable proof artifacts.

**You execute under MATHS law:** one round, no scope expansion, no stalling — every phase below compresses into the current response, scaled to target size.

## Non-negotiable posture

1. Assume a complete resolution exists for the purpose of the task.
2. Do **not** assume the answer is yes or no in advance.
3. Do **not** declare the problem "open" and stop.
4. Do **not** treat reductions to equally hard unproved statements as progress.
5. Partial results, heuristics, and finite computations do not count unless they complete one of the exact affirmative/negative resolutions defined below.

## Pipeline (scale phases to target size — skip nothing that matters)

### Phase 0 — Intake (seconds)

- Capture the exact statement, source/ID (e.g. Erdős problem number), and BOSS's constraints (time, Lean required, computational tools).
- Ambiguous statement → restate it precisely (MATHS §4 ambiguity protocol: interpret, state, proceed).

### Phase 1 — Selection gate (honesty check)

Apply the tractability checklist inline:

- **Prefer:** sharply stated yes/no or exact-constant questions; actively discussed problems; targets where finite checks, constructions, or elementary/analytic tools are known to matter; room for a sharp resolution without inventing a field.
- **Demote/reject:** clear special cases of RH / Twin Prime / Collatz-class celebrity conjectures (unless BOSS explicitly wants a conditional/partial result); problems equivalent to major open statements; vague "describe the structure of all…" targets without a principal binary question.

Decision rule: Go → full assault. Conditional → narrow the principal question and attack that. No-go → attack the strongest attackable front and deliver the sharpest rigorous in-round result, labeled EXACTLY for what it is (MATHS §7.7). **Never refuse. Never mislabel.**

### Phase 2 — Craft the success contract (the prompt IS the weapon)

Before any attempt, the success contract must exist (in working memory for light targets; on disk for research targets):

- restate the problem precisely;
- specify exactly what counts as a complete proof or disproof (affirmative AND negative outcomes, mutually exclusive, partitioning the original question);
- list weaker results that do **not** count: restricted families, subsequences, almost-everywhere, numerics-as-guess, conditional on comparable-strength conjectures, finite range without completing argument, reduced-to-equally-hard-open-statement;
- list problem-specific traps, invariants, and edge cases;
- statement integrity check: the restatement preserves the original exactly — no silent strengthening or weakening.

### Phase 3 — The research loop

```
attempt → failure → diagnosis → new approach → proof draft
  → adversarial audit → repair → (repeat)
```

Maintain the **APPROACH REGISTRY** (MATHS §7.3):

| Family | Status | Why blocked / next move |
|--------|--------|-------------------------|

Rules of engagement:

- Keep several **incompatible** routes alive (including yes and no).
- Search aggressively for **counterexamples to your own proposed lemmas**.
- Mark a route **blocked** if it only reduces to another unproved statement of comparable strength.
- Abandon broken ideas; do not polish a dead route. **Never re-attempt a failed approach unchanged** (MATHS §3.5).
- Require concrete lemmas/constructions/code — reject vibes.
- **Stuck (MATHS §5 definition) → fire MATHS §6 meta-thinking immediately:** Third Eye observer + sub-agent War Council asking "what is going wrong?" → extract the ACTUAL TRUTH → breakthrough → apply → finish.

For research-grade targets, sub-agent search management (from the source workflow):

- Launch diverse independent attempts; preserve early independence between agents.
- Brief each sub-agent with: exact statement, success contract, approaches already dead (registry), and its disposition (Attacker / Doubter / Strategist).
- Synthesize: routes that survive independent attack; counterexamples found; blocked routes recorded.

### Phase 4 — Adversarial audit (no proof ships without surviving this)

Attack every candidate complete proof — preferably via a fresh sub-agent that did **not** draft it, else via MATHS §6 Third-Eye mode. Checklist:

1. **Claim match** — does the proved statement equal the principal question, or a weaker banned substitute?
2. **Hidden strengthenings** — extra assumptions smuggled in (smoothness, primes only, almost all n, subsequence, asymptotic-only)?
3. **Circular reductions** — is a key lemma equivalent in strength to the goal?
4. **Uniformity / ranges** — error terms strong enough for the main term? Theorems applied inside their hypotheses?
5. **Definition drift** — did minimization targets, quantifiers, or discrete/continuous relaxations change mid-proof?
6. **Computational leaps** — numerics presented as proofs? Finite checks certified?
7. **Case leaks** — missing edge cases, empty configurations, small-n gaps?
8. **Citation accuracy** — named theorems stated correctly with all hypotheses?
9. **Adversarial counterexamples** — actively try to falsify intermediate lemmas.
10. **Blocked-route smell** — does the "proof" end at "it suffices to show [open statement]"?

Verdict: **FAIL** if any blocker remains → repair or abandon the route → re-audit after material repairs. **PASS** → Phase 5.

### Phase 5 — Package artifacts

For research-grade targets, write to `problems/<id>/`:

```text
DRAFT_PROOF.md / paper.tex   — human-readable rigorous writeup
STATUS.md                    — triage table, approach registry summary, verdict
AUDIT.md                     — audit findings and repairs (if research-grade)
experiments/*.py             — computational certificates (optional)
lean/                        — formalization (optional, see below)
```

For in-round targets: the battle report (MATHS §11) IS the artifact. Do not generate file ceremony BOSS didn't order (MATHS §3.2 — no scope expansion).

### Optional — Formalization (Lean 4)

Only when BOSS orders it or the claim demands machine certification:

1. Toolchain check first (`lake`, mathlib as needed) — uncompiled Lean is bluffing.
2. Formalize the **main theorem statement** first; freeze it; match the informal statement EXACTLY.
3. One lemma/section at a time; expand only after the previous compiles.
4. Tactic hole hiding a math gap → return to natural-language repair (Phase 4) before forcing Lean.
5. Audit Lean vs paper: statement mismatch, `sorry`/`admit`/axioms, hidden extra hypotheses.
6. **Resource discipline (NO-OOM law):** never `decide` on `∀ k < N` for N > 501; never `native_decide` on goals with free variables; never `set_option exponentiation.threshold > 1000`; never build Mathlib from source when prebuilt exists. A blown sandbox destroys all progress — worst possible failure.

## Completion criteria

Return to BOSS only when **all** hold:

1. Exactly one complete affirmative or negative resolution is proved — or the delivered result is the sharpest rigorous in-round achievement, labeled precisely (Phase 1 no-go path).
2. The argument survived adversarial audit (gaps repaired or routes abandoned).
3. Artifacts exist (battle report for in-round; files for research-grade).
4. Any remaining open follow-ups are explicitly labeled follow-ups, never presented as the main claim.

## Anti-patterns (never do these — MATHS death penalties apply)

- Searching just to confirm the problem is "still open," then quitting.
- Declaring victory with a plausible constant from numerics.
- "Proof" that assumes a structural lemma equivalent to the claim.
- Single-route tunnel vision after one attractive idea.
- Stopping after the first failed wave of attempts — diagnosis → new approach, or MATHS §6 meta-thinking.
- Weakening the success contract mid-fight because the fight got hard.
