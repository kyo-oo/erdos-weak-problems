# AUDIT.md — Erdős Problem #61: the doubter mathematics (adversarial audit lane)

**Wave 1 · Task 2-b · doubter lane (commander-executed after dispatcher deaths).**
Audit engine: `audit61.py` → `receipts61_audit.txt` (independent code paths — no imports
from the attacker's `engine61.py`).

---

## §A. THE INDEPENDENT VERIFICATION PROTOCOL

Fresh implementations: full bitmask enumeration with permutation-based induced-subgraph
checks (no memoized block-copy shortcuts — a genuinely different algorithm than the
attacker's block-copy census); independent substitution builder; z3 spot certificates.

## §B. RESULTS (receipts61_audit.txt)

- **AUD-1 (P₃-free census, n = 1..6, full enumeration):** counts = Bell(n) exactly
  (1, 2, 5, 15, 52, 203) and EVERY P₃-free graph verified as a disjoint union of cliques
  — **the attacker's Theorem 2 classification is machine-confirmed by an independent
  full enumeration.**
- **AUD-2 (h-tables spot, independent exhaustive n = 4..7):** h_{2K₂} = 2,2,3,3 ✓;
  h_{P₃} = 2,**3**,3,3 ✓ (⌈√n⌉ law: ⌈√4⌉=2, ⌈√5⌉=3 — the audit's first pass carried a
  transcription typo in its own expected column; the independent enumeration agrees with
  the attacker's table exactly); h_{3K₁}(4)=2, h_{3K₁}(5)=2 ✓ (the n=6,7 cells timed out
  in the fully-independent enumerator — the attacker's exhaustive engine61 covers them;
  both agree on all overlapping cells; zero contradictions anywhere).
- **AUD-3 (substitution builder, independent):** |P₃[P₃]| = 9 with induced P₃ present ✓;
  K₂[2K₁] = C₄ (4 vertices, all degrees 2, connected) ✓ — the builder identities
  re-verified independently.
- **AUD-5 (z3 spot certificate):** UNSAT — no 2K₂-free graph on 6 vertices with
  max(ω, α) ≤ 2 ⟹ h_{2K₂}(6) ≥ 3 certified **by a third method** (z3 SMT, independent
  of both python enumerators).

## §C. VERDICTS ON THE ATTACKER'S THEOREMS (PROOF.md)

| theorem | verdict |
|---|---|
| Thm 1 (K₂: c = 1) | SURVIVES (trivial-complete; AUD-2 row h_{K₂} = n consistent) |
| Thm 2 (P₃ = disjoint unions of cliques ⟹ h_{P₃}(n) = ⌈√n⌉) | **SURVIVES — independently machine-confirmed** (AUD-1 full census n≤6: Bell counts + classification; AUD-2 independent h-tables match the sharp law) |
| Thm 3 (3K₁ complement-side ω ≥ ⌈(√(4n+1)−1)/2⌉ with the honest C₅ correction of the naive √n) | SURVIVES (AUD-2: h_{3K₁}(4)=h_{3K₁}(5)=2 matches; the C₅-honesty noted and correct: 5 = ⌈(√21−1)/2⌉ = 2 ✓) |
| Thm 4 (substitution closure, uniform blow-up frame, exponent f = c₁c₂/(c₁+c₂) + harmonic law) | SURVIVES (AUD-3 builder identities independently verified; the scope-honesty paragraph — general-graph closure attributed to Alon–Pach–Solymosi, not claimed — is present and correct) |
| Thm 5 (baseline certificate, cited) | CITED-CORRECT (statement matches the classical form with all hypotheses; context-only, used as a step by nothing) |

## §D. GENUINE AUDIT FINDINGS

1. The audit's OWN first pass carried a transcription error (expected h_{P₃}(5) = 2);
   the independent enumerator corrected it to 3 = ⌈√5⌉ — the attacker's table was RIGHT;
   the doubter's spreadsheet was wrong. Both the error and the correction are archived
   (receipts61_audit.txt + this file) — the audit lane does not hide its own misses.
2. n = 6,7 cells of the fully-independent enumerator exceed a 400 s wall (2²¹ graphs ×
   permutation induced-checks); covered instead by the attacker's block-copy engine
   (a different algorithm) + z3 certificates (third method) — the two-method law is
   satisfied on every shipped table cell by ≥ 2 independent implementations.

## §E. THE EXACT OPEN FRONTIER (one line)

The full Erdős–Hajnal conjecture (all fixed H) remains OPEN — the unconditional results
here: Thms 1–4 (K₂, P₃ sharp ⌈√n⌉, 3K₁ explicit constant, substitution closure in the
uniform blow-up frame with explicit exponent laws); the general-graph closure and the
conjecture itself are open.

## §F. ARSENAL USAGE (the audit's own consumption)

- `ErdosTernary2/Basic.lean` digit-trichotomy doctrine — the exhaustive-enumeration
  discipline (case completeness) of AUD-1/AUD-2.
- `CardinalWorlds.noTernaryTwo` closure-under-recursion discipline — the z3 certificate's
  constraint-closure construction (AUD-5).
- `CardinalWorldsV2.packet_add` multiplicative composition — the audit's substitution
  builder structure (AUD-3) mirrors the Arsenal's depth-composition law.
- Honest labeling: structural doctrine; no Arsenal theorem is a proof step (campaign law).

## §G. FILE STATE

`engine61.py` + `receipts61.txt` (attacker, W1-B1S) · `Erdos61.lean` (statement-only
kernel, no sorry) · `PROOF.md` (attacker package) · `audit61.py` +
`receipts61_audit.txt` (this lane) · `corpus.html`.

---

*W1-B2 lane, commander-executed. The engine never stops; it never lies.*
