# Audit — Round 29 (the boundary breach) — 2026-11-01 (session clock)

**Auditor**: this round's audit loop ran under an infrastructure constraint: the
two independent adversarial sub-agent dispatches (29-b1: the abelian layer;
29-b2: the nonabelian layer + receipts) both failed on agent-infrastructure
context deadlines (two "context deadline exceeded" failures, recorded in the
worklog). The recomputation was therefore performed by the orchestrator with
**deliberately different algorithms** at every load-bearing point (the §27
break-stance applied to one's own work), with the independent-agent re-run
recorded as an obligation for the next equipped session. The recompute code:
`audits/audit29_selfaudit_recompute.py` — 10 probes, exit 0, deterministic.

## Verdict: PASS_WITH_REPAIRS_REQUIRED (self-audit class) → PASS after the one batched repair round

The mathematics survives the different-route recomputation at every
load-bearing point. The findings were receipt-layer (the ledger-102 class) and
were repaired in one batched round; the closing re-check ran clean.

## The independent recomputations (different algorithms)

- **P1** — the F_2 ambient by **direct total-complex Gaussian elimination**
  (the assembled block matrices with the zero vertical differential explicit;
  NOT the certificate's row-sum): dims 1, 8, 30, 71 — **agrees**. The trivial
  deck control: 1, 9, 37, 93 — agrees. The split claim (d_vert = 0 ⇒ the total
  complex is the row-direct-sum) is confirmed within the same framework, and
  the framework itself is confirmed against the presentation-based
  abelianization below.
- **P2** — the H^1 cross-check through the **group presentation**: G = ⟨x_0..x_7,
  g | [x_i,x_j], g^4, g x_i g^{-1} = γ(x_i)⟩; the abelianization's Smith
  invariants: free 6, torsion [1, 2, 4] — Hom(G_ab, F_2) = F_2^8 — **agrees**
  with the engine's H^1 = 8 through a genuinely different route.
- **P3** — the rotation-lattice rank by the **character/trace identity**:
  tr(Φ²) = (tr γ²)² = 16 over End(Z^8) (tr γ² = −1−1+6 = 4), so the
  −1-eigen multiplicity = (64−16)/2 = 24 — **agrees** with the 64×64 kernel
  computation.
- **P4** — the dressed two-cell on the **complete basis sweep**: all 64 (h,k,l)
  deck triples × all 64 letter-basis (w,u)-pairs = 4096 cells per candidate, 3
  candidates, **0 failures**. With c_ν independent of (v,l) and linear in w,
  and the identity's difference bilinear in (w,u) per (h,k,l), the sweep
  **proves** the identity for all x,y,z ∈ G_bullet — closing the universal
  quantifier that the original battery only sampled (finding F1 below).
- **P5** — the additive bar identity of c_ν on 25 own-seed triples
  (coefficients in [−5,5]) — agrees.
- **P6** — the certificate re-run twice by the auditor: exit 0 both,
  byte-identical.

## Findings

- **F1 (major, receipt-fidelity / quantifier integrity)**: the .tex's dressed
  two-cell theorem asserted "for all x,y,z ∈ G_bullet" with the receipt being
  a finite random battery + 16 structured cells per candidate — a sample, not
  a proof of the universal quantifier. **Repair (executed)**: the complete
  basis sweep (4096 cells) folded into the certificate as the load-bearing
  gate 0144; the .tex's proof rewritten with the bilinearity argument and the
  sweep receipt; the count and the abstract updated. The sweep passes with 0
  failures.
- **F2 (minor, receipt-fidelity)**: the .tex said "150 checks" while the
  post-self-audit certificate prints 151 (now 154 after the repairs).
  **Repair (executed)**: the receipts paragraph updated to 154 with the
  current structure.
- **F3 (minor, strengthening)**: the ambient H^1 and the rotation-lattice rank
  lacked independent cross-routes inside the certificate itself.
  **Repair (executed)**: the presentation-based abelianization (gate 0012) and
  the trace cross-check (gate 0138) folded in as hostile controls.
- **F4 (minor, labeling)**: the §46-line-1/2 gates are documentation pointers
  (ok(True)) with the load-bearing gates named in their labels; the T2b
  receipt-pointer likewise. Assessed **honest** per the Round-28 repaired-T1c
  precedent (documentation is allowed when labeled; the pointers name the real
  gates and those gates exist and can fail).
- **F5 (note, process)**: the certificate's pre-repair version contained
  ledger-102-class weak gates (an `or True`, a `>= 2`, an `or`-disjunction, a
  dead else-branch, two unqualified §46-echo ok(True)s) — caught by the
  strike's own self-audit pass **before** the audit wave and repaired in
  place; the audit confirms the repaired forms gate the computed truth (==
  where determinable, the honest count gate, the no-go branch converted to a
  real failure gate).
- **F6 (note, scope)**: the .tex's "boundaries (b),(d) discharged" claims were
  checked against the mathematics: (d)'s discharge rests on the uniform-kill
  theorem whose proof (the five-term + the |C_4|-torsion law via
  cor∘res = 4 with res landing in H^n(1;M) = 0) is correctly stated; (b)'s
  discharge rests on the dichotomy theorem with both honest cases computed.
  Boundary (a) is labeled "transformed" — honest: the envelope is built and
  the ambient computed, but the residual class is not yet computed. The Clay
  statement is not claimed; the closing string is not emitted.

## The closing re-check

After the batched repair round: the certificate re-run twice, exit 0 both,
byte-identical, 154 checks; the basis sweep gate present and passing; the
.tex recompiled with 0 errors and the receipts matching the current output;
the audit recompute script re-run (10 probes, exit 0). **The loop is closed
at PASS.**

## The honest process record

The 29-b1/29-b2 independent-agent dispatches failed twice on infrastructure
deadlines. The audit work above is a self-audit by the round's author using
different algorithms — a weaker independence guarantee than the 28-b lineage.
The next equipped session should re-run the independent adversarial audit of
Round 29 (the recompute script and this document provide the probe list).
