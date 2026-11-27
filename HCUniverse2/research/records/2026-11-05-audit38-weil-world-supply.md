# AUDIT-38 — Round 38 certificate scope — 2026-11-05

## Verdict

**PASS_WITH_REPAIRS_REQUIRED → REPAIRED → PASS** (one batched repair round; closing
re-check 182/0/exit 0, deterministic double-run byte-identical; loop CLOSED).

Part A executed by ONE fresh adversarial agent (the repo's PTS adversarial-auditor
role invoked alongside SKILL V6.2 per the operator's standing order; the certificate
is compact — 182 checks, ~13 s per run — so the full scope fit a single bounded
dispatch). The agent's independent recompute (its own code: 4th-compound matrices
via 4×4 minors, sympy trace/nullspace, its own xgcd + congruence solve, cycle-
decomposition parity) is the orchestrator-recompute role (Part B) discharged within
the same agent.

## Claim match

Every substantive claim — the census, the spectral law (2/36/32, trace-verified),
the repo calibration (the three factors; the CRT projector equal to the repo's P_W
coefficient for coefficient; the a_j; the key identity), the projector action (the
congruences, the fixation on W basis and random-class, the ambient/mixed kills),
the divisor-sector kill, the generators with INT W_R² = 8, the fourth-power
character, the dichotomy, the Eisenstein degeneracy — SURVIVED computation,
external sabotage, and the agent's own independent reconstruction. The findings
were label-precision and documentation minors, all repaired in one batched round.

## Findings (all minor or nano; none blocker/major)

- F1 — the fourth-power character message asserted "[α]^* = multiplication by α⁴ = −7+24i" while the computed action on the (ReΩ, ImΩ) basis is multiplication by conj(α⁴) = −7−24i (trace/det cannot distinguish; the authoring exploration's own "MATCH: False" was the truth) — REPAIRED: the check now tests the first column (−7, −24) explicitly and the message/the .tex state the conjugate identification (Re ↔ 1, Im ↔ −i; the Weil factor either way).
- F2 — the sector-total check `2 + 36 + 32 == 70` was a literal tautology — REPAIRED: the MEASURED dimensions len(Wb) + len(amb_ker) + len(mix_ker) == 70.
- F3 — the disjointness label overstates the predicate (basis-vector-level test; vacuous under the empty-basis sabotage) — REPAIRED: the full-strength 2×2 test (the restriction of (^4[α] − N(α)²) to W has nonzero determinant).
- F4 — the dichotomy canary tested only the triangular cases — REPAIRED: the discriminant tr² − 4det is not a rational square (the general no-rational-eigenvalue test).
- F5 — the .tex referenced the repo forcing-frame files without location — REPAIRED: "the repository-root files … on the research branch".
- F6 — the md5 was listed among the certificate's properties without saying what it hashes — REPAIRED: "md5 of the receipts runA.txt (= runB.txt)".
- F7 — stale runtime estimate in the header — REPAIRED (~15 s).

## Counterexample / computation attempts

- Fidelity: two fresh runs, exit 0, 182/0 both, byte-identical (audA ≡ audB ≡ runA ≡ runB).
- S1 (ambient constant 25→26): FIRED, exit 1 (the ambient-factor check).
- S2 (sign flip in the α-matrix block): FIRED, exit 1 (171 failures — the K-operator laws, the trace identity, W-dim, the kernels).
- S3 (the degenerate world claimed generic): FIRED (three explicit FAILs: W-dim 34≠2, mixed 34≠32, coprimality; then a loud crash in the CRT inversion — the wrong census cannot pass silently).
- Vacuity: 0 hits on all patterns; the three garbage tests all fire.
- Recompute: the spectral law at three worlds by the compound-matrix method (traces 1366/1894/784; dims 2/36/32); the projector by xgcd AND a 5×5 congruence solve (both reproduce the repo's P_W exactly); INT W_R² = 8 by cycle-parity; the degeneracy by direct K-arithmetic (α⁴ = conj(α³ᾱ) at (3, 1+√−3); −7+24i ≠ 15−20i at (1, 2+i)). Bonus: the agent's compound(Mᵀ) equals the certificate's E4 entry-for-entry (an adjoint-convention match, immaterial — all claims transpose-invariant).

## Closing re-check

weil_world_supply_round38_checks.py: **182 checks, 0 failures, exit 0**;
deterministic double-run byte-identical (runA ≡ runB, md5
bdfb4d74323292a562a376ef46dad47c post-repair; pre-repair
60c3a5d374cf6b75df426a6d547974ff); ~13 s; the derivation recompiled
(tectonic, 0 errors); the Lean face carries per-part ledger-108 labels (all
shape records). Q2 NOT claimed; the closing string NOT emitted; the polarity
split stands.
