# ROUND 38 — THE WEIL-WORLD SUPPLY STRIKE
## The non-split Weil fourfold face of R2′: the projector supply, the divisor kill, the reduction to the one-source leaf

**Date**: 2026-11-05 (session clock) — **Mode**: B, V6.2 ultra max.
**Operator pre-order (§40)**: the standing finish order with the continuation order — *"ofcourse finish everyhting, why stopped in one round only? and also trigger the v6 skill and prove that shit skill, and finsih the proof. go"* — the PTS adversarial-auditor role invoked alongside SKILL V6.2; no stopping after one round.

**Target**: R2′ face (b) — the non-split Weil fourfold world (NS(A)_Q = Qθ, the 2-dimensional Weil plane, Round 34's committed obstruction receipts), per the boundary statements of Rounds 36 (S17(iii)) and 37 (S20(iii)).

**Session continuity**: the same continuation session that closed Round 37 (audit → repair → push at 4d6b4217) struck this round immediately, per the no-stopping order.

---

## THE STRIKE (construction-first per §34; the repo's forcing frame as the calibration anchor)

**ENGINE 1 — the Weil letter model** (this round's new construction): H¹ as a K = Q(√−d)-module of rank 4 (the Q-letters e_j, f_j = √−d·e_j), the operator [α] as the 8×8 block matrix, the exterior spectral calculus on ∧⁴_Q H¹. **ENGINE 2 — the repo's forcing frame** (GSTUniversalCMArithmeticObstruction.lean + GSTWeilForcingFrameCertificate.lean, the repository root): the discriminating fourfold f = [2+i], the spectral factors, the projector P_W, the correspondence coefficients, INT W_R² = 8, the kernel-verified source dichotomy — every receipt reproduced from first principles and used as the calibration anchor. **ENGINE 3 — the CRT/invariant arithmetic**: the structural eigenvalue law (α^k ᾱ^{4−k} with multiplicities C(4,k)C(4,4−k)) + the exact 70×70 verification.

### The deliverables

- **S21 THE SPECTRAL LAW** (PROVEN): at every committed generic world the Q-spectral structure of [α]^* on ∧⁴_Q H¹ is minpoly(α⁴)¹ ⊕ minpoly(α³ᾱ)¹⁶ ⊕ (t−N(α)²)³⁶ (2+32+36 = 70, trace-verified against the actual exterior matrix); **the Weil plane W = the α⁴-primary part, dimension exactly 2**; the genericity law: the three factors are pairwise coprime iff (α/ᾱ)^k ≠ 1 for k ≤ 4 (the root-of-unity phase exclusion).
- **S22 THE PROJECTOR SUPPLY** (PROVEN): at every committed generic world the CRT projector — the UNIQUE degree-≤4 Q-polynomial P with P ≡ 1 mod the Weil factor, 0 mod the others — is an explicit Q-combination of the isogeny iterates' graphs: **an algebraic correspondence at every committed world**. At the discriminator (Q(i), 2+i) the canonical representative equals the repo's P_W(t) = −((t−25)(39t−79)(t²−30t+625))/44000000 COEFFICIENT FOR COEFFICIENT (a₀..a₄ = −79/2816, 359/22000, −527/400000, 139/2750000, −39/44000000; the key identity pwN + (t²+14t+625)(39t²−2770t+72375) = 44000000).
- **S23 THE DIVISOR-SECTOR KILL, THE FIXATION, THE MEASUREMENT** (PROVEN): [α]^*θ = N(α)θ; [α]^*θ² = N(α)²θ²; **P(θ²) = 0 at every world — every product of divisor classes is killed; the algebraic source must be beyond-divisor**; P = identity on W (basis + deterministic random-class); P annihilates the 36-dim ambient and 32-dim mixed sectors; the spectral disjointness (the 2×2 restriction test): **the beyond-divisor content is EXACTLY the 2-dimensional Weil plane**; the generators W = ⟨Re Ω, Im Ω⟩ (Ω = ∧⁴(e_j + i f_j): 16 monomials, 8 real components); **INT W_R² = 8** (the repo's Part B receipt); the fourth-power character ([α]^*|_W = multiplication by ᾱ⁴ = −7−24i on the {Re, Im} basis; char poly t²+14t+625); **the dichotomy** (minpoly(α⁴) irreducible; the discriminant non-square: any K-stable Q-subspace of W is 0 or all of W — the repo's kernel-verified source dichotomy reproduced in the letter model).
- **THE EISENSTEIN DEGENERACY** (PROVEN, a new named world): at (Q(√−3), 1+√−3) the phase α/ᾱ = e^{iπ/3} is a cube root of unity: α⁴ = conj(α³ᾱ) exactly, the Weil and mixed factors coincide (t²+16t+256), the primary part merges to dimension 34 = 2+32; the degeneracy occurs at NO generic world (the canary).
- **S24 THE REDUCTION TO ONE SOURCE + THE RE-DRAWN BOUNDARY** (PROVEN as the equivalence): under the external leaf W ⊂ Hdg⁴(A) (the Weil-type Hodge condition, inherited from the repo's forcing frame), **the RHC at a committed non-split Weil fourfold at degree 4 is EQUIVALENT to the single leaf: one algebraic class z with P(z) ≠ 0** (the correspondence supply + the dichotomy spread one nonzero source to the full plane; the kill forces the source beyond-divisor). The boundary after this round: (b) reduced at the committed census to the one-source leaf — exactly the repo's own committed open content ("P_W cl(Z) = 0 for EVERY actual algebraic surface Z, not just the divisor subalgebra" — the complementary direction); the transport families of (a′) and (b) beyond their censuses; R3 and R4 stand untouched.

## THE CERTIFICATE

`weil_world_supply_round38_checks.py` — **182 checks, 0 failures, exit 0, deterministic double-run byte-identical** (runA ≡ runB, md5 bdfb4d74323292a562a376ef46dad47c post-repair; pre-repair 60c3a5d374cf6b75df426a6d547974ff; xorshift64* seed 0x5CA1AB1E0D15EA5E — distinct from every prior certificate; exact Fraction arithmetic, zero floats; ~13 s). V1 the census (the K-operator laws); V2 the spectral law (trace-verified; the 2/36/32 kernels; the coprimality); V3 the repo calibration; V4 the projector supply at every world; V5 the divisor sector, the generators, the period identity, the character, the dichotomy; V6 the Eisenstein degeneracy; V7 the hostile battery (letter-deletion, projector-sign, fake-ambient, non-word, garbage liveness, the degeneracy claim — every control fires) + the vacuity and self-comparison scans. One authoring-time defect (a dead `or True` remnant) was caught by the certificate's own vacuity scan — the ledger-092/107 gate working on the session's own first draft.

## AUDIT-38 (§36 one loop)

ONE fresh adversarial agent (the compact certificate fit a single bounded dispatch; the agent's own-code recompute — compound matrices, xgcd, cycle-parity — discharged the orchestrator-recompute role within the same dispatch). **Verdict: no blockers, no majors** — every substantive claim survived computation, external sabotage (S1/S2/S3 all fired, exit 1), and the independent reconstruction. Seven minor/nano findings (F1 the conjugate-character identification — the authoring exploration's own MATCH: False was the truth; F2 a literal-tautology sector total; F3 the disjointness label; F4 the dichotomy canary; F5–F7 documentation), ALL repaired in one batched round strengthen-to-label. Closing re-check 182/0/exit 0 deterministic — **loop CLOSED**.

## PUSH

Research-only artifacts (the .tex + PDF tectonic-0-errors 93.99 KiB; the certificate; the exploration script; the round record; the AUDIT-38 file; the INDEX.md entry) + the unregistered draft Lean face GSTLawStackRound38.lean (no workflow path matches, no CI fires). No new ledger entry (no new scar class: the findings were ledger-109/112-family instances caught pre-push by the audit — the immune system working).

## QUANTIFIER LINE

The non-split Weil fourfold face of R2′ is reduced at the committed census to the one-source leaf: the projector supply is certified at every world (an algebraic correspondence), the divisor algebra is provably killed, the beyond-divisor content is exactly the 2-dimensional Weil plane, and one nonzero algebraic source spreads to the full plane by the dichotomy. **Q2 NOT claimed; the closing string NOT emitted; the polarity split stands.** The falsifiable line: the one-source leaf; the transport families; R3; R4.
