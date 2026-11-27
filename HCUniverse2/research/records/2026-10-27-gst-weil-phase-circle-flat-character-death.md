# GST Round 16: The Weil Phase Circle (Lemma W9) — the Monodromy Mechanism's Question Answered at the Character Layer

**Date**: 2026-10-27
**Cycle**: 4 follow-up, round 16 (boss directive: execute the reopen menu — work the proof, no closure; SKILL V6 MODE B, ULTRA MODE)
**Derivation**: `research/derivations/GST_pair_channel_weil_phase_circle_2026_10_27.tex`
**Certificate script**: `research/experiments/task16a_pair_phase_circle_checks.py` (bounded: exact Fraction arithmetic; the committed 16-letter model conventions imported verbatim from the audited task13d/task15a certificates; no floats; every check asserts; < 1 s; ALL GREEN on first run)
**Registry movement**: the NO-route reopen item (Picard–sheaf monodromy / determinant-of-cohomology rigidity) moves from "OPENED with its certified entry wall" to "OPENED, additive core certified DEAD, non-abelian + phase residue armed"; the YES-side kill-list loses one family (the character-layer obstruction is eliminated). The row stays BLOCKED-characterized (DETERMINES NO BIT).

## What was struck

Round 15-b armed the monodromy mechanism and recorded its question: do Ψ_pair + the per-fiber monodromy representations constrain (m,q) beyond the additive profile? LIVE = a separating constraint; DEAD = both strata monodromy-consistent. This round answers the question at the determinant/character layer.

## The theorem

**Lemma W9 (the Weil phase circle).** For every holomorphic pure pair at every scale m:
1. **(Unification, leaf P5)** Ψ_pair = det(ρ₊)·det(ρ₋)⁻¹: the two W8.1 entry-test items (the flat position and the per-fiber monodromy reps) are ONE observable at the determinant level.
2. **(The ghost census, model-certified)** the dual-side virtual family Φ̂(ξ_pair) has the FULL five-grade Chern census (0, 0, m·Ŵ_R-dual, 0, 0): rank 0, c₁ 0, the middle grade exactly m·(the committed W5 unit ghost), c₃ 0, top 0 — extending W8.2 with the rank/top vanishing certified on ALL committed instances. The census is m-determined: the ambient (r, c₁, γ, c₂) data — in particular the Weil charge q — is invisible (the (m,q)-content of the determined grade-4 difference dies at the Euler-cancellation face, W4).
3. **(The type-split, leaf P6)** the character input of the phase is the family's (1,1)-content = c₁(L_pair) = 0 (W8); the residual phase factors through the discrete Chern lattice of the family class — a homomorphism of the ghost lattice: **χ_pair = m·χ_W, with ψ_W ONE fixed phase point of the double-dual**, independent of the pair, the rank, the ambient data, the charge, and the scale.
4. **(The circle)** every pure pair's flat line lies on the fixed rank-1 subtorus of Pic⁰(Â) — the **Weil phase circle**; the entry test sharpens from "exhibit a flat line" to "exhibit the flat line ON the circle".

**Corollary W9.1 (the additive death).** The character value is (m)-profile-computed; both strata are character-consistent (the m = 0 stratum — e.g. the Pic⁰-twist pairs, cohomologically trivial differences — carries the trivial character; every m ≥ 1 pair carries m·χ_W, no internal contradiction). The recorded mechanism question is answered **DEAD at the determinant/character layer**: no separating constraint exists there.

**Corollary W9.2 (the twist-scale stability at all grades).** ch(ξ_pair ⊗ e^{kθ}) = ch(ξ_pair) for every k ∈ ℤ at every grade 0–4 (each correction term carries a W_R∧θ^j factor, killed by W0). Extends the committed task14c grade-2/3 twist checks to grades 0, 1, 4. Certified: k ∈ {−3..5}, all instances, all grades.

**Corollary W9.3 (the sharpened LIVE residue).** Post-W9 the mechanism survives only through: (a) the non-abelian per-fiber reps beyond their determinants; (b) the phase-point structure of ψ_W (ψ_W = 0: the character observable is vacuous on the channel — the entry test simplifies; ψ_W ≠ 0: the circle is a nonzero rank-1 phase constraint, LIVE only via a future independent phase/torsion mechanism). ψ_W's value is a holomorphic datum NOT computed at the model layer. **YES-side symmetric note**: the character-layer death eliminates one obstruction family from the kill-list — future W-charged-surface constructions face a strictly simpler entry test.

## Verification

- Script task16a (ALL GREEN, first run, 0.11 s): CHECK 0 the committed constants + the dual-side W0 annihilation in the shifted representation (the relabeling convention — the fm pushforward maps AB-letters to low positions — documented in place; the inherited-convention gate, ledger 084); CHECK 1 the FULL five-grade ghost census on ALL committed instances (the four W6 table instances + the carrier + the detector probe c₂(E₋) = W_R, r=6, m=2) with the input-side purity ch-diff = m·W_R purely at grade 2; CHECK 2 the m-linearity of the full census (m ∈ {1,2,3,5}) + the q-invisibility face (the q=8 probe vs a synthetic q=0 instance at m=2: identical census); CHECK 3 the twist-scale stability at all grades 0–4, k ∈ {−3..5}, all instances; CHECK 4 the character-input layer certified NON-VACUOUS both ways (fm₃(θ³) ≠ 0, the 28→28 census, no silent skips, the uniform +1 composite — recorded, not fitted; the channel kill fm₃(ch₃-diff) = 0 everywhere); CHECK 5 the ghost's duality face (degree-4 purity of the unit ghost's words, the committed W5 round trip identity, the unit census shape of the round-trip class).
- Layering: the scheme-level steps (P5 the Appell–Humbert/determinant-holonomy unification; P6 the Pic⁰-invariance/discrete-quotient type-split of the phase; and the round-15-b leaves P1–P4 beneath them) are declared external leaves at standard strength and NOT certified. The model layer certified here is the same layer as the committed W5/W6/W8 certificates. No new Lean file this round; the Lean certificate of the census arithmetic is the declared next movement (the same decide-able style as the pair-channel walls certificate), to land with CI receipts in a following round.

## Discipline

- Scope box in the dossier: claimed = W9, W9.1, W9.2, W9.3; NOT claimed = any decision, any ψ_W value, any exhaustiveness beyond the determinant/character layer, any non-abelian rep content, any resolution. DETERMINES NO BIT.
- Labels W9/W9.1/W9.2/W9.3 extend the committed W-frame; no committed label reused; the W8 statement untouched.
- M3 discipline: no equivalence content claimed as new; W9 is a new necessary-condition sharpening + the additive death of one armed mechanism family, the same epistemic status as the cycle-2/4 walls.
- English-only (ledger 081); banned-word gate run at commit time (ledger 076); floats banned in certificate scripts (ledger 084) — none present.
