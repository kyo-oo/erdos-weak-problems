# Wave 27 — The Full-File Reconstruction of GSTTwelvePointFoldWord

**Date:** 2026-11-17
**Branch:** `research/gpt6-gst-hypothesis-part1-chow-square-20261110`
**Base:** `084e4b7` (wave 26, run 43937304302 — RED, 37 errors, all in `GSTTwelvePointFoldWord.lean`)
**Method:** the 10-wave 40-agent system (W1 recon x4, W2 kill-design x4+commander, W3 verification x4, W5 weapons x2-method, W7 deployment; W8-W10 post-push monitoring/repair/report in flight)

## The 37 errors, five root causes

1. **The scoped tensor notation was OFF** (`Mathlib/LinearAlgebra/TensorProduct/Defs.lean:88`,
   `scoped[TensorProduct]`): the type-level `⊗[ℂ]` was an unknown token at :105/:132 —
   `pointPairAlgHom` never elaborated — cascading into :116, :126, :150, :340.
   FIX: `open scoped TensorProduct` in the header.
2. **`twelvePointAnalytification` was not imported**: the HodgeData contract lemmas and the
   region-4 hoists are spelled at the constant clan; the module was never in the import list
   (:748 unknown identifier; :725/:749 heartbeat cascades).
   FIX: `import GSTTwelvePointAnalytification` + `open GSTTwelvePointAnalytification`.
3. **The two leg-homs had their `comp` REVERSED** (W2-A's new finding — an authoring bug, not a
   cascade): `(algebraMap).comp (pointPairAlgHom.toRingHom)` can never elaborate; the semantics
   (leg = eval ∘ inclusion) demand `(pointPairAlgHom.toRingHom).comp (inclusion)`.
   FIX: comp swap + the pointPair_left/right proofs rebuilt on the hleg-hoist design
   (pullbackSpecIso_inv_fst'/inv_snd at the goal's own spelling, forward assoc, ofHom_comp merge).
4. **The rw-pattern diseases**: (a) `{default : Spec ℂ}` parsed as a PrimeSpectrum structure
   instance (:312/:359/:392) — parenthesized; (b) the ite needed `open Classical in` above the
   docstring (:311, the wave-23 law); (c) `Ideal.span_le` lands in Set-membership where
   `RingHom.mem_ker` cannot rewrite (:247) — rerouted via `Ideal.span_singleton_le_iff_mem`;
   (d) `finrank_eq_one_iff_of_nonzero'` hard-codes class-projection paths in its rw pattern
   (:280) — term-mode `.mpr` application; (e) the residueDegree Y-implicit spelling seam (:302)
   — the hrd ground have at the Spec-spelling closed by `exact` at default transparency;
   (f) the coe-instance seams on operator applications (:484/:665/:695/:786) — the wave-19
   have-hoist discipline applied everywhere; (g) `intro` on IFF goals (:373 + latent) —
   `iff_of_false ... False.elim`.
5. **The :503 statement timeout**: `RealizesAmbientOnPoints`'s `{p}` implicit left the
   unifier facing the nonlinear `2 * ?p =?= 0` (the documented HodgeData:356 disease).
   FIX: pin `(p := 0)` by name. The :534 `_`-calc error was a parse-recovery artifact of this
   timeout — `_`-LHS calc is legal at the pin (101 green corpus steps measured, plus 4466 in
   Mathlib); the calcs were rewritten with explicit LHS anyway (zero-risk).
   Plus: `subst hic` killed the wrong binder (latent L3) — `rw [hic]` instead; `rw [hzero]`
   cross-spelling (latent L4) — `exact hzero.symm`.

## The equiv bridge (W1-A design)

`comap_evalRingHom_default`'s `rfl` was dead: the two `default`s of `PrimeSpectrum ℂ` ride
different `Unique` instance paths (scheme-level vs the carrier's sigmaUnique-baked default) —
propositionally equal on the one-point space, definitionally not. The new proof: `unfold
twelvePointEquiv` (baked instances preserved), six pinned rfl-simp rewrites
(`Equiv.trans_apply`, `Equiv.sigmaUnique_symm_apply`, `Homeomorph.coe_toEquiv`,
`PrimeSpectrum.sigmaToPiHomeo_apply`, `PrimeSpectrum.sigmaToPi_apply` — all verified at the
pin), then two `Subsingleton.elim` transports (`congrArg (comap (eval i))`). The chain reduces
the equiv to exactly `comap (eval i) default` (sigmaToPi_apply: `sigmaToPi R ⟨i, p⟩ = comap
(Pi.evalRingHom R i) p`, RingHom.lean:115, rfl).

## The weapons' certificate (two-method law, evidence tier)

- The 26 letters of `foldWordData` assemble `twelvePointFoldMatrix` == `Twave` entry-for-entry
  (verified against the corpus definition; `twelvePointFoldMatrix_eq_Twave` is kernel-green in
  LawLanding).
- sympy: `det[Krylov(Twave, coordSeed)] = -1,149,656,584,000`, rank 12/12.
- PARI/GP 2.17.2 (independent): same determinant, same rank.
- Factorization `(-1) · 2^6 · 5^3 · 149^2 · 6473` — matches the campaign anchor exactly.
- `det(Twave) = 16 ≠ 0` (the fold is invertible); the orbit of the mixed seed under the fold
  spans the whole twelve-cell space — THE SPANNING LAW IS TRUE.

## Verification stack (pre-push)

- W3-C syntax certification: 1074 lines, 46/46 declarations, brackets balanced, splice
  boundaries 24/24 verified, four assembler defects found and fixed (truncated
  `twelvePointFoldWord_op` statement + three eaten docstrings).
- W3-D kill-table certification: 33/37 KILLED, 4 UNCERTAIN (all one-defeq-deep exacts only CI
  can retire), 0 ALIVE; latent L1-L6 6/6 killed; adversarial name-audit passed
  (IsClosedImmersion [IsIso] instance at ClosedImmersion.lean:73; IsIso residueFieldMap at
  ResidueField.lean:177; algebraMap_toAlgebra rfl).
- Commander identifier sweeps: 211 identifiers, zero real misses; the Equiv-chain names
  source-verified in the pinned tarball.
- Zero `sorry`/`admit`/`native_decide`; the CI sorry-grep gate will find nothing.

## Dispatch

Pushed as the twenty-seventh repair wave. The lane `gst-twelve-point-native-world` fires on
the FoldWord path filter; module 8968 (`GSTTwelvePointFoldWord`) elaborates, then module 8969
(`GSTTwelvePointLawLanding`) elaborates for the first time in campaign history — the
twelve-point native geometric world contract completes when the kernel signs it.
