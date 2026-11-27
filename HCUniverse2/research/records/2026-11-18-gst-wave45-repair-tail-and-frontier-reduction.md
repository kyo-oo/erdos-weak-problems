# 2026-11-18 — Wave 45: the repair tail killed, the frontier reduction at adjudication

## The target (BOSS)

The general live rank >= 2 core on positive-dimensional worlds —
`NativeGSTSingleFoldOrbitLaw` on a positive-dimensional `SmoothProjectiveComplexScheme`
with a live Hodge fiber of rank >= 2.

## The state before this wave

Wave 44 (commits `20cc352` -> `4fb9fa7` -> `b519f9b`) built and pushed the live-core
kit `GSTPositiveDimensionalLiveCoreKit.lean` (526 lines, zero sorry, four engines) and
froze the finiteLine lane design (`campaign/wave44/API_CONTRACT.md`, six modules).
The kit's CI arc: run 44332341609 died at the lakefile gate (lib-name collision,
fixed at `4fb9fa7`); run 44334743119 = the true first Lean touch: 51 errors, all
diagnosed and killed in the second repair wave (`b519f9b`); run 44339723668 = the
repair's adjudication: 15 residual errors — the environment collapsed before the log
could be pulled. The dying session's verdict: "the next kill is exactly two moves:
the repair tail, then the gate."

## This wave (session 4, the rebuilt environment)

1. **Environment rebuilt from message one**: the zip bag re-downloaded from Google
   Drive (token verified live), HC-PROOF re-cloned at the branch tip `b519f9b`
   (remote match confirmed), Vampire/PARI/Z3/sympy/gmpy2 reinstalled, the battle
   map rebuilt (`/home/z/hc-map/00_FOUNDATION.md`), the pinned Mathlib checkout
   recovered at `/tmp/ml4` (HEAD = 51e6992efd06126df61a496bebf8f49482a4e129).

2. **The repair tail retrieved and killed.** The run-44339723668 artifact log
   (1.23 MB, full motives) was pulled and distilled into
   `campaign/wave44/REPAIR_TAIL.md` (the environment's own campaign folder). All 15
   diseases were mechanical, zero mathematical breakage. The wave-45 repair
   (commit `bfd2262`):

   | Error site | Disease | Fix |
   |---|---|---|
   | :124 | rewrite direction (`←` on a goal already in algebraMap form) | forward `Algebra.algebraMap_eq_smul_one` + `exact hq` |
   | :149 | missing `LinearMap.add_apply` in the additivity simp chain | chain completed |
   | :166 | `TensorProduct.lift_tmul` (no such constant) | `TensorProduct.lift.tmul` (Basic.lean:127) |
   | :191, :326 | `iSupIndep_iff_pairwiseDisjoint` is Frame-gated; Submodule lattices are not frames | `iSupIndep_def` (the general-lattice `Iff.rfl`, Order/SupIndep.lean) + `iSup₂_le` + `Disjoint.mono_right` per-slot arguments |
   | :228, :229, :251, :518 | the VQ-slot disease (section-implicit `VQ` fed into explicit `n`/`p` slots) | implicit-VQ call forms |
   | :252 | `Submodule.eq_bot_iff.mpr` (dot-projection on unapplied constant) | `(Submodule.eq_bot_iff _).mpr` |
   | :407 | `prodEquivOfIsCompl hW` (p q are explicit variables in Projection.lean) | named arguments `(p := ...) (q := W)` |
   | :476–:485 | `span_induction` case order mismatched the logged motives | reordered mem/zero/add/smul; smul scalar coerced `(q : ℂ)` |

   Every replacement lemma name was verified against the pinned Mathlib checkout
   before the edit. Zero theorem statements changed; zero mathematics changed.

3. **The war council's carrier verdict (three recon agents + commander verification).**
   The finiteLine lane's carrier was re-adjudicated against the pin:
   - `Limits.lean` HAS scheme sigma-coproducts (`Sigma.ι` open immersions, disjoint
     images, `sigmaSpec` iso for finite products) — the coproduct route reopens the
     M-cycle (`Sigma.desc`, `σ^M = id` nearly free).
   - `RationalSingularCohomology A n = (linearYonedaObj of the singular chains).homology n`
     (Stage2F) — degree-0 cohomology is `ker d⁰` with `B⁰ = ⊥` (the `up ℕ` shape),
     i.e. the path-component-constant functions: the H⁰ machine needs NO universal
     coefficient theorem. `singularHomology₀Iso` (HomologyZero.lean) and
     `isPathConnected_sphere` (Analysis/Normed/Module/Connected.lean:207,
     `1 < Module.rank ℝ E`) are both present at the pin.
   - The blocked ring route's quotient-`GradedAlgebra` instance does NOT exist at
     the pin; the product-ring route (`Fin M → MvPolynomial (Fin 2) ℂ`, componentwise
     grading) needs a hand-built pi-grading instance; `ComplexPoint V` is the type of
     sections of the structure map, so the analytification requires a bare equiv from
     the world's actual C-points — the P¹(C) classification is itself a Mathlib
     frontier. **The carrier campaign is a multi-wave construction; the lane's
     remaining cost is concentrated there.**

## The certified state after this wave

- The kit's CI adjudication at `bfd2262`: run 44372952162 (auto-triggered by the
  path filter on push). The verdict lands on the Actions tab; the campaign does not
  claim green ahead of the kernel.
- The four engines stand mathematically: `complexificationMapQ_injective` (the
  keystone), `stashBigrading` + `rationalHodgeSubspace_stash_eq_bot` (dead positive
  weights with no vanishing proof), `spanBigrading` + `rationalHodgeSubspace_span_eq`
  (the gated-live fiber is exactly the rational span of the supplied classes), and
  `native_GST_single_fold_orbit_law_of_stashed_positive_weights` (the frontier
  reduction corollary: weight-0 cyclicity + stashed positive weights => the full law).

## The next kill (frozen)

The gate: the finiteLine lane per `API_CONTRACT.md`, entering through the carrier
campaign (the product-ring Proj route or the coproduct route, both costed above),
then the H⁰ kernel machine (route certified by the council: `ker d⁰` =
component-constant functions, no UCT), then the HodgeData assembly (span/stash
instantiation of THIS kit), then the CycleWord + LawLanding (the finite-point
twin's attested architecture).

## THE VERDICT (post-script, same day)

**GREEN.** Run 44382896351 at `a6ceb54`: SUCCESS — "LEAN PASSED:
GSTPositiveDimensionalLiveCoreKit", the sorryAx gate silent, all steps green,
the 268-module closure built on v4.33.0-rc2.

The repair arc of the kit (the finite-point lane's convergence signature,
replayed): 51 errors -> 15 -> 9 -> 2 -> GREEN, four CI waves.

THE CERTIFIED ENGINES (the general live rank >= 2 core's algebraic half,
kernel-checked at a6ceb54):

- `exists_complex_retraction` / `complexificationMapQ_injective` — the keystone
- `stashComponents` / `stashBigrading` / `rationalHodgeSubspace_stash_eq_bot`
  — dead positive weights with NO vanishing proof
- `complexifiedFamily` / `spanSlot` / `spanComponents` / `spanBigrading` /
  `rationalHodgeSubspace_span_eq` — the gated-live fiber is EXACTLY the
  rational span of the supplied classes (the tensor-projection argument, with
  the C-linearity engine `hTsmul` and the span_induction membership route)
- `native_GST_single_fold_orbit_law_of_stashed_positive_weights` — THE
  FRONTIER REDUCTION: weight-0 cyclicity + stashed positive weights =>
  the full `NativeGSTSingleFoldOrbitLaw` on any world

The wave-45.2/.3 repairs (all zero-mathematics): the rw-auto-close cascade,
the le_of_eq direction, bot_le (le_bot absent at the pin), the latent
omega-on-VQ (abel), THE RING MISMATCH (spanSlot is a C-submodule, ker T only
Q-linear — replaced by the C-linearity engine), the tmul-case rewrite order
(the second map_tmul must fire on the RHS instance), and the sub_mem
elaboration-postponement (the implicit submodule pinned by named argument).

The lane's remaining cost is concentrated in the carrier campaign (the world
construction); the H^0 kernel machine route is certified by the council
(ker d^0 = component-constant functions, no UCT needed).
