# Wave 68 — THE GENERAL-M LAW KERNEL-GREEN: the capstone's first certification

Date: 2026-11-21. Author: the reconstruction session's wave-68 strike
(the architecture agent 68-A, the authoring agent 68-D, and three
commander repair rounds 68.1–68.3).

## The kill

`GSTFiniteLineGeneralMLaw.lean` (1,031 lines) — **CI-GREEN: run 44928010015
at `dc31a62`** (the fourth adjudication round). `Build completed
successfully (8982 jobs)`, zero errors, the sorry-gate silent.

**THE LAW** (§8, line 968):

```
theorem native_GST_single_fold_orbit_law_finiteLine (M : ℕ) [NeZero M]
    (V : SmoothProjectiveComplexScheme)
    (hWX : V.X = finiteLineScheme M)
    (hWmap : hWX ▸ V.structureMap = finiteLineStructureMap M)
    (A : AnalytificationData V)
    (hspace : A.space = TopCat.of (sphereUnionSpace M))
    (ω : ...) (Z₀ : ...) (hZ₀ : Z₀ ≠ 0) (Z₁ : ...) (hZ₁ : Z₁ ≠ 0)
    (R₁ : RealizedFiniteClosedCorrespondence V H 1)
    (hR₁ : ∀ j : Fin M, R₁.cohomologyOperator (spherePointClassWorld ... j) =
      spherePointClassWorld ... (cyclicPred M j))
    (R₀ : RealizedFiniteClosedCorrespondence V H 0)
    (hR₀ : ∀ j : Fin M, R₀.cohomologyOperator (sphereComponentClass ... j) =
      sphereComponentClass ... (cyclicPred M j)) :
    NativeGSTSingleFoldOrbitLaw V (finiteLineHodgeData M V A hspace ω Z₀ hZ₀ Z₁ hZ₁)
```

For every `M ≥ 1`: the finite-line world (the disjoint union of `M`
projective lines) with the M-cycle fold satisfies the FULL
`NativeGSTSingleFoldOrbitLaw` — every weight's Hodge fiber is
Krylov-cyclic under the single fold. Discharged through the CI-green
wave-60 engine `native_GST_single_fold_orbit_law_of_sphereUnion_gate`
(run 44642555839) with the wave-64 identity-Krylov certificates (the
orbit IS the honest point-class family; det = 1, rank M/M at every M).

## The module body (all kernel-certified now)

§0 the world gate + the F1+F2 receipts · §0.5 the wave-63 instance
bridges · §2 the honest point-class family (nonzero on every line,
linearly independent) · §3 the seeds + the two cycle-class functionals ·
§4 the assembled `finiteLineHodgeData` (stash@0 / span@1 / stash@p≥2)
with the seven discharge lemmas · §5 the letter rotation · §6/§7 the
weight-1/weight-0 certificates + cyclicities · §8 THE LAW · §9 the
dead-weights receipt (every p ≥ 2 subsingleton).

## The repair arc

* **68.1**: the lane's import fix (`GSTPositiveDimensionalLawLanding`
  as an explicit `lake build` root — the wave-60 lane's own pattern).
* **68.2**: the lib-roots extension (the wave-60 module was never a
  lakefile root; added to `GSTFiniteLineGeneralMLawLib`'s roots with
  `GSTCyclicOrbitSpan`; the lane dispatched manually — the lakefile-only
  commit was outside the paths filter).
* **68.3**: the three-site repair — `finiteLineWorldGate_cycles` deleted
  (the dependent-transport disease), the two `map_smul'` goals respelled
  to the wave-63 template's explicit show-form (the plain-smul RHS
  unifies with the `RingHom.id` form by defeq).

## The gate ledger (the disclosed inputs, each a frozen interface)

* F1 ✓ GREEN · F2 ✓ GREEN (this session) · F3 staged (the chart-ring
  battle in commander authoring) · the analytification receipt (gated) ·
  the letter realization (gated) · the world instantiation (gated, needs
  `finiteLineEmbedding_over_base` + F3).

When each gate lands, the final unconditional instantiation composes by
discharging one hypothesis of THIS certified body — the campaign's own
frozen plug-in doctrine.
