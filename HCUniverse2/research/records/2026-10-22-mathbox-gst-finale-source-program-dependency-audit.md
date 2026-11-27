# Mathbox proof audit — exact GST Hodge finale dependency and spectral-to-native bridge

**Audit date:** 2026-10-22. **Branch and pinned revision inspected:** `research/gpt6-native-point-primitive-span-20261017` at `1baa2b42f4b36a3d713f16d1e67e67d0af97bfb7`. **Type of review:** direct Mathbox proof-audit SELF-REVIEW of current theorem signatures and their proof bodies. No public web; source-of-truth GitHub connector. **Full repository scope:** targeted actual modules and final-landings, not a claim of reviewing all 701 Lean proofs.

## Exact target / demonstrated proof branch

Target: for arbitrary smooth projective complex V, arbitrary p and rational Hodge alpha, an actual original-X native codimension-p cycle with class alpha under a genuine canonical rational Betti cycle map. Current formal terminal statement: `GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic H`.

**Verified actual condition-to-conclusion theorem** in `GSTClassicalHodgeGSTExactFinale.lean` (blob `ee2f243371f53a7dc826d2c8edff1a9e777c52ff`, lines 51-92):

```lean
abbrev CanonicalSpineGSTProgramFamily
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H) :=
  ∀ p : Nat, ∀ j : ClassicalHodgeBasisIndex V H p,
    CanonicalSpineGSTProgram G M p j

theorem gst_everyHodgeClassIsRationalAlgebraic
    (G : GeometricCycleClassSpine V H)
    (M : NativeMassCycleClassBridge V H)
    (R : CanonicalSpineGSTProgramFamily G M) :
    EveryHodgeClassIsRationalAlgebraic H := ...
```

This is a mathematically correct proof of **R + G + M ⇒ Stage2G exact Hodge**; its stated theorem PARAMETERS remain logical premises (they are NOT implicit facts that Lean automatically constructs). The proof uses `gst_bigradedBettiHodge` after `all_basis_separators_empty` and the exact normal form equivalence. The separate `GSTClassicalHodgeLimitlessExactClayFinale.lean` (blob `3ad163d213e6b8072feb32486e1fc07630a90398`) instead requires `(R : FullProjectiveCosmicExternalization G)`, along with G and M. Its `FullProjectiveCosmicExternalization` definition (in `GSTClassicalHodgeFullLimitlessCrown.lean`, blob `c90ac9eec2bf752d8888edbd226cde10d45e60b8`) requires a true projective native kernel and `AtomCosmicExternalization` for **each ordered pair of Hodge-basis directions**.

**First necessary independent input R** in `GSTClassicalHodgeGSTSourceProgramCompiler.lean` (blob `d3f73044c3f8d0a1382da3b2474aa9b4c1411318`, lines 52-118):

```lean
structure GSTSourceTargetProgram (G ...) (S ...) (j ...) where
  program : GradedGeometricProgram V p p
  source_action :
    program.cohomologyEval G S.hodge.1 =
      (classicalHodgeBasis V H p).repr S.hodge S.sourceIndex •
       (classicalHodgeBasis V H p j).1
```

The program applies to an existing source cycle; Lean then defines
`targetCycle = sourceScalar⁻¹ • program.cycleEval G S.cycle`, proves `targetCycle_spec`, and produces the requested target class. This **is** an actual Chow-cycle construction from a genuinely certified program; the source_action existence for arbitrary target j is the crucial realization condition. Without proving a family of actual geometric programs R, invoking the finale is conditional on the very property capable of generating every target.

**Independent canonical-semantics issue:** `GSTClassicalHodgeGeometricCycleClassSpine.lean` (blob `306441f288c906c3e4703e83c383b9e28eb0278e`) builds a `zeroCycleClassSpine` satisfying its current spine laws with identically zero externally supplied cycle class. Its theorem `spine_laws_do_not_force_hodge` proves, GIVEN a nonzero rational Hodge class, that those spine laws alone do not force Stage2G Hodge surjectivity. This is an in-repo **formal countermodel to insufficiency of the interface**; it is NOT a counterexample to the classical Hodge conjecture on an actual geometrically realized canonical map. It makes the canonical cycle-class comparison an independent semantic check.

**Other finals cross-checked by exact signatures:** `GSTClassicalHodgeUniversalTwoSlotSaturation.bigradedBettiHodge_of_universalTwoSlot` requires actual `htransport : ∀p,UniversalTwoSlotInvariant (AlgebraicHodgeSubspace...)` and a nonzero seed when the Hodge fiber is nonzero. `GSTClassicalHodgeGeneralSpaceExactOperatorFinale.everyHodgeClassIsRationalAlgebraic_of_operatorCosmos` requires a `NativeHodgeSeed` and a `GeometryFirstTwoGenerator` for every basis target. `GSTClassicalHodgeGSTProjectiveWordExactFinale` requires words whose `operatorPair` actions **already hit each requested basis target** on a canonical source. `GSTClassicalHodgeGeneralSpaceDefectExtinction.saturation_iff_exactHodge` is an EXACT equivalence but does not produce native saturation from the bare GeneralSpace ontology.

## New spectral reduction has completed GitHub kernel CI

`GSTClassicalHodgeExactClayStatement.lean` on pinned HEAD blob `34e70d0039d457ef2541c4ebaaaa57d85c64ba95` contains `rationalSpectralKernel_eq_rationalHodge`, `exactHodge_iff_spectralKernel_in_nativeRange`, `exactHodge_iff_nativeRange_eq_spectralKernel`. The full complex Hodge-charge kernel `ker_C(G_p)=(H.hodgeBigrading p).ppComponent` is a **spectral geometry hypothesis**; it does not supply the native source-cycle range inclusion. Exact terminal range-equality theorem additionally has `CycleClassHodgeCompatible H` (true for a genuine canonical cycle map, not an arbitrary Stage2G datum). The dedicated `GST Hodge Spectral Kernel Reduction` GitHub Actions run [39672107848](https://github.com/kyo-oo/HC-PROOF/actions/runs/39672107848) at commit `1998800c8d69defc68ad15e5703af41d9207f031` is **COMPLETED SUCCESS**, including its explicit Lean kernel build. This validates only that module's actual formalized theorems as stated, not omitted premises or unrelated finals.

## Dependency matrix and outcome

1. Whole complex Hodge `ker_C G=H^(p,p)`: **proved** by exact eigenspace argument, without any source assumption.
2. Rational Hodge fiber `K_Q=H^(2p)(X,Q)∩ker_C G`: **proved** as canonical comap / Lean kernel bridge.
3. For genuine cycle classes `im cl ⊆ K_Q`: **true mathematical geometry**, represented as an explicit semantic structure field/compatibility proposition for general Stage2G maps.
4. `∀p,j, CanonicalSpineGSTProgram G M p j` OR `FullProjectiveCosmicExternalization G`: **named input**, not unconditionally established by the target finale proofs. This is an exact first source-existence obligation, not a new request to redo spectral algebra.
5. Conditional programs → genuine target cycle via `sourceScalar⁻¹ • program.cycleEval G S.cycle`: **proved under premise** by `targetCycle_spec`.
6. For ALL original X and p, `im cl =K_Q` and canonical Betti comparison: **not established by the audited chain absent item 4 and actual semantic grounding**.

**Primary Mathbox verdict:** **conditional on a named unverified input**. This does not imply HC is false, and it does not refute any independent verified actual-X source theorem elsewhere. It directly explains what Lean compiled and which theorem argument must be produced to make this particular chain unconditional.

**Next discriminating proof obligation for this exact chain:** Construct, from arbitrary original X and its canonical geometry and a source `globalSpineOrbitSeed G M p`, a `GSTSourceTargetProgram G ... j` for every rational Hodge-basis sheet j, with its **actual** `program.cohomologyEval` source_action equation and true `program.cycleEval` Chow action. It must not assume a Chow preimage for the requested j; in particular the projective-word normalizer/spectral operator cannot be called a geometric program without its true canonical cycle-class commuting square.

**Audit operations:** read actual branch AGENTS, active plan, current indexed records; exact source for 10 nearest finals and 19 broader finals; separately inspected underlying `GSTSourceTargetProgram`, `FullProjectiveCosmicExternalization`, `GeometricCycleClassSpine`, `NativeMassCycleClassBridge` definitions; checked run 39672107848 job success. No Lean edits, no local Lean, no new Wolfram computation, and no inference from compilation to mathematical surjectivity.
