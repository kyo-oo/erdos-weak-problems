# GST fully connected proof-dependency graph: wave, n-cohomology, cosmology, CM, native curvature and Hodge

Date 2026-11-09 · Active branch `research/gpt6-native-point-primitive-span-20261017` · This is a dependency/status graph, **not** a theorem claiming that every arrow is already established.

```mermaid
flowchart TB
    A["Dimensionless seven-axis x4/base3 graph"]
    B["Exact information recovery F^5 = id"]
    W["Omega / N-wave, 2D/4D emergence, finite wave windows"]
    G["Self-expanding world cosmology, event and causal graph"]
    NC["N-shape / n-cohomology abstract channels"]
    L["World Lefschetz and duality operations"]
    C["CM/NM rational complex structure J and native geometry"]
    T["Infinite fold jet tower and curvature memory"]
    P["Geometric original-X cycle operator pairs"]
    I["Mixed wave/CM/curvature word naturality (Lean green)"]
    X["Canonical original-X Hodge and primitive sectors"]
    FIV["(P1)^5 genuine Chow source and 10D wave+CM cyclic orbit"]
    BIRTH["Independent primitive algebraic source-birth correspondence"]
    HYP["Universal GST single-fold orbit hypothesis"]
    HC["All rational Hodge classes receive original-X Chow cycles"]
    NV["Exact N-wave CM readout + actual Wave-I source"]
    FW["Genuine original-X N-wave dual Chow frame"]
    PR["Actual Hard Lefschetz primitive residual"]
    CR["Native wave+curvature residual elimination: Lean green"]
    SIX["(P1)^6 genuine curvature source ladder: rank 2 to 9"]
    CYCL["One native cyclic fold from augmented wave/curvature frame"]
    RANK["Rank n+1 source certificate and original-X Hodge construction"]
    EX["Exceptional Weil-fourfold primitive source, geometry needed"]
    A --> B
    A --> W
    W --> G
    B --> G
    G --> NC
    NC --> L
    C --> P
    T --> I
    P --> I
    I --> FIV
    B --> FIV
    C --> FIV
    L -. "missing canonical Hodge comparison" .-> X
    G -. "missing original-X geometry functor" .-> P
    C -. "need non-CM blocks / genuine kernels" .-> BIRTH
    X --> BIRTH
    I --> BIRTH
    FIV -->|"verified model, not universal"| BIRTH
    NC --> NV
    W --> NV
    C --> NV
    NV --> FW
    P --> FW
    X --> PR
    L --> PR
    FW --> PR
    PR --> CR
    I --> CR
    T --> CR
    CR --> SIX
    CR --> CYCL
    CYCL --> RANK
    SIX --> RANK
    CR -. "additional geometric source-birth direction" .-> EX
    SIX -->|"exact full-rank example"| BIRTH
    EX -. "construct non-divisor primitive source"| BIRTH
    BIRTH -. "geometric birth for arbitrary X" .-> HYP
    HYP --> HC
```

## Contract at every edge

| From | To | Actual mathematical status |
|---|---|---|
| Seven-axis arithmetic | Exact F^5 local information | **Lean-proved**, the 12 physical carry/trit states and full stream recovery |
| Seven-axis arithmetic | Ω/N wave | **Lean-developed** on canonical perfect-power arithmetic sheets; not a statement about cohomology of every projective X |
| Waves and events | Unbounded cosmology | **Lean-developed** as types, causal paths and world-birth rules; algebraic geometry is optional supplied realization |
| World-cohomology channels | Canonical H^{2p}(X) | **Missing comparison**, needs actual rational Betti/cohomological grading, Hodge filtration and polarization |
| World Lefschetz | Cup by ample divisor | **Missing comparison**, the world-digit/carry nilpotent operator does not itself establish hard Lefschetz on X |
| CM/NM programs | Native actual original-X cycles | **Proved for supported realized programs**; universal existence of suitable CM data on every X is not supplied |
| Infinite JetTowerInf | Fold-curvature identities | **Lean-proved** as formal all-order convolution; no automatic analytically convergent infinite geometry |
| Actual original-X wave and CM operators | Single combined fold and mixed curvature word | **Lean kernel green** as soon as both are genuine cycle-operator pairs |
| Combined fold T=S+J | Q^8 cyclotomic plus CM model | **Exact Wolfram and elementary field proof** of cyclicity; determinant 541 |
| Combined fold T=S+J | X=(P1)^5, codim2, actual Chow correspondence | **Complete hand-geometric construction**, exact Wolfram cyclic determinant 10,292,525 |
| Every codimension of X=(P1)^5 | One actual Chow correspondence seed orbit per weight | **Constructively shown** via complementary monomial cycles; dimensions 1,5,10,10,5,1 |
| Actual original-X native words | The existing algebraic image | **Lean kernel proved**: cannot produce a missing quotient direction by replaying only those words |
| Genuine N-wave dual Chow frame | Primitive Hodge residual | **Lean kernel established in prior modules**; original-X frame map with actual native cycles |
| Native geometric curvature cycle | Wave residual detector | **New Lean kernel green [42679545127](https://github.com/kyo-oo/HC-PROOF/actions/runs/42679545127)**: every old N-hole detector and one independent curvature probe vanish on the residual |
| Original-X primitive codimension-two wave+curvature | Primitive residual | **Lean green** [42683458742](https://github.com/kyo-oo/HC-PROOF/actions/runs/42683458742) including a rank n+1 original-X primitive reconstruction |
| (P¹)^6 original-X primitive sector | Seven successive curvature corrections | **Exact rational Wolfram**: ranks 2→3→4→5→6→7→8→9, all detector equations true, final residual zero |
| Weil-type discriminant-one fourfolds | Non-divisor exceptional primitive classes | Floccari–Fu arXiv:2504.13607v2 uses OG6/Kuga–Satake geometry; GST realization of exceptional source is the next test |
| Geometry-specific primitive source-birth | Arbitrary-X GST cyclic hypothesis | **The genuine target of the proof attempt**: construct new correspondence source for each primitive direction independent of knowing its Chow representative |

## Why the low-dimensional Hodge proof DOES enter

On all smooth projective complex d-folds, classical Lefschetz (1,1) plus hard Lefschetz shows the entire Hodge problem reduces to primitive middle-type sectors where divisor/hyperplane sources no longer suffice. Therefore the legitimate goal of the world wave/Lefschetz dictionary is to land on primitive rational Hodge pieces with genuine geometric Chow operators; a matching numeral n or grade index in abstract GST channels does not suffice.

The new 10-dimensional model uses an actual **fivefold**, not a 5D assignment to the seven axes. The five is the dimension of X as an independent algebraic realization; the seven axes remain dimensionless.

## The exact obstruction to naive full synthesis

On `GSTGraphV2CMNMCoupledUniverse`, arithmetic transitions leave the geometry node unchanged, while certified geometric transitions preserve existing algebraic witnesses. Hence the currently implemented *product coupling* by itself does not show that an arithmetic information period generates a new geometric Hodge direction. The new verified `combinedWaveCM` and `word_cycleClass` theorems correctly define how a geometric wave operator WOULD interact when constructed, and the fivefold genuine Chow example shows that nontrivial geometric realization is possible. The required new general GST map must be **interaction-bearing**, not merely a Cartesian product of independent graphs.

Source conservation is a theorem, not pessimism: every actual original-X Chow correspondence word sends the existing cycle-class image into itself. To make the orbit complete, the geometric construction must cover all primitive Hodge directions by actual new native sources.

| Added curvature source + genuine augmented wave frame | One native cyclic fold | **Lean green** [42683986245](https://github.com/kyo-oo/HC-PROOF/actions/runs/42683986245): one native/Betti cycle-class-compatible operator, exact cyclic orbit, all Hodge fiber classes when geometric rank = n+1 |

## Updated exact source-birth formula and the missing arrow

For an existing actual original-X wave frame `Z_i` with geometric duals `D_i`, let `g=cl([N_A,N_B]z_0)` be the class of an additional genuine curvature-born cycle. If a geometrically fixed detector `ell` vanishes on the old frame but has `ell(g)≠0`, define the native correction:

```
Z(alpha) = sum_i D_i(alpha)*Z_i
  + [ell(alpha - sum_i D_i(alpha)*cl(Z_i))/ell(g)]
      * ([N_A,N_B]z_0 - sum_i D_i(g)*Z_i).
```

The Lean theorem gives `alpha=cl(Z(alpha))+residual`, with every old `D_i(residual)=0` and the new `ell(residual)=0`. The exact sixfold realizes a complete ladder via actual geometric correspondences. For arbitrary X one must independently produce enough such sources and their nonzero readouts. The dimensionless seven axes are unchanged.

Full derivation: `research/records/2026-11-10-gst-wave-cm-cosmology-geometric-curvature-residual-synthesis.md`.

## Key artifacts

- `GSTHodgeWaveCurvatureResidualStep.lean`: exact native wave-plus-curvature residual-killing theorem, CI 42679545127 SUCCESS.
- `GSTHodgePrimitiveWaveCurvatureLanding.lean`: original-X p=2 specialization and rank n+1 reconstruction, CI 42683458742 SUCCESS.
- `research/computations/gst_wave_curvature_full_primitive_sixfold_ladder_20261110.wl`: exact 9D primitive rank completion via 7 original-X geometric curvature cycles.
- `GSTHodgeWaveCurvatureCyclicAugmentation.lean`: one native cycle-class-compatible fold from appended genuine curvature source, CI 42683986245 SUCCESS.
- `research/computations/gst_sixfold_curvature_born_nine_cycle_single_fold_20261110.wl`: original-X nine-primitive cyclic fold, orbit/moment determinants both 1.
- `GSTGraphV2IntegratedWaveCMGate.lean`: mixed words and single combined fold, rank-one CM compatibility boundary; run 42663099970 **SUCCESS**.
- `research/computations/gst_cm_wave_single_fold_cyclotomic8_20261109.wl`: exact 8D field/cyclic generator.
- `research/computations/gst_cm_wave_chow_fivefold_codim2_20261109.wl`: actual 10-subset intersection matrix, exact rank-10 operator.
- `research/records/2026-11-09-gst-wave-cm-chow-fivefold-codim-two-full-cyclic-geometric-proof.md`: original-X Chow construction in all weights.
- `research/records/2026-11-09-gst-entire-wave-cm-curvature-ncohomology-hypothesis-attack.md`: alphaXiv-extracted literature comparison and complete proof attempt.
