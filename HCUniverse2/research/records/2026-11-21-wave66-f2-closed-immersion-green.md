# Wave 66 — F2 CLOSED: the chartwise closed-immersion certification, CI-GREEN

Date: 2026-11-21. Author: the reconstruction session's wave-66 strike
(four agents + four commander repair rounds 66.1–66.4).

## The kill

`GSTFiniteLineClosedImmersion.lean` — **CI-GREEN: run 44918529342 at
`1cf6ff2`** (the fourth adjudication round; the arc 14 errors → 1 → 1 → 1 →
0). All three headline receipts depend only on
`[propext, Classical.choice, Quot.sound]`:

* `awayMap_surjective` — the Away-lift surjectivity of the graded quotient
  presentation's chart maps (the piece-level lift `mem_lineGrading` +
  `Away.mk_surjective` + `Away.map_mk` + the arity roundtrip);
* `chart_closed` — the per-chart closed immersion (the five-stage cascade:
  the retype, the awayι square (`awayι_comp_map` + the two
  `basicOpenIsoSpec_inv_ι` rfl-rewrites), the mono-cancellation reduction,
  the cancel-of-respectsIso peels, `spec_of_surjective`);
* `finiteLine_closedImmersion` — THE ASSEMBLY: the embedding of
  `Proj (lineGrading M)` into `ℙ^{2M-1}` is a closed immersion, chartwise
  via `IsZariskiLocalAtTarget.of_iSup_eq_top` over the `D+(X j)` cover
  (the cover twins `lineCoverHomogeneous`/`lineCoverSpan` feeding
  `Proj.iSup_basicOpen_eq_top'` at the ambient arity `Fin (2M-1+1)`).

## The repair arc (the four disease families, each killed in one round)

1. **66.1 (58c2cd2 → e6db0c7)**: the namespace disease — the module's
   preamble lacked `open AlgebraicGeometry CategoryTheory` (the carrier's
   own pattern); 14 errors were one missing line. §1+§2 receipts were
   already kernel-green in the very first run.
2. **66.2 (e6db0c7 → 3c8e20f)**: the dependent-rewrite disease —
   `rw [← hmr] at h` abstracted the OPEN inside `.ι` (the motive is not
   type correct); rebuilt on the pin's own
   `fromOfGlobalSections_morphismRestrict` pattern
   (`rw [← Iso.inv_comp_eq, ← cancel_mono ι]` + the append-ι chain).
3. **66.3 (3c8e20f → 5c06365)**: the implicit-transparency disease — the
   hfac equation's type rides the rfl-defeq of the two open spellings
   (preimage vs chart open, `map_preimage_basicOpen`); `rw`'s pattern
   matching at implicit transparency cannot see it — the TERM-MODE
   rebuild (`refine (Iso.inv_comp_eq _).mp ?_` + the e1/e2/e4 `Eq.trans`
   chain with `congrArg`-carried `morphismRestrict_ι`), every step at
   default transparency where the defeq IS found. Also: the §4 assembly
   theorem restored (the 66.2 splice collateral).
4. **66.4 (5c06365 → 1cf6ff2)**: the assoc-direction disease — the pin's
   `Category.assoc : (f ≫ g) ≫ h = f ≫ g ≫ h` (the Category-CLASS field
   direction, verified verbatim); e1 forward, e4 symm. GREEN.

## The wave ledger

* W66-A: the cover twins (delivered; the applied `lineCover_iSup` package).
* W66-B: the Away-lift surjectivity (delivered; kernel-green first run).
* W66-C: the chart cascade (delivered with the designated repair points —
  #1 fired exactly as predicted in 66.2).
* W66-D: the assembly (commander-executed per doctrine after the D-slot
  agents hit context deadlines).

## The frontier after this wave

F3 (smoothness — `GSTFiniteLineSmoothness.lean` staged: B's substrate +
the chart square + the cascade; the battle cores — the chart ring ≃ ℂ[T] —
in commander authoring), then the analytification receipt, the gate
discharges, and the composition with the wave-64 cyclic word (the general-M
law module `GSTFiniteLineGeneralMLaw.lean` — 1,031 lines — staged in CI
adjudication this same session).
