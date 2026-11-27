# 2026-11-18 — The finite-point native geometric world: the general-N law landing (lane opened)

## What this is

The third concrete lane of the `NativeGSTSingleFoldOrbitLaw` program (after
`GSTNativeSingleFoldOrbitLawLanding.lean`'s cost classification, GREEN at
`23780031` / run 43750693353, and the twelve-point world, GREEN at `cd72153`
/ run 44182950667): **the general-N finite-point world family** — six new
modules discharging

```
NativeGSTSingleFoldOrbitLaw (finitePointWorld N) (finitePointHodgeData N)
```

for EVERY `N ≥ 1` (`[NeZero N]`), at a LIVE weight-0 fiber of rank `N`, with
a certificate whose Krylov orbit is computed by a nilpotent shift — no Krylov
determinant, no numeric certification, at any N.

## The wave-41 recon (the target correction — audit-mandated)

Three recon agents (framework / world-constructor / corpus) plus the doubter's
two computational batteries (64/64 PASS on the lattice saturation battery;
the every-H battery's countermodel) established THE ACTUAL TRUTH about the
general-N target before any Lean was drafted:

1. **The weight-0 fiber is FORCED full for ANY Hodge data.**
   `HodgeBigrading VQ 0` has index type `Fin (0 + 1) = Fin 1` — the only
   slot is the `(0,0)` component, and the `spans` field promotes it to `⊤`.
   Hence `rationalHodgeSubspace (H.hodgeBigrading 0) = ⊤` for EVERY
   `HodgeBigradedBettiData`. New generic lemma
   `GSTFinitePointHodgeData.rationalHodgeSubspace_eq_top_of_degree_zero`.
   Consequence: `word_hodge` and `seed_hodge` are FREE at weight 0 on every
   world — the certificate's only real content at weight 0 is cyclicity.
2. **The "for EVERY HodgeBigradedBettiData" form is FALSE.** The structure's
   `cycleClass` is an unconstrained linear map; an H with non-surjective
   `cycleClass 0` (e.g. the zero map) traps every orbit in
   `range (cycleClass 0) ⊊ H⁰ ≅ ℚ^N` — a Lean-level countermodel to the
   law at weight 0. The honest target is the CANONICAL discrete Hodge data
   (the degree cycle-class map) at every N — which is what this lane
   discharges.
3. **The twelve-point world is the only concrete world in the corpus** —
   no general-N constructor existed anywhere. The lane's six modules are
   the generalization (a formal bridge `twelvePointWorld ≡ finitePointWorld 12`
   is future work, NOT claimed here).

## The six modules (the lane stack)

| Module | Content |
|---|---|
| `GSTFinitePointWorldCarrier.lean` | `finitePointWorld N : SmoothProjectiveComplexScheme` — Spec of `Fin N → ℂ`, N distinct points on ℙ¹ via `nodeValues i ↦ (i : ℂ)`, smooth, projective, coheight-0 point classification `finitePointEquiv N`. |
| `GSTFinitePointAnalytification.lean` | `finitePointAnalytification N` — the discrete N-point space contract, sections, `ComplexPoint` classification. |
| `GSTFinitePointCohomology.lean` | `finitePointCohomologyIso N : H⁰ ≃ₗ[ℚ] (Fin N → ℚ)` and `finitePointCohomology_subsingleton` (positive-degree vanishing, parity-exactness). |
| `GSTFinitePointHodgeData.lean` | `finitePointHodgeData N` — the canonical discrete Hodge data: the forced weight-0 bigrading, the degree cycle-class map, `zeroCycleClass_point` (the i-th point's class is `Pi.single i 1`), `deadFiber_subsingleton`, and the GENERIC `rationalHodgeSubspace_eq_top_of_degree_zero`. |
| `GSTFinitePointShiftWord.lean` | The letter machinery (ported point-pair correspondences: `Spec ℂ ⟶ X ×_ℂ X` on `(point c, point r)`, each realizing its matrix unit `E_{r,c}`) + **the nilpotent shift word**: `N − 1` unit letters `(i+1, i, 1)`; `shiftWord_op_single` — the word operator carries `e_i ↦ e_{i+1}` under the H⁰ iso. |
| `GSTFinitePointLawLanding.lean` | `finitePointCertificate` (shift word + point-0 seed; both Hodge fields free by the forced-⊤ fiber), `finitePointHodgeOrbit_coords` (the orbit IS the indicator family `e₀ → e₁ → … → e_{N−1}`), `finitePointCertificate_isKrylovCyclic` (the indicators span), **`finitePoint_law`** (weight 0 by the shift certificate; p ≥ 1 dead by the empty word + subsingleton), `finitePoint_FS`, `finitePoint_everyHodge` (through `exactHodge_of_one_GST_fold_orbit`), and `the_finite_point_native_world_package` (the 5-fold capstone). |

## What is proved (exact statements)

1. `finitePoint_law (N) [NeZero N] :
     NativeGSTSingleFoldOrbitLaw (finitePointWorld N) (finitePointHodgeData N)`
   — the law at EVERY weight: weight 0 live (rank N) by the shift
   certificate; every p ≥ 1 dead (the discrete N-point space has no
   positive-degree rational singular cohomology).
2. `finitePoint_everyHodge :
     EveryHodgeClassIsRationalAlgebraic (finitePointHodgeData N)` — through
   the repository's conditional chain (`exactHodge_of_one_GST_fold_orbit`).
3. `the_finite_point_native_world_package` — the law ∧ every-Hodge ∧ the
   per-weight FS datum (through the native⇒typed bridge
   `gst_FS_of_native_law`, at the bridge's own spelling) ∧ the dead-weight
   subsingleton at weight 1 ∧ the live-witness seed (the point-0 cycle:
   class in the fiber, class ≠ 0).
4. The generic `rationalHodgeSubspace_eq_top_of_degree_zero` — for ANY
   `(V, H)`: the weight-0 rational Hodge fiber is the whole H⁰.

## The mathematics of the certificate (why no determinant)

The twelve-point lane needed a 26-letter fold word `Twave = U + J + M` with
`det[Krylov(T, seed₁₂)] = −1,149,656,584,000 ≠ 0` (five-method certified)
because its word was designed around the owner's fold matrix. The general-N
certificate replaces it with the **nilpotent shift**: the word
`[(1, E_{1,0}), …, (1, E_{N−1,N−2})]` (each `E_{r,c}` a genuine point-pair
correspondence letter) sums to the shift operator `S` with `S e_i = e_{i+1}`
and `S^N = 0`. The Krylov orbit of the point-0 seed is then literally
`e₀, e₁, …, e_{N−1}, 0, 0, …` — the standard basis — and cyclicity is the
statement that the indicators span `Fin N → ℚ`. The only per-N content is
the letter-list bookkeeping (`shiftWordData`: the `N − 1` entries
`(⟨i+1, _⟩, i, 1)`; `shiftWordData_sum`: the column-sum at column `i` is the
successor indicator, by `List.sum_eq_single_of_mem`).

## Port disclosure (audit-mandated)

* The letter machinery of `GSTFinitePointShiftWord.lean` (from
  `comap_evalRingHom_default` through `lettersOf`, the operator unfoldings,
  `wordOp_pointClass`, `module_decomp`) is the CI-green twelve-point twin
  ported under the lane rename map (`twelvePoint ↦ finitePoint`,
  `Fin 12 ↦ Fin N`, explicit `N` threading, the local point abbrev deleted in
  favor of `GSTFinitePointHodgeData.finitePointPt`). Proof bodies verbatim;
  the twin's wave-19..40 seam-hardening comments are preserved verbatim as
  the CI repair guide.
* The twin's Twave-specific parts (foldWordData, the 26-entry matrix, the
  144-entry sweeps, `foldWord_op_pointClass`, `twelvePointFoldWord_op`,
  `twelvePointFoldWord_hodge`) are NOT ported — replaced by the shift
  machinery; the law landing discharges `word_hodge` itself via the generic
  forced-⊤ fiber lemma.
* The carrier/analytification/cohomology/HodgeData modules are likewise
  ports of the twin's four modules (33/30/21/24 declarations respectively,
  per the drafting agents' status blocks); the landing module is a
  re-architecture (the orbit equation carries the `n < N` bound the
  twelve-point total Krylov table did not need).
* Every `PORT RISK` site flagged by the drafting agents is documented in the
  files' DRAFT STATUS blocks; the CI lane owns the kernel check.

## Non-claims (exact scope)

* This is a restricted-class theorem under the AGENTS.md acceptance test,
  NOT the Hodge conjecture: the worlds are 0-dimensional (finite discrete),
  and the Hodge data is the canonical discrete one.
* The law is NOT claimed for arbitrary `HodgeBigradedBettiData` on these
  worlds — that form is FALSE in general (the cycleClass countermodel
  above); at monogenic/dead weights the landing-file classification already
  covers arbitrary H.
* No formal bridge `twelvePointWorld ≡ finitePointWorld 12` is constructed
  here; the twelve-point lane remains independently green at `cd72153`.
* Live weights at p ≥ 1 on positive-dimensional worlds remain the genuine
  geometric core (untouched, as in the twelve-point record).

## Registration

* `lakefile.toml`: new lib `GSTFinitePointNativeWorldUpgrade`, the six roots
  (the full import closure is appended at CI time by
  `scripts/gst_lean_dependency_roots.py`, invoked by the lane as
  `GSTFinitePointNativeWorldLib GSTFinitePointLawLanding`).
* CI lane: `.github/workflows/gst-finite-point-native-world.yml` — the
  twelve-point lane's hardened template (elan v4.2.4 pinned tarball with
  3×2 mirror retry, toolchain + `.lake/build` caches, 16800 s build cap,
  sorryAx hard gate, log artifact always).
* Static verification only from this sandbox: comment-aware paren/bracket
  balance 0 on all six files; zero `sorry`/`admit`/`native_decide`/new
  axioms; no `twelvePoint`/`Fin 12` identifiers survive outside port-notes.

## CI status

No Lean compilation is claimed from this sandbox. The lane above owns the
kernel check; per AGENTS.md rule 7, no green run is cited until the run
exists at the pushed SHA. (This record will be updated with the run id and
the adjudication of the first wave.)
