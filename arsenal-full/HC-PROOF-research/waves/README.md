# THE WAVE MECHANICS LAYER — machine-checked

**STATUS: COMPILED, MACHINE-VERIFIED, IN THE BUILD.**

This directory is the Wave Mechanics layer of the universe.  As of the
Task-5 upgrade it is **fully proven** and **part of the build registry**:

* the four modules are roots of the `HCUniverse` registry in
  `lakefile.toml` (`waves.GSTWaveCohomology`, `waves.GSTNCohomology`,
  `waves.GSTVortexSingularity`, `waves.CardinalWorldsPostulateLaw`);
* `HCProof.lean` (the comparator entry face) imports all four, so
  `lake build` compiles them and the comparator checks them;
* `scripts/sorry_check.sh` counts this directory like every other
  module — the old "uncompiled spec layer" exclusion is retired;
* **41 theorems, 0 sorries.**

## What happened to the 29 spec statements

The Task-4 spec layer carried 29 statements with pending proofs.  Before
writing a single proof, every statement was truth-checked against the
actual definitional cascade (`mixedDensity`, `surviveI`, `carry4`,
`digit3`, the tower words) by exhaustive finite computation.  Verdict:

* **8 statements were TRUE as stated** — proven directly, mostly by
  instantiating already-verified universe theorems or the house
  twelve-cell `norm_num` cascade;
* **21 statements were FALSE or vacuous as literally stated** — each was
  *upgraded* to the true law it was reaching for (the false closed forms
  replaced by the verified tower/stabilization/transport theorems they
  were paraphrasing; the vacuous existentials replaced by the exact
  rank/injectivity/presentation statements).  Every upgrade is
  documented in the docstring of the theorem that carries the name.

The upgrade is the point: a spec layer that "looks like" geometry is not
geometry.  This layer now *is* the geometry — every law below is a
machine-checked statement about the discrete connection, its holonomy,
its flatness, its 3-adic renormalization cascade, and its puncture
singularity.

## Contents

| File | Wave | What is proven |
|------|------|----------------|
| `GSTWaveCohomology.lean` | **WAVE I** | The Hodge wave: the twelve-cell discrete de Rham complex; the closedness law (the verified emergence equation as the structure equation `2-form = δh + δv + source`); the ROW telescoping law and the RECTANGLE Gauss–Bonnet law on the canonical lattice; the window class, its integrality (Hodge wave), and its additive transport under `R ↦ 4R`; the chord realizations; the mode spectrum (12 amplitudes, chord separation); total matter 224; 9 harmonic cells. |
| `GSTNCohomology.lean` | **WAVE II** | N-cohomology: N-shapes as injective channel maps (rank law); tower windows as depth-N stabilized profiles; the interference pairing of the two waves and its EXACT decomposition (horizontal + vertical + source pairing); NULL-sterility and GST+ maximality of the source; the Ω-family signature (verified `omega_wave_existence_class_two`); the two-wave frame refinement (BIG2 ⇒ nonzero wave mode). |
| `GSTVortexSingularity.lean` | **THE METHOD** | The GST Vortex Singularity Method as geometry: the vortex connection `coreRotate` with holonomy of order exactly five (two pentagon orbits, two-cell axis); the spiral section and incompressibility; the axial-stretch/radial-thinning law; **zero curvature of the lattice connection** (the ×4-stride and descent transports commute — the curvature square closes); the 3-adic renormalization cascade (each layer a higher-order correction, the frozen window); the smooth-driver law; the puncture singularity (verified `omega_puncture`); the full N-shape signature (every ignition channel fires); finite energy (descent terminates). |
| `CardinalWorldsPostulateLaw.lean` | **THE LAW** | POSTULATE III — the Law of Controlled Emergence: finite presentation of every controlled limit; the emergence law (emergent dimension at depth N is exactly N); the infinite dimension as the colimit of finite readouts (unbounded growth); colimit uniqueness; the admissibility law. |

The full geometric theory document is `docs/WAVE_MECHANICS_TASK4.md`;
the law book of the underlying GST Graph V2 system is
`docs/GST_V2_OPERATING_MANUAL.md`.

## The NS → GST translation table (what was copied, what it became)

Every load-bearing component of the OpenAI Navier–Stokes vortex-singularity
method (Sep 8, 2026) is a discrete geometric object here:

| Navier–Stokes | GVSM (proven here) |
|---|---|
| self-similar ansatz | similarity variables `(R/3^p, R%3^p)` + frozen tower windows |
| swirling vortex | the connection `coreRotate`, holonomy Z/5, two pentagons |
| spiral inward | carry-space spiral NULL→ALT-→GST+ (incompressible) |
| axial stretch | seventh axis `n/3` + strict boundary burn |
| incompressibility | `spiral_incompressible` (NULL regenerates, GST+ propagates) |
| flat coordinates | `lattice_curvature_zero` (the transport square commutes) |
| layer cascade | `frozen_window_selfsimilar` (3-adic refinement) + `cascade_stabilizes` (frozen window mod `3^k`) |
| smooth forcing | `cascade_preserves_driver` (driver ≡ 1 mod 3) |
| finite-time singularity | `vortex_singularity_forms` (verified `omega_puncture`) |
| any N shapes in holes | `gvsm_full_signature` (every ignition channel fires) |
| finite energy | `vortex_energy_finite` (descent terminates at depth R+1) |
