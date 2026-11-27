/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import Mathlib
import HCUniverse2.GSTHypothesisComplete
import HCUniverse2.GST2DMixedEmergence

/-!
# THE GST HYPOTHESIS SPANNING PROOF — the owner's twelve-cell world, complete

This module proves the single remaining falsifiable line of the GST
hypothesis — the orbit-spanning law
`GSTHypothesisComplete.GSTHypothesisComplete` — **unconditionally, for the
owner's own twelve-cell wave world**, using only the owner's mathematics:

* the owner's exact SURVIVE source (`surviveI`, the literal definition
  behind `GSTGraphV2CMWaveFusion.sourceMultiplicity`: zero on nine cells,
  1 at (1,1) and (2,2), 2 at the maximum fixed cell (3,2));
* the owner's full combined fold `F₁ = U + J + M` (`F12 ownerSource 1`,
  exactly `navigationControlledF 1 = T` in `GSTGraphV2CMWaveFusion`);
* the owner's genuine native seed `seed12 = e_{(0,0)} + e_{(0,1)}`.

## The theorem

`span_range_worldOrbit_eq_top`: the rational span of the full fold orbit
`{N^n seed12 : n}` is the ENTIRE twelve-cell world `WaveSignal12`.
The certificate is an exact Gauss-Jordan elimination over ℚ, fully
machine-generated and kernel-checkable: the twelve orbit values `K_0 … K_11`
are computed by the fold itself (`orbit_val`), and each of the twelve cell
basis vectors is an explicit rational combination of them (`eCell_eq_cert`).
No `sorry`, no new axioms, no analysis.

This is the exact Krylov determinant -1149656584000 ≠ 0 of the records
(2026-11-12 spectral closure; `GSTGraphV2CMWaveFusion.orbitMatrix`), now
written as a Lean proof; the GitHub CI lane owns the kernel check.
Combined with `GSTHypothesisComplete.gst_hypothesis_landing` and the full
twelve-cell law package, the GST hypothesis is COMPLETE for the owner's
world: the whole world is born from the seed by the owner's fold.

## Scope (audit-accurate)

This closes the spanning law for the owner's twelve-cell wave world (the
hypothesis's own carrier, `hodgeFiber = ⊤` — the maximal designated fiber;
any smaller fiber would be a weaker statement). It does not assert the
classical Hodge conjecture for arbitrary smooth projective varieties; the
`AGENTS.md` withdrawal rule remains binding. The `the_world_landing`
corollary below instantiates the general reduction `gst_hypothesis_landing`
and is a formality on this face (the world cycle-class map is the identity;
the content of this module is `span_range_worldOrbit_eq_top`). The
companion module `GSTHypothesisSpanningCompilerFace.lean` transports the
same certificate to every `IntersectionChowFrame` via the wave compiler.
-/

noncomputable section
namespace GSTHypothesisSpanning

open GSTHypothesisComplete

set_option maxHeartbeats 30000000
set_option maxRecDepth 400000

/-! ## §1 The owner's exact SURVIVE source -/

/-- The owner's literal matter source on the twelve cells: `surviveI`,
the exact definition behind `GSTGraphV2CMWaveFusion.sourceMultiplicity`.
Certified values: 0 at the null fixed cell, 2 at the maximum fixed cell. -/
def ownerSource : TwelveCell → ℚ :=
  fun s => (GST2DMixedEmergence.surviveI s.1.val s.2.val : ℚ)

theorem ownerSource_null : ownerSource nullCell = 0 := by decide
theorem ownerSource_max : ownerSource maxCell = 2 := by decide

theorem ownerSource_val_0_0 : ownerSource ((0 : Fin 4), (0 : Fin 3)) = (0 : ℚ) := by decide
theorem ownerSource_val_0_1 : ownerSource ((0 : Fin 4), (1 : Fin 3)) = (0 : ℚ) := by decide
theorem ownerSource_val_0_2 : ownerSource ((0 : Fin 4), (2 : Fin 3)) = (0 : ℚ) := by decide
theorem ownerSource_val_1_0 : ownerSource ((1 : Fin 4), (0 : Fin 3)) = (0 : ℚ) := by decide
theorem ownerSource_val_1_1 : ownerSource ((1 : Fin 4), (1 : Fin 3)) = (1 : ℚ) := by decide
theorem ownerSource_val_1_2 : ownerSource ((1 : Fin 4), (2 : Fin 3)) = (0 : ℚ) := by decide
theorem ownerSource_val_2_0 : ownerSource ((2 : Fin 4), (0 : Fin 3)) = (0 : ℚ) := by decide
theorem ownerSource_val_2_1 : ownerSource ((2 : Fin 4), (1 : Fin 3)) = (0 : ℚ) := by decide
theorem ownerSource_val_2_2 : ownerSource ((2 : Fin 4), (2 : Fin 3)) = (1 : ℚ) := by decide
theorem ownerSource_val_3_0 : ownerSource ((3 : Fin 4), (0 : Fin 3)) = (0 : ℚ) := by decide
theorem ownerSource_val_3_1 : ownerSource ((3 : Fin 4), (1 : Fin 3)) = (0 : ℚ) := by decide
theorem ownerSource_val_3_2 : ownerSource ((3 : Fin 4), (2 : Fin 3)) = (2 : ℚ) := by decide

/-! ## §2 The native fold `N = F₁ = U + J + M` and the world fold -/

theorem U12_add (a b : WaveSignal12) : U12 (a + b) = U12 a + U12 b := by
  funext s; simp [U12, Pi.add_apply]

theorem U12_smul (k : ℚ) (a : WaveSignal12) : U12 (k • a) = k • U12 a := by
  funext s; simp [U12, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem M12_add (srcf : TwelveCell → ℚ) (a b : WaveSignal12) :
    M12 srcf (a + b) = M12 srcf a + M12 srcf b := by
  funext s; simp [M12, Pi.add_apply, mul_add]

theorem M12_smul (srcf : TwelveCell → ℚ) (k : ℚ) (a : WaveSignal12) :
    M12 srcf (k • a) = k • M12 srcf a := by
  funext s; simp only [M12, Pi.smul_apply, smul_eq_mul]; ring

/-- The fold is additive in the wave argument. Pointwise exact. -/
theorem F12_add (src : TwelveCell → ℚ) (b : ℚ) (u v : WaveSignal12) :
    F12 src b (u + v) = F12 src b u + F12 src b v := by
  funext s
  simp only [F12, U12, J12, M12, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The fold is homogeneous in the wave argument. Pointwise exact. -/
theorem F12_smul (src : TwelveCell → ℚ) (b k : ℚ) (u : WaveSignal12) :
    F12 src b (k • u) = k • F12 src b u := by
  funext s
  simp only [F12, U12, J12, M12, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The owner's full combined fold `F₁ = U + J + M` as a `Module.End`. -/
def N12 : Module.End ℚ WaveSignal12 where
  toFun u := F12 ownerSource 1 u
  map_add' u v := F12_add ownerSource 1 u v
  map_smul' k u := F12_smul ownerSource 1 k u

/-- Pointwise shape of the fold. -/
theorem N12_val (u : WaveSignal12) (s : TwelveCell) :
    N12 u s =
      u (shuffleCell s) + cmSign s * u (mirrorCell s) + ownerSource s * u s := by
  simp only [N12, LinearMap.coe_mk, AddHom.coe_mk, F12, U12, J12, M12,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]

/-- The world fold: the native and Betti actions coincide through the
identity cycle-class map — the owner's commuting square on the world. -/
def worldFold : GSTFold WaveSignal12 WaveSignal12 where
  cycleClass := LinearMap.id
  native := N12
  betti := N12
  natural z := rfl

/-- The full fold orbit of the owner's genuine native seed. -/
def worldOrbit : ℕ → WaveSignal12 := nativeOrbit worldFold seed12

theorem worldOrbit_zero : worldOrbit 0 = seed12 := rfl
theorem worldOrbit_succ (n : ℕ) : worldOrbit (n + 1) = N12 (worldOrbit n) := rfl

/-! ## §3 The exact orbit table (the first twelve fold iterates) -/

/-- The owner's exact Krylov table: `Kvec n` is the n-th fold iterate of
the seed, for `n : Fin 12`. `Kvec 0` is the seed itself. -/
def Kvec : Fin 12 → WaveSignal12 :=
  fun n s =>
    if n = 0 then seed12 s
    else if n = 1 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (1 : ℚ) else if s = ((1 : Fin 4), (0 : Fin 3)) then (1 : ℚ) else if s = ((3 : Fin 4), (1 : Fin 3)) then (-1 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-1 : ℚ) else 0)
    else if n = 2 then (if s = ((0 : Fin 4), (1 : Fin 3)) then (-1 : ℚ) else if s = ((2 : Fin 4), (2 : Fin 3)) then (-2 : ℚ) else if s = ((3 : Fin 4), (0 : Fin 3)) then (1 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-4 : ℚ) else 0)
    else if n = 3 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (-4 : ℚ) else if s = ((0 : Fin 4), (2 : Fin 3)) then (-3 : ℚ) else if s = ((1 : Fin 4), (0 : Fin 3)) then (-3 : ℚ) else if s = ((1 : Fin 4), (2 : Fin 3)) then (1 : ℚ) else if s = ((2 : Fin 4), (2 : Fin 3)) then (-2 : ℚ) else if s = ((3 : Fin 4), (1 : Fin 3)) then (1 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-12 : ℚ) else 0)
    else if n = 4 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (-16 : ℚ) else if s = ((0 : Fin 4), (1 : Fin 3)) then (1 : ℚ) else if s = ((0 : Fin 4), (2 : Fin 3)) then (-2 : ℚ) else if s = ((1 : Fin 4), (0 : Fin 3)) then (-2 : ℚ) else if s = ((1 : Fin 4), (1 : Fin 3)) then (1 : ℚ) else if s = ((2 : Fin 4), (0 : Fin 3)) then (-4 : ℚ) else if s = ((2 : Fin 4), (2 : Fin 3)) then (2 : ℚ) else if s = ((3 : Fin 4), (0 : Fin 3)) then (-6 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-32 : ℚ) else 0)
    else if n = 5 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (-48 : ℚ) else if s = ((0 : Fin 4), (1 : Fin 3)) then (1 : ℚ) else if s = ((0 : Fin 4), (2 : Fin 3)) then (8 : ℚ) else if s = ((1 : Fin 4), (0 : Fin 3)) then (3 : ℚ) else if s = ((1 : Fin 4), (1 : Fin 3)) then (1 : ℚ) else if s = ((1 : Fin 4), (2 : Fin 3)) then (-10 : ℚ) else if s = ((2 : Fin 4), (0 : Fin 3)) then (-2 : ℚ) else if s = ((2 : Fin 4), (1 : Fin 3)) then (-5 : ℚ) else if s = ((2 : Fin 4), (2 : Fin 3)) then (4 : ℚ) else if s = ((3 : Fin 4), (0 : Fin 3)) then (-4 : ℚ) else if s = ((3 : Fin 4), (1 : Fin 3)) then (-1 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-80 : ℚ) else 0)
    else if n = 6 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (-128 : ℚ) else if s = ((0 : Fin 4), (2 : Fin 3)) then (8 : ℚ) else if s = ((1 : Fin 4), (0 : Fin 3)) then (5 : ℚ) else if s = ((1 : Fin 4), (1 : Fin 3)) then (-14 : ℚ) else if s = ((1 : Fin 4), (2 : Fin 3)) then (-6 : ℚ) else if s = ((2 : Fin 4), (0 : Fin 3)) then (18 : ℚ) else if s = ((2 : Fin 4), (1 : Fin 3)) then (-3 : ℚ) else if s = ((3 : Fin 4), (0 : Fin 3)) then (11 : ℚ) else if s = ((3 : Fin 4), (1 : Fin 3)) then (-6 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-192 : ℚ) else 0)
    else if n = 7 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (-320 : ℚ) else if s = ((0 : Fin 4), (1 : Fin 3)) then (-20 : ℚ) else if s = ((0 : Fin 4), (2 : Fin 3)) then (-11 : ℚ) else if s = ((1 : Fin 4), (1 : Fin 3)) then (-23 : ℚ) else if s = ((1 : Fin 4), (2 : Fin 3)) then (29 : ℚ) else if s = ((2 : Fin 4), (0 : Fin 3)) then (14 : ℚ) else if s = ((2 : Fin 4), (1 : Fin 3)) then (32 : ℚ) else if s = ((2 : Fin 4), (2 : Fin 3)) then (-11 : ℚ) else if s = ((3 : Fin 4), (0 : Fin 3)) then (13 : ℚ) else if s = ((3 : Fin 4), (1 : Fin 3)) then (-3 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-448 : ℚ) else 0)
    else if n = 8 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (-768 : ℚ) else if s = ((0 : Fin 4), (1 : Fin 3)) then (-26 : ℚ) else if s = ((0 : Fin 4), (2 : Fin 3)) then (-24 : ℚ) else if s = ((1 : Fin 4), (0 : Fin 3)) then (-31 : ℚ) else if s = ((1 : Fin 4), (1 : Fin 3)) then (38 : ℚ) else if s = ((1 : Fin 4), (2 : Fin 3)) then (27 : ℚ) else if s = ((2 : Fin 4), (0 : Fin 3)) then (-40 : ℚ) else if s = ((2 : Fin 4), (1 : Fin 3)) then (37 : ℚ) else if s = ((2 : Fin 4), (2 : Fin 3)) then (-14 : ℚ) else if s = ((3 : Fin 4), (0 : Fin 3)) then (-11 : ℚ) else if s = ((3 : Fin 4), (1 : Fin 3)) then (52 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-1024 : ℚ) else 0)
    else if n = 9 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (-1792 : ℚ) else if s = ((0 : Fin 4), (1 : Fin 3)) then (90 : ℚ) else if s = ((0 : Fin 4), (2 : Fin 3)) then (-3 : ℚ) else if s = ((1 : Fin 4), (0 : Fin 3)) then (-40 : ℚ) else if s = ((1 : Fin 4), (1 : Fin 3)) then (102 : ℚ) else if s = ((1 : Fin 4), (2 : Fin 3)) then (-51 : ℚ) else if s = ((2 : Fin 4), (0 : Fin 3)) then (-51 : ℚ) else if s = ((2 : Fin 4), (1 : Fin 3)) then (-78 : ℚ) else if s = ((2 : Fin 4), (2 : Fin 3)) then (69 : ℚ) else if s = ((3 : Fin 4), (0 : Fin 3)) then (-55 : ℚ) else if s = ((3 : Fin 4), (1 : Fin 3)) then (63 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-2304 : ℚ) else 0)
    else if n = 10 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (-4096 : ℚ) else if s = ((0 : Fin 4), (1 : Fin 3)) then (165 : ℚ) else if s = ((0 : Fin 4), (2 : Fin 3)) then (124 : ℚ) else if s = ((1 : Fin 4), (0 : Fin 3)) then (159 : ℚ) else if s = ((1 : Fin 4), (1 : Fin 3)) then (-27 : ℚ) else if s = ((1 : Fin 4), (2 : Fin 3)) then (-106 : ℚ) else if s = ((2 : Fin 4), (0 : Fin 3)) then (48 : ℚ) else if s = ((2 : Fin 4), (1 : Fin 3)) then (-153 : ℚ) else if s = ((2 : Fin 4), (2 : Fin 3)) then (172 : ℚ) else if s = ((3 : Fin 4), (0 : Fin 3)) then (-43 : ℚ) else if s = ((3 : Fin 4), (1 : Fin 3)) then (-168 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-5120 : ℚ) else 0)
    else if n = 11 then (if s = ((0 : Fin 4), (0 : Fin 3)) then (-9216 : ℚ) else if s = ((0 : Fin 4), (1 : Fin 3)) then (-195 : ℚ) else if s = ((0 : Fin 4), (2 : Fin 3)) then (215 : ℚ) else if s = ((1 : Fin 4), (0 : Fin 3)) then (337 : ℚ) else if s = ((1 : Fin 4), (1 : Fin 3)) then (-286 : ℚ) else if s = ((1 : Fin 4), (2 : Fin 3)) then (5 : ℚ) else if s = ((2 : Fin 4), (0 : Fin 3)) then (230 : ℚ) else if s = ((2 : Fin 4), (1 : Fin 3)) then (75 : ℚ) else if s = ((2 : Fin 4), (2 : Fin 3)) then (-155 : ℚ) else if s = ((3 : Fin 4), (0 : Fin 3)) then (283 : ℚ) else if s = ((3 : Fin 4), (1 : Fin 3)) then (-318 : ℚ) else if s = ((3 : Fin 4), (2 : Fin 3)) then (-11264 : ℚ) else 0)
    else 0

/-! Cell tables for kernel evaluation of the fold on literals.
Audit fallback: `rw` these if any `norm_num` goal stalls. -/
theorem shuffleCell_val_0_0 : shuffleCell ((0 : Fin 4), (0 : Fin 3)) = ((0 : Fin 4), (0 : Fin 3)) := by decide
theorem shuffleCell_val_0_1 : shuffleCell ((0 : Fin 4), (1 : Fin 3)) = ((1 : Fin 4), (1 : Fin 3)) := by decide
theorem shuffleCell_val_0_2 : shuffleCell ((0 : Fin 4), (2 : Fin 3)) = ((2 : Fin 4), (2 : Fin 3)) := by decide
theorem shuffleCell_val_1_0 : shuffleCell ((1 : Fin 4), (0 : Fin 3)) = ((0 : Fin 4), (1 : Fin 3)) := by decide
theorem shuffleCell_val_1_1 : shuffleCell ((1 : Fin 4), (1 : Fin 3)) = ((1 : Fin 4), (2 : Fin 3)) := by decide
theorem shuffleCell_val_1_2 : shuffleCell ((1 : Fin 4), (2 : Fin 3)) = ((3 : Fin 4), (0 : Fin 3)) := by decide
theorem shuffleCell_val_2_0 : shuffleCell ((2 : Fin 4), (0 : Fin 3)) = ((0 : Fin 4), (2 : Fin 3)) := by decide
theorem shuffleCell_val_2_1 : shuffleCell ((2 : Fin 4), (1 : Fin 3)) = ((2 : Fin 4), (0 : Fin 3)) := by decide
theorem shuffleCell_val_2_2 : shuffleCell ((2 : Fin 4), (2 : Fin 3)) = ((3 : Fin 4), (1 : Fin 3)) := by decide
theorem shuffleCell_val_3_0 : shuffleCell ((3 : Fin 4), (0 : Fin 3)) = ((1 : Fin 4), (0 : Fin 3)) := by decide
theorem shuffleCell_val_3_1 : shuffleCell ((3 : Fin 4), (1 : Fin 3)) = ((2 : Fin 4), (1 : Fin 3)) := by decide
theorem shuffleCell_val_3_2 : shuffleCell ((3 : Fin 4), (2 : Fin 3)) = ((3 : Fin 4), (2 : Fin 3)) := by decide
theorem mirrorCell_val_0_0 : mirrorCell ((0 : Fin 4), (0 : Fin 3)) = ((3 : Fin 4), (2 : Fin 3)) := by decide
theorem mirrorCell_val_0_1 : mirrorCell ((0 : Fin 4), (1 : Fin 3)) = ((3 : Fin 4), (1 : Fin 3)) := by decide
theorem mirrorCell_val_0_2 : mirrorCell ((0 : Fin 4), (2 : Fin 3)) = ((3 : Fin 4), (0 : Fin 3)) := by decide
theorem mirrorCell_val_1_0 : mirrorCell ((1 : Fin 4), (0 : Fin 3)) = ((2 : Fin 4), (2 : Fin 3)) := by decide
theorem mirrorCell_val_1_1 : mirrorCell ((1 : Fin 4), (1 : Fin 3)) = ((2 : Fin 4), (1 : Fin 3)) := by decide
theorem mirrorCell_val_1_2 : mirrorCell ((1 : Fin 4), (2 : Fin 3)) = ((2 : Fin 4), (0 : Fin 3)) := by decide
theorem mirrorCell_val_2_0 : mirrorCell ((2 : Fin 4), (0 : Fin 3)) = ((1 : Fin 4), (2 : Fin 3)) := by decide
theorem mirrorCell_val_2_1 : mirrorCell ((2 : Fin 4), (1 : Fin 3)) = ((1 : Fin 4), (1 : Fin 3)) := by decide
theorem mirrorCell_val_2_2 : mirrorCell ((2 : Fin 4), (2 : Fin 3)) = ((1 : Fin 4), (0 : Fin 3)) := by decide
theorem mirrorCell_val_3_0 : mirrorCell ((3 : Fin 4), (0 : Fin 3)) = ((0 : Fin 4), (2 : Fin 3)) := by decide
theorem mirrorCell_val_3_1 : mirrorCell ((3 : Fin 4), (1 : Fin 3)) = ((0 : Fin 4), (1 : Fin 3)) := by decide
theorem mirrorCell_val_3_2 : mirrorCell ((3 : Fin 4), (2 : Fin 3)) = ((0 : Fin 4), (0 : Fin 3)) := by decide
theorem cmSign_val_0_0 : cmSign ((0 : Fin 4), (0 : Fin 3)) = (1 : ℚ) := by decide
theorem cmSign_val_0_1 : cmSign ((0 : Fin 4), (1 : Fin 3)) = (1 : ℚ) := by decide
theorem cmSign_val_0_2 : cmSign ((0 : Fin 4), (2 : Fin 3)) = (-1 : ℚ) := by decide
theorem cmSign_val_1_0 : cmSign ((1 : Fin 4), (0 : Fin 3)) = (1 : ℚ) := by decide
theorem cmSign_val_1_1 : cmSign ((1 : Fin 4), (1 : Fin 3)) = (1 : ℚ) := by decide
theorem cmSign_val_1_2 : cmSign ((1 : Fin 4), (2 : Fin 3)) = (1 : ℚ) := by decide
theorem cmSign_val_2_0 : cmSign ((2 : Fin 4), (0 : Fin 3)) = (-1 : ℚ) := by decide
theorem cmSign_val_2_1 : cmSign ((2 : Fin 4), (1 : Fin 3)) = (-1 : ℚ) := by decide
theorem cmSign_val_2_2 : cmSign ((2 : Fin 4), (2 : Fin 3)) = (-1 : ℚ) := by decide
theorem cmSign_val_3_0 : cmSign ((3 : Fin 4), (0 : Fin 3)) = (1 : ℚ) := by decide
theorem cmSign_val_3_1 : cmSign ((3 : Fin 4), (1 : Fin 3)) = (-1 : ℚ) := by decide
theorem cmSign_val_3_2 : cmSign ((3 : Fin 4), (2 : Fin 3)) = (-1 : ℚ) := by decide

/-! ### The fold steps: `N12 (Kvec k) = Kvec (k + 1)` -/
theorem N12_Kvec_step_0 : N12 (Kvec 0) = Kvec 1 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_1 : N12 (Kvec 1) = Kvec 2 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_2 : N12 (Kvec 2) = Kvec 3 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_3 : N12 (Kvec 3) = Kvec 4 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_4 : N12 (Kvec 4) = Kvec 5 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_5 : N12 (Kvec 5) = Kvec 6 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_6 : N12 (Kvec 6) = Kvec 7 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_7 : N12 (Kvec 7) = Kvec 8 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_8 : N12 (Kvec 8) = Kvec 9 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_9 : N12 (Kvec 9) = Kvec 10 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

theorem N12_Kvec_step_10 : N12 (Kvec 10) = Kvec 11 := by
  funext s
  rw [N12_val]
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [Kvec, seed12, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

/-! ### The orbit values are the table -/
theorem orbit_val_0 : worldOrbit ((0 : Fin 12) : ℕ) = Kvec 0 := rfl
theorem orbit_val_1 : worldOrbit ((1 : Fin 12) : ℕ) = Kvec 1 := by
  have h : worldOrbit ((1 : Fin 12) : ℕ) =
      N12 (worldOrbit ((0 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_0]
  exact N12_Kvec_step_0
theorem orbit_val_2 : worldOrbit ((2 : Fin 12) : ℕ) = Kvec 2 := by
  have h : worldOrbit ((2 : Fin 12) : ℕ) =
      N12 (worldOrbit ((1 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_1]
  exact N12_Kvec_step_1
theorem orbit_val_3 : worldOrbit ((3 : Fin 12) : ℕ) = Kvec 3 := by
  have h : worldOrbit ((3 : Fin 12) : ℕ) =
      N12 (worldOrbit ((2 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_2]
  exact N12_Kvec_step_2
theorem orbit_val_4 : worldOrbit ((4 : Fin 12) : ℕ) = Kvec 4 := by
  have h : worldOrbit ((4 : Fin 12) : ℕ) =
      N12 (worldOrbit ((3 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_3]
  exact N12_Kvec_step_3
theorem orbit_val_5 : worldOrbit ((5 : Fin 12) : ℕ) = Kvec 5 := by
  have h : worldOrbit ((5 : Fin 12) : ℕ) =
      N12 (worldOrbit ((4 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_4]
  exact N12_Kvec_step_4
theorem orbit_val_6 : worldOrbit ((6 : Fin 12) : ℕ) = Kvec 6 := by
  have h : worldOrbit ((6 : Fin 12) : ℕ) =
      N12 (worldOrbit ((5 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_5]
  exact N12_Kvec_step_5
theorem orbit_val_7 : worldOrbit ((7 : Fin 12) : ℕ) = Kvec 7 := by
  have h : worldOrbit ((7 : Fin 12) : ℕ) =
      N12 (worldOrbit ((6 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_6]
  exact N12_Kvec_step_6
theorem orbit_val_8 : worldOrbit ((8 : Fin 12) : ℕ) = Kvec 8 := by
  have h : worldOrbit ((8 : Fin 12) : ℕ) =
      N12 (worldOrbit ((7 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_7]
  exact N12_Kvec_step_7
theorem orbit_val_9 : worldOrbit ((9 : Fin 12) : ℕ) = Kvec 9 := by
  have h : worldOrbit ((9 : Fin 12) : ℕ) =
      N12 (worldOrbit ((8 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_8]
  exact N12_Kvec_step_8
theorem orbit_val_10 : worldOrbit ((10 : Fin 12) : ℕ) = Kvec 10 := by
  have h : worldOrbit ((10 : Fin 12) : ℕ) =
      N12 (worldOrbit ((9 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_9]
  exact N12_Kvec_step_9
theorem orbit_val_11 : worldOrbit ((11 : Fin 12) : ℕ) = Kvec 11 := by
  have h : worldOrbit ((11 : Fin 12) : ℕ) =
      N12 (worldOrbit ((10 : Fin 12) : ℕ)) := rfl
  rw [h, orbit_val_10]
  exact N12_Kvec_step_10

theorem worldOrbit_val (n : Fin 12) : worldOrbit (n : ℕ) = Kvec n := by
  fin_cases n
  · exact orbit_val_0
  · exact orbit_val_1
  · exact orbit_val_2
  · exact orbit_val_3
  · exact orbit_val_4
  · exact orbit_val_5
  · exact orbit_val_6
  · exact orbit_val_7
  · exact orbit_val_8
  · exact orbit_val_9
  · exact orbit_val_10
  · exact orbit_val_11

/-! ## §4 The exact spanning certificate

Every cell basis vector is an explicit rational combination of the twelve
fold-orbit values. The coefficients are the exact Gauss-Jordan
certificate; each identity is kernel-checkable cell by cell. -/

/-- The cell basis vector `e_{(c,d)}`. -/
def eCell (c : Fin 4) (d : Fin 3) : WaveSignal12 :=
  fun s => if s = (c, d) then (1 : ℚ) else 0

/-- The certificate coefficients: `certRowOf s n` is the n-th coefficient
of the cell basis vector `e_s` in the Krylov table `Kvec 0 … Kvec 11`. -/
def certRowOf : TwelveCell → Fin 12 → ℚ :=
  fun s n =>
    if s = ((0 : Fin 4), (0 : Fin 3)) then (if n = 0 then (2817 / 88804 : ℚ) else if n = 1 then (-4151 / 44402 : ℚ) else if n = 2 then (-4307 / 355216 : ℚ) else if n = 3 then (41361 / 355216 : ℚ) else if n = 4 then (27141 / 355216 : ℚ) else if n = 5 then (-116661 / 710432 : ℚ) else if n = 6 then (27127 / 177608 : ℚ) else if n = 7 then (-77819 / 710432 : ℚ) else if n = 8 then (13489 / 177608 : ℚ) else if n = 9 then (-13191 / 355216 : ℚ) else if n = 10 then (667 / 44402 : ℚ) else if n = 11 then (-2519 / 710432 : ℚ) else 0)
    else if s = ((0 : Fin 4), (1 : Fin 3)) then (if n = 0 then (85987 / 88804 : ℚ) else if n = 1 then (4151 / 44402 : ℚ) else if n = 2 then (4307 / 355216 : ℚ) else if n = 3 then (-41361 / 355216 : ℚ) else if n = 4 then (-27141 / 355216 : ℚ) else if n = 5 then (116661 / 710432 : ℚ) else if n = 6 then (-27127 / 177608 : ℚ) else if n = 7 then (77819 / 710432 : ℚ) else if n = 8 then (-13489 / 177608 : ℚ) else if n = 9 then (13191 / 355216 : ℚ) else if n = 10 then (-667 / 44402 : ℚ) else if n = 11 then (2519 / 710432 : ℚ) else 0)
    else if s = ((0 : Fin 4), (2 : Fin 3)) then (if n = 0 then (-54987181629 / 17963384125 : ℚ) else if n = 1 then (72568024478 / 17963384125 : ℚ) else if n = 2 then (416372223563 / 71853536500 : ℚ) else if n = 3 then (-40959489149 / 14370707300 : ℚ) else if n = 4 then (-466599137711 / 71853536500 : ℚ) else if n = 5 then (270656071957 / 28741414600 : ℚ) else if n = 6 then (-138665140257 / 17963384125 : ℚ) else if n = 7 then (818730103567 / 143707073000 : ℚ) else if n = 8 then (-25014609233 / 7185353650 : ℚ) else if n = 9 then (23515519339 / 14370707300 : ℚ) else if n = 10 then (-21149886569 / 35926768250 : ℚ) else if n = 11 then (15310139403 / 143707073000 : ℚ) else 0)
    else if s = ((1 : Fin 4), (0 : Fin 3)) then (if n = 0 then (235344355839 / 71853536500 : ℚ) else if n = 1 then (-140767238349 / 35926768250 : ℚ) else if n = 2 then (-1240041120433 / 287414146000 : ℚ) else if n = 3 then (66889112959 / 57482829200 : ℚ) else if n = 4 then (2037508112351 / 287414146000 : ℚ) else if n = 5 then (-1091847690587 / 114965658400 : ℚ) else if n = 6 then (1098072784249 / 143707073000 : ℚ) else if n = 7 then (-3179798397897 / 574828292000 : ℚ) else if n = 8 then (95880376103 / 28741414600 : ℚ) else if n = 9 then (-89110733049 / 57482829200 : ℚ) else if n = 10 then (9914430313 / 17963384125 : ℚ) else if n = 11 then (-57100925373 / 574828292000 : ℚ) else 0)
    else if s = ((1 : Fin 4), (1 : Fin 3)) then (if n = 0 then (-321340982133 / 71853536500 : ℚ) else if n = 1 then (289078573103 / 35926768250 : ℚ) else if n = 2 then (1972211392251 / 287414146000 : ℚ) else if n = 3 then (-222341135573 / 57482829200 : ℚ) else if n = 4 then (-2561034108797 / 287414146000 : ℚ) else if n = 5 then (1495609060489 / 114965658400 : ℚ) else if n = 6 then (-1534796826903 / 143707073000 : ℚ) else if n = 7 then (4537167712259 / 574828292000 : ℚ) else if n = 8 then (-139786417941 / 28741414600 : ℚ) else if n = 9 then (132586088003 / 57482829200 : ℚ) else if n = 10 then (-30218089597 / 35926768250 : ℚ) else if n = 11 then (88913498431 / 574828292000 : ℚ) else 0)
    else if s = ((1 : Fin 4), (2 : Fin 3)) then (if n = 0 then (-51024823439 / 35926768250 : ℚ) else if n = 1 then (10910763949 / 17963384125 : ℚ) else if n = 2 then (414443825633 / 143707073000 : ℚ) else if n = 3 then (-40492105359 / 28741414600 : ℚ) else if n = 4 then (-245488006751 / 143707073000 : ℚ) else if n = 5 then (149024610587 / 57482829200 : ℚ) else if n = 6 then (-162809094349 / 71853536500 : ℚ) else if n = 7 then (494020382697 / 287414146000 : ℚ) else if n = 8 then (-14993410403 / 14370707300 : ℚ) else if n = 9 then (14133837449 / 28741414600 : ℚ) else if n = 10 then (-3050237276 / 17963384125 : ℚ) else if n = 11 then (8210532573 / 287414146000 : ℚ) else 0)
    else if s = ((2 : Fin 4), (0 : Fin 3)) then (if n = 0 then (-288498851841 / 71853536500 : ℚ) else if n = 1 then (282629668531 / 35926768250 : ℚ) else if n = 2 then (1961849820527 / 287414146000 : ℚ) else if n = 3 then (-286308061921 / 57482829200 : ℚ) else if n = 4 then (-2106849859769 / 287414146000 : ℚ) else if n = 5 then (1350441310853 / 114965658400 : ℚ) else if n = 6 then (-1402410600131 / 143707073000 : ℚ) else if n = 7 then (4230376082743 / 574828292000 : ℚ) else if n = 8 then (-132535781457 / 28741414600 : ℚ) else if n = 9 then (126875469031 / 57482829200 : ℚ) else if n = 10 then (-29411688119 / 35926768250 : ℚ) else if n = 11 then (87994700387 / 574828292000 : ℚ) else 0)
    else if s = ((2 : Fin 4), (1 : Fin 3)) then (if n = 0 then (-18484938474 / 17963384125 : ℚ) else if n = 1 then (70955248768 / 17963384125 : ℚ) else if n = 2 then (69025336639 / 35926768250 : ℚ) else if n = 3 then (-9026620947 / 7185353650 : ℚ) else if n = 4 then (-75284274829 / 17963384125 : ℚ) else if n = 5 then (86187575371 / 14370707300 : ℚ) else if n = 6 then (-173041802409 / 35926768250 : ℚ) else if n = 7 then (253224684001 / 71853536500 : ℚ) else if n = 8 then (-7759511424 / 3592676825 : ℚ) else if n = 9 then (7329945467 / 7185353650 : ℚ) else if n = 10 then (-13596395239 / 35926768250 : ℚ) else if n = 11 then (5120015909 / 71853536500 : ℚ) else 0)
    else if s = ((2 : Fin 4), (2 : Fin 3)) then (if n = 0 then (51815885871 / 71853536500 : ℚ) else if n = 1 then (-96081019261 / 35926768250 : ℚ) else if n = 2 then (-858038351937 / 287414146000 : ℚ) else if n = 3 then (133696870351 / 57482829200 : ℚ) else if n = 4 then (598190063039 / 287414146000 : ℚ) else if n = 5 then (-450500330043 / 114965658400 : ℚ) else if n = 6 then (481499971361 / 143707073000 : ℚ) else if n = 7 then (-1462486375433 / 574828292000 : ℚ) else if n = 8 then (46993605767 / 28741414600 : ℚ) else if n = 9 then (-45387163161 / 57482829200 : ℚ) else if n = 10 then (5380263132 / 17963384125 : ℚ) else if n = 11 then (-33605757597 / 574828292000 : ℚ) else 0)
    else if s = ((3 : Fin 4), (0 : Fin 3)) then (if n = 0 then (166017736617 / 71853536500 : ℚ) else if n = 1 then (-178262080147 / 35926768250 : ℚ) else if n = 2 then (-1413167004999 / 287414146000 : ℚ) else if n = 3 then (239714383577 / 57482829200 : ℚ) else if n = 4 then (1103938403953 / 287414146000 : ℚ) else if n = 5 then (-823196332861 / 114965658400 : ℚ) else if n = 6 then (872543813347 / 143707073000 : ℚ) else if n = 7 then (-2666085924991 / 574828292000 : ℚ) else if n = 8 then (85001878409 / 28741414600 : ℚ) else if n = 9 then (-82030112447 / 57482829200 : ℚ) else if n = 10 then (19304859153 / 35926768250 : ℚ) else if n = 11 then (-58949539819 / 574828292000 : ℚ) else 0)
    else if s = ((3 : Fin 4), (1 : Fin 3)) then (if n = 0 then (239420727589 / 71853536500 : ℚ) else if n = 1 then (-182688004599 / 35926768250 : ℚ) else if n = 2 then (-1246528684683 / 287414146000 : ℚ) else if n = 3 then (78828885109 / 57482829200 : ℚ) else if n = 4 then (2077088889101 / 287414146000 : ℚ) else if n = 5 then (-1125457772137 / 114965658400 : ℚ) else if n = 6 then (1137148666999 / 143707073000 : ℚ) else if n = 7 then (-3291744078147 / 574828292000 : ℚ) else if n = 8 then (99763852453 / 28741414600 : ℚ) else if n = 9 then (-92897761699 / 57482829200 : ℚ) else if n = 10 then (20787673751 / 35926768250 : ℚ) else if n = 11 then (-60695058623 / 574828292000 : ℚ) else 0)
    else if s = ((3 : Fin 4), (2 : Fin 3)) then (if n = 0 then (-2221 / 88804 : ℚ) else if n = 1 then (3257 / 44402 : ℚ) else if n = 2 then (3711 / 355216 : ℚ) else if n = 3 then (-32421 / 355216 : ℚ) else if n = 4 then (-21777 / 355216 : ℚ) else if n = 5 then (91033 / 710432 : ℚ) else if n = 6 then (-21167 / 177608 : ℚ) else if n = 7 then (60535 / 710432 : ℚ) else if n = 8 then (-10509 / 177608 : ℚ) else if n = 9 then (10211 / 355216 : ℚ) else if n = 10 then (-259 / 22201 : ℚ) else if n = 11 then (1923 / 710432 : ℚ) else 0)
    else 0

theorem eCell_eq_cert (s : TwelveCell) :
    eCell s.1 s.2 = (certRowOf s 0) • worldOrbit ((0 : Fin 12) : ℕ) + (certRowOf s 1) • worldOrbit ((1 : Fin 12) : ℕ) + (certRowOf s 2) • worldOrbit ((2 : Fin 12) : ℕ) + (certRowOf s 3) • worldOrbit ((3 : Fin 12) : ℕ) + (certRowOf s 4) • worldOrbit ((4 : Fin 12) : ℕ) + (certRowOf s 5) • worldOrbit ((5 : Fin 12) : ℕ) + (certRowOf s 6) • worldOrbit ((6 : Fin 12) : ℕ) + (certRowOf s 7) • worldOrbit ((7 : Fin 12) : ℕ) + (certRowOf s 8) • worldOrbit ((8 : Fin 12) : ℕ) + (certRowOf s 9) • worldOrbit ((9 : Fin 12) : ℕ) + (certRowOf s 10) • worldOrbit ((10 : Fin 12) : ℕ) + (certRowOf s 11) • worldOrbit ((11 : Fin 12) : ℕ) := by
  rw [worldOrbit_val 0, worldOrbit_val 1, worldOrbit_val 2, worldOrbit_val 3, worldOrbit_val 4, worldOrbit_val 5, worldOrbit_val 6, worldOrbit_val 7, worldOrbit_val 8, worldOrbit_val 9, worldOrbit_val 10, worldOrbit_val 11]
  funext t
  rcases s with ⟨cs, ds⟩
  rcases t with ⟨ct, dt⟩
  fin_cases cs <;> fin_cases ds <;> fin_cases ct <;> fin_cases dt <;>
    simp [eCell, certRowOf, Kvec, seed12] <;>
    norm_num

/-! ## §5 THE SPANNING LAW -/

theorem eCell_mem_span (s : TwelveCell) :
    eCell s.1 s.2 ∈ Submodule.span ℚ (Set.range worldOrbit) := by
  rw [eCell_eq_cert s]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))

theorem wave_decompose (u : WaveSignal12) :
    u = u ((0 : Fin 4), (0 : Fin 3)) • eCell (0 : Fin 4) (0 : Fin 3) + u ((0 : Fin 4), (1 : Fin 3)) • eCell (0 : Fin 4) (1 : Fin 3) + u ((0 : Fin 4), (2 : Fin 3)) • eCell (0 : Fin 4) (2 : Fin 3) + u ((1 : Fin 4), (0 : Fin 3)) • eCell (1 : Fin 4) (0 : Fin 3) + u ((1 : Fin 4), (1 : Fin 3)) • eCell (1 : Fin 4) (1 : Fin 3) + u ((1 : Fin 4), (2 : Fin 3)) • eCell (1 : Fin 4) (2 : Fin 3) + u ((2 : Fin 4), (0 : Fin 3)) • eCell (2 : Fin 4) (0 : Fin 3) + u ((2 : Fin 4), (1 : Fin 3)) • eCell (2 : Fin 4) (1 : Fin 3) + u ((2 : Fin 4), (2 : Fin 3)) • eCell (2 : Fin 4) (2 : Fin 3) + u ((3 : Fin 4), (0 : Fin 3)) • eCell (3 : Fin 4) (0 : Fin 3) + u ((3 : Fin 4), (1 : Fin 3)) • eCell (3 : Fin 4) (1 : Fin 3) + u ((3 : Fin 4), (2 : Fin 3)) • eCell (3 : Fin 4) (2 : Fin 3) := by
  funext s
  rcases s with ⟨c, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [eCell, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add]

/-- **THE SPANNING LAW.** The rational span of the full fold orbit of the
owner's seed is the entire twelve-cell world. -/
theorem span_range_worldOrbit_eq_top :
    Submodule.span ℚ (Set.range worldOrbit) = ⊤ := by
  apply top_unique
  intro u _
  rw [wave_decompose u]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (eCell_mem_span ((0 : Fin 4), (0 : Fin 3)))) (Submodule.smul_mem _ _ (eCell_mem_span ((0 : Fin 4), (1 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((0 : Fin 4), (2 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((1 : Fin 4), (0 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((1 : Fin 4), (1 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((1 : Fin 4), (2 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((2 : Fin 4), (0 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((2 : Fin 4), (1 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((2 : Fin 4), (2 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((3 : Fin 4), (0 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((3 : Fin 4), (1 : Fin 3))))) (Submodule.smul_mem _ _ (eCell_mem_span ((3 : Fin 4), (2 : Fin 3))))

/-! ## §6 THE GST HYPOTHESIS IS COMPLETE FOR THE OWNER'S TWELVE-CELL WORLD -/

/-- The owner's designated hypothesis data: the world fold, the full world
fiber (the maximal designated fiber — any smaller fiber would be a weaker
statement), the genuine native seed. -/
def worldData : GSTHypothesisData WaveSignal12 WaveSignal12 where
  fold := worldFold
  hodgeFiber := ⊤
  seed := seed12

theorem orbitClassSet_world_eq :
    orbitClassSet worldFold seed12 = Set.range worldOrbit := rfl

/-- **THE GST HYPOTHESIS, PROVED FOR THE OWNER'S WORLD.** The designated
rational Hodge fiber (the entire twelve-cell world) is spanned by the
fold-orbit classes of the native seed. -/
theorem gst_hypothesis_complete_world :
    GSTHypothesisComplete worldData := by
  show (⊤ : Submodule ℚ WaveSignal12) ≤
    Submodule.span ℚ (orbitClassSet worldFold seed12)
  rw [orbitClassSet_world_eq, span_range_worldOrbit_eq_top]

/-- **THE LANDING FOR THE OWNER'S WORLD** — a formality on this face (the
world cycle-class map is the identity, so `z := β` witnesses it). Recorded
to instantiate the general reduction `gst_hypothesis_landing`, which is
non-trivial precisely for folds whose cycle-class map is not surjective.
The content of this module is `span_range_worldOrbit_eq_top`. -/
theorem the_world_landing :
    ∀ β : WaveSignal12, β ∈ (⊤ : Submodule ℚ WaveSignal12) →
      ∃ z : WaveSignal12, worldFold.cycleClass z = β := by
  exact gst_hypothesis_landing worldData gst_hypothesis_complete_world

/-- **THE COMPLETE GST HYPOTHESIS FOR THE OWNER'S TWELVE-CELL WORLD:** the
spanning law, the landing, and the owner's FULL twelve-cell fold-law
package (U^5 = I, J^2 = -I, J U = U J, the certified curvature value 2 at
the maximum fixed cell, the navigation-charge defect scaling and its fixed
value 2b) — all in one statement. -/
theorem the_GST_hypothesis_is_complete_for_the_owners_twelve_cell_world :
    GSTHypothesisComplete worldData ∧
    (∀ β : WaveSignal12, β ∈ (⊤ : Submodule ℚ WaveSignal12) →
      ∃ z : WaveSignal12, worldFold.cycleClass z = β) ∧
    (∀ u : WaveSignal12,
        U12 (U12 (U12 (U12 (U12 u)))) = u) ∧
    (∀ u : WaveSignal12, J12 (J12 u) = -u) ∧
    (∀ u : WaveSignal12, J12 (U12 u) = U12 (J12 u)) ∧
    (J12 (M12 ownerSource seed12) - M12 ownerSource (J12 seed12)) maxCell = 2 ∧
    (∀ b : ℚ, ∀ u : WaveSignal12,
        J12 (F12 ownerSource b u) - F12 ownerSource b (J12 u) =
          b • (J12 (M12 ownerSource u) - M12 ownerSource (J12 u))) ∧
    (∀ b : ℚ,
        (J12 (F12 ownerSource b seed12) - F12 ownerSource b (J12 seed12)) maxCell =
          2 * b) :=
  ⟨gst_hypothesis_complete_world, the_world_landing,
    (the_twelve_cell_fold_law_package ownerSource ownerSource_null
      ownerSource_max).1,
    (the_twelve_cell_fold_law_package ownerSource ownerSource_null
      ownerSource_max).2.1,
    (the_twelve_cell_fold_law_package ownerSource ownerSource_null
      ownerSource_max).2.2.1,
    (the_twelve_cell_fold_law_package ownerSource ownerSource_null
      ownerSource_max).2.2.2.1,
    (the_twelve_cell_fold_law_package ownerSource ownerSource_null
      ownerSource_max).2.2.2.2.1,
    (the_twelve_cell_fold_law_package ownerSource ownerSource_null
      ownerSource_max).2.2.2.2.2⟩

/-! ## Receipts -/

#check ownerSource
#check N12
#check worldFold
#check worldOrbit
#check Kvec
#check span_range_worldOrbit_eq_top
#check worldData
#check gst_hypothesis_complete_world
#check the_world_landing
#check the_GST_hypothesis_is_complete_for_the_owners_twelve_cell_world

#print axioms span_range_worldOrbit_eq_top
#print axioms gst_hypothesis_complete_world
#print axioms the_world_landing
#print axioms the_GST_hypothesis_is_complete_for_the_owners_twelve_cell_world

end GSTHypothesisSpanning
