/-
Copyright (c) 2026. The HC-Proof owner's GST hypothesis program.
-/
import Mathlib
import HCUniverse2.GSTHypothesisSpanningProof
import HCUniverse2.GSTOriginalXWaveChowMatrixCompiler

/-!
# THE GST HYPOTHESIS SPANNING — THE COMPILER FACE

The same spanning certificate, transported through the repository's rational
wave compiler (`GSTOriginalXWaveChowMatrixCompiler`) to **every**
`IntersectionChowFrame (Fin 12) A B`. The owner's twelve-cell fold
`F₁ = U + J + M` — realized as the exact wave matrix `Twave` (proved to BE
the owner's fold: `Twave_bridge`) — acts natively and Betti-side on any
certified frame, and the fold orbit of the designated native seed
`Z₀ = source 0 + source 1` spans the **entire source-class space**
`span {cl (source j)}`.

## Theorems

* `span_orbitClasses_eq_sourceClassSpan`: the span of the fold-orbit classes
  equals the source-class span — on EVERY frame. This is the non-trivial
  content of this module.
* `gst_hypothesis_complete_compiler`: `GSTHypothesisComplete` holds for the
  compiler data — the designated fiber (the source-class span) is spanned by
  the fold-orbit classes of the seed.
* `the_compiler_landing`: a formality on this face (every source-class
  combination is `cl (phiNat c)` by linearity, so `z := phiNat c` witnesses
  it); recorded to instantiate the general reduction `gst_hypothesis_landing`.

The coordinate certificate in `Fin 12 → ℚ` is the SAME Gauss-Jordan
elimination as the owner's world (face 1); the transfer is exact linear
algebra (`Submodule.map_span`, `LinearMap.range_eq_map`). All cell/coordinate
values are kernel-checkable by `decide`/`norm_num`; the GitHub CI lane owns
the kernel check.

## Scope (audit-accurate)

The fiber here is the frame's source-class span — the algebraic source sector
the compiler's companion geometry constructs (for original X with twelve
independent divisor-Lefschetz source cycles). It is NOT claimed to be the
full rational Hodge fiber W_p(X) of an arbitrary X; the `AGENTS.md`
withdrawal rule remains binding.
-/

noncomputable section
namespace GSTHypothesisSpanningCompilerFace

open GSTHypothesisComplete
open GSTHypothesisSpanning
open GSTOriginalXWaveChowMatrixCompiler
open GSTOriginalXDivisorCurveCyclicChowFold
universe u v

set_option maxHeartbeats 30000000
set_option maxRecDepth 400000

/-! ## §1 The owner's fold as an exact wave matrix -/

/-- The owner's full combined fold `F₁ = U + J + M` in carry-major cell
coordinates: column `j` is `F₁` applied to the j-th cell basis vector. -/
def Twave : Matrix (Fin 12) (Fin 12) ℚ :=
  fun i j =>
    if i = (0 : Fin 12) then (if j = (0 : Fin 12) then (1 : ℚ) else if j = (11 : Fin 12) then (1 : ℚ) else 0)
    else if i = (1 : Fin 12) then (if j = (4 : Fin 12) then (1 : ℚ) else if j = (10 : Fin 12) then (1 : ℚ) else 0)
    else if i = (2 : Fin 12) then (if j = (8 : Fin 12) then (1 : ℚ) else if j = (9 : Fin 12) then (-1 : ℚ) else 0)
    else if i = (3 : Fin 12) then (if j = (1 : Fin 12) then (1 : ℚ) else if j = (8 : Fin 12) then (1 : ℚ) else 0)
    else if i = (4 : Fin 12) then (if j = (4 : Fin 12) then (1 : ℚ) else if j = (5 : Fin 12) then (1 : ℚ) else if j = (7 : Fin 12) then (1 : ℚ) else 0)
    else if i = (5 : Fin 12) then (if j = (6 : Fin 12) then (1 : ℚ) else if j = (9 : Fin 12) then (1 : ℚ) else 0)
    else if i = (6 : Fin 12) then (if j = (2 : Fin 12) then (1 : ℚ) else if j = (5 : Fin 12) then (-1 : ℚ) else 0)
    else if i = (7 : Fin 12) then (if j = (4 : Fin 12) then (-1 : ℚ) else if j = (6 : Fin 12) then (1 : ℚ) else 0)
    else if i = (8 : Fin 12) then (if j = (3 : Fin 12) then (-1 : ℚ) else if j = (8 : Fin 12) then (1 : ℚ) else if j = (10 : Fin 12) then (1 : ℚ) else 0)
    else if i = (9 : Fin 12) then (if j = (2 : Fin 12) then (1 : ℚ) else if j = (3 : Fin 12) then (1 : ℚ) else 0)
    else if i = (10 : Fin 12) then (if j = (1 : Fin 12) then (-1 : ℚ) else if j = (7 : Fin 12) then (1 : ℚ) else 0)
    else if i = (11 : Fin 12) then (if j = (0 : Fin 12) then (-1 : ℚ) else if j = (11 : Fin 12) then (3 : ℚ) else 0)
    else 0

/-- **`Twave` IS the owner's fold**: entry `(i, j)` is the owner's full fold
of the j-th cell basis vector, evaluated at the i-th cell. -/
theorem Twave_bridge (i j : Fin 12) :
    Twave i j =
      N12 (eCell (⟨(j : ℕ) / 3, by have := j.isLt; omega⟩ : Fin 4)
          (⟨(j : ℕ) % 3, by have := j.isLt; omega⟩ : Fin 3))
        ((⟨(i : ℕ) / 3, by have := i.isLt; omega⟩ : Fin 4),
          (⟨(i : ℕ) % 3, by have := i.isLt; omega⟩ : Fin 3)) := by
  fin_cases i <;> fin_cases j <;>
    simp [Twave, N12_val, eCell, shuffleCell, mirrorCell, cmSign, ownerSource,
      GST2DMixedEmergence.surviveI, GST2DMixedEmergence.twoI,
      GST2DMixedEmergence.midDigit, GST2DMixedEmergence.finalMicroDigit,
      GST2DMixedEmergence.microOutput, GST2DMixedEmergence.highBit,
      GST2DMixedEmergence.lowBit] <;>
    norm_num

/-! ## §2 The coordinate certificate in `Fin 12 → ℚ` -/

/-- The coordinate seed: the two leading cells of the owner's seed. -/
def coordSeed : Fin 12 → ℚ := fun i => if i = 0 ∨ i = 1 then 1 else 0

/-- The coordinate fold orbit: `C 0` is the seed, `C (n+1) = Twave * C n`. -/
def C : ℕ → (Fin 12 → ℚ)
  | 0 => coordSeed
  | n + 1 => Twave.mulVec (C n)

theorem C_zero : C 0 = coordSeed := rfl
theorem C_succ (n : ℕ) : C (n + 1) = Twave.mulVec (C n) := rfl

/-- The coordinate Krylov table. -/
def Cvec : Fin 12 → (Fin 12 → ℚ) :=
  fun n i =>
    if n = (0 : Fin 12) then (if i = (0 : Fin 12) then (1 : ℚ) else if i = (1 : Fin 12) then (1 : ℚ) else 0)
    else if n = (1 : Fin 12) then (if i = (0 : Fin 12) then (1 : ℚ) else if i = (3 : Fin 12) then (1 : ℚ) else if i = (10 : Fin 12) then (-1 : ℚ) else if i = (11 : Fin 12) then (-1 : ℚ) else 0)
    else if n = (2 : Fin 12) then (if i = (1 : Fin 12) then (-1 : ℚ) else if i = (8 : Fin 12) then (-2 : ℚ) else if i = (9 : Fin 12) then (1 : ℚ) else if i = (11 : Fin 12) then (-4 : ℚ) else 0)
    else if n = (3 : Fin 12) then (if i = (0 : Fin 12) then (-4 : ℚ) else if i = (2 : Fin 12) then (-3 : ℚ) else if i = (3 : Fin 12) then (-3 : ℚ) else if i = (5 : Fin 12) then (1 : ℚ) else if i = (8 : Fin 12) then (-2 : ℚ) else if i = (10 : Fin 12) then (1 : ℚ) else if i = (11 : Fin 12) then (-12 : ℚ) else 0)
    else if n = (4 : Fin 12) then (if i = (0 : Fin 12) then (-16 : ℚ) else if i = (1 : Fin 12) then (1 : ℚ) else if i = (2 : Fin 12) then (-2 : ℚ) else if i = (3 : Fin 12) then (-2 : ℚ) else if i = (4 : Fin 12) then (1 : ℚ) else if i = (6 : Fin 12) then (-4 : ℚ) else if i = (8 : Fin 12) then (2 : ℚ) else if i = (9 : Fin 12) then (-6 : ℚ) else if i = (11 : Fin 12) then (-32 : ℚ) else 0)
    else if n = (5 : Fin 12) then (if i = (0 : Fin 12) then (-48 : ℚ) else if i = (1 : Fin 12) then (1 : ℚ) else if i = (2 : Fin 12) then (8 : ℚ) else if i = (3 : Fin 12) then (3 : ℚ) else if i = (4 : Fin 12) then (1 : ℚ) else if i = (5 : Fin 12) then (-10 : ℚ) else if i = (6 : Fin 12) then (-2 : ℚ) else if i = (7 : Fin 12) then (-5 : ℚ) else if i = (8 : Fin 12) then (4 : ℚ) else if i = (9 : Fin 12) then (-4 : ℚ) else if i = (10 : Fin 12) then (-1 : ℚ) else if i = (11 : Fin 12) then (-80 : ℚ) else 0)
    else if n = (6 : Fin 12) then (if i = (0 : Fin 12) then (-128 : ℚ) else if i = (2 : Fin 12) then (8 : ℚ) else if i = (3 : Fin 12) then (5 : ℚ) else if i = (4 : Fin 12) then (-14 : ℚ) else if i = (5 : Fin 12) then (-6 : ℚ) else if i = (6 : Fin 12) then (18 : ℚ) else if i = (7 : Fin 12) then (-3 : ℚ) else if i = (9 : Fin 12) then (11 : ℚ) else if i = (10 : Fin 12) then (-6 : ℚ) else if i = (11 : Fin 12) then (-192 : ℚ) else 0)
    else if n = (7 : Fin 12) then (if i = (0 : Fin 12) then (-320 : ℚ) else if i = (1 : Fin 12) then (-20 : ℚ) else if i = (2 : Fin 12) then (-11 : ℚ) else if i = (4 : Fin 12) then (-23 : ℚ) else if i = (5 : Fin 12) then (29 : ℚ) else if i = (6 : Fin 12) then (14 : ℚ) else if i = (7 : Fin 12) then (32 : ℚ) else if i = (8 : Fin 12) then (-11 : ℚ) else if i = (9 : Fin 12) then (13 : ℚ) else if i = (10 : Fin 12) then (-3 : ℚ) else if i = (11 : Fin 12) then (-448 : ℚ) else 0)
    else if n = (8 : Fin 12) then (if i = (0 : Fin 12) then (-768 : ℚ) else if i = (1 : Fin 12) then (-26 : ℚ) else if i = (2 : Fin 12) then (-24 : ℚ) else if i = (3 : Fin 12) then (-31 : ℚ) else if i = (4 : Fin 12) then (38 : ℚ) else if i = (5 : Fin 12) then (27 : ℚ) else if i = (6 : Fin 12) then (-40 : ℚ) else if i = (7 : Fin 12) then (37 : ℚ) else if i = (8 : Fin 12) then (-14 : ℚ) else if i = (9 : Fin 12) then (-11 : ℚ) else if i = (10 : Fin 12) then (52 : ℚ) else if i = (11 : Fin 12) then (-1024 : ℚ) else 0)
    else if n = (9 : Fin 12) then (if i = (0 : Fin 12) then (-1792 : ℚ) else if i = (1 : Fin 12) then (90 : ℚ) else if i = (2 : Fin 12) then (-3 : ℚ) else if i = (3 : Fin 12) then (-40 : ℚ) else if i = (4 : Fin 12) then (102 : ℚ) else if i = (5 : Fin 12) then (-51 : ℚ) else if i = (6 : Fin 12) then (-51 : ℚ) else if i = (7 : Fin 12) then (-78 : ℚ) else if i = (8 : Fin 12) then (69 : ℚ) else if i = (9 : Fin 12) then (-55 : ℚ) else if i = (10 : Fin 12) then (63 : ℚ) else if i = (11 : Fin 12) then (-2304 : ℚ) else 0)
    else if n = (10 : Fin 12) then (if i = (0 : Fin 12) then (-4096 : ℚ) else if i = (1 : Fin 12) then (165 : ℚ) else if i = (2 : Fin 12) then (124 : ℚ) else if i = (3 : Fin 12) then (159 : ℚ) else if i = (4 : Fin 12) then (-27 : ℚ) else if i = (5 : Fin 12) then (-106 : ℚ) else if i = (6 : Fin 12) then (48 : ℚ) else if i = (7 : Fin 12) then (-153 : ℚ) else if i = (8 : Fin 12) then (172 : ℚ) else if i = (9 : Fin 12) then (-43 : ℚ) else if i = (10 : Fin 12) then (-168 : ℚ) else if i = (11 : Fin 12) then (-5120 : ℚ) else 0)
    else if n = (11 : Fin 12) then (if i = (0 : Fin 12) then (-9216 : ℚ) else if i = (1 : Fin 12) then (-195 : ℚ) else if i = (2 : Fin 12) then (215 : ℚ) else if i = (3 : Fin 12) then (337 : ℚ) else if i = (4 : Fin 12) then (-286 : ℚ) else if i = (5 : Fin 12) then (5 : ℚ) else if i = (6 : Fin 12) then (230 : ℚ) else if i = (7 : Fin 12) then (75 : ℚ) else if i = (8 : Fin 12) then (-155 : ℚ) else if i = (9 : Fin 12) then (283 : ℚ) else if i = (10 : Fin 12) then (-318 : ℚ) else if i = (11 : Fin 12) then (-11264 : ℚ) else 0)
    else 0

theorem coordSeed_eq_Cvec0 : coordSeed = Cvec 0 := by
  funext i; fin_cases i <;> simp [coordSeed, Cvec] <;> norm_num

/-! The fold steps of the coordinate table: one `mulVec` each — the sum is
unrolled by `Fin.sum_univ_castSucc` and evaluated cellwise. -/
theorem C_step_0 : ∀ i, (Twave.mulVec (Cvec (0 : Fin 12))) i = Cvec (1 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_1 : ∀ i, (Twave.mulVec (Cvec (1 : Fin 12))) i = Cvec (2 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_2 : ∀ i, (Twave.mulVec (Cvec (2 : Fin 12))) i = Cvec (3 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_3 : ∀ i, (Twave.mulVec (Cvec (3 : Fin 12))) i = Cvec (4 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_4 : ∀ i, (Twave.mulVec (Cvec (4 : Fin 12))) i = Cvec (5 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_5 : ∀ i, (Twave.mulVec (Cvec (5 : Fin 12))) i = Cvec (6 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_6 : ∀ i, (Twave.mulVec (Cvec (6 : Fin 12))) i = Cvec (7 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_7 : ∀ i, (Twave.mulVec (Cvec (7 : Fin 12))) i = Cvec (8 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_8 : ∀ i, (Twave.mulVec (Cvec (8 : Fin 12))) i = Cvec (9 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_9 : ∀ i, (Twave.mulVec (Cvec (9 : Fin 12))) i = Cvec (10 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num
theorem C_step_10 : ∀ i, (Twave.mulVec (Cvec (10 : Fin 12))) i = Cvec (11 : Fin 12) i := by
  intro i; fin_cases i <;>
    simp [Twave, Cvec, coordSeed, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, mul_comm] <;>
    norm_num

theorem C_val_0 : C ((0 : Fin 12) : ℕ) = Cvec 0 := by
  show C 0 = Cvec 0
  rw [C_zero, coordSeed_eq_Cvec0]

theorem C_val_1 : C ((1 : Fin 12) : ℕ) = Cvec (1 : Fin 12) := by
  have h : C ((1 : Fin 12) : ℕ) = Twave.mulVec (C ((0 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_0]
  funext i
  exact C_step_0 i
theorem C_val_2 : C ((2 : Fin 12) : ℕ) = Cvec (2 : Fin 12) := by
  have h : C ((2 : Fin 12) : ℕ) = Twave.mulVec (C ((1 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_1]
  funext i
  exact C_step_1 i
theorem C_val_3 : C ((3 : Fin 12) : ℕ) = Cvec (3 : Fin 12) := by
  have h : C ((3 : Fin 12) : ℕ) = Twave.mulVec (C ((2 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_2]
  funext i
  exact C_step_2 i
theorem C_val_4 : C ((4 : Fin 12) : ℕ) = Cvec (4 : Fin 12) := by
  have h : C ((4 : Fin 12) : ℕ) = Twave.mulVec (C ((3 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_3]
  funext i
  exact C_step_3 i
theorem C_val_5 : C ((5 : Fin 12) : ℕ) = Cvec (5 : Fin 12) := by
  have h : C ((5 : Fin 12) : ℕ) = Twave.mulVec (C ((4 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_4]
  funext i
  exact C_step_4 i
theorem C_val_6 : C ((6 : Fin 12) : ℕ) = Cvec (6 : Fin 12) := by
  have h : C ((6 : Fin 12) : ℕ) = Twave.mulVec (C ((5 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_5]
  funext i
  exact C_step_5 i
theorem C_val_7 : C ((7 : Fin 12) : ℕ) = Cvec (7 : Fin 12) := by
  have h : C ((7 : Fin 12) : ℕ) = Twave.mulVec (C ((6 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_6]
  funext i
  exact C_step_6 i
theorem C_val_8 : C ((8 : Fin 12) : ℕ) = Cvec (8 : Fin 12) := by
  have h : C ((8 : Fin 12) : ℕ) = Twave.mulVec (C ((7 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_7]
  funext i
  exact C_step_7 i
theorem C_val_9 : C ((9 : Fin 12) : ℕ) = Cvec (9 : Fin 12) := by
  have h : C ((9 : Fin 12) : ℕ) = Twave.mulVec (C ((8 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_8]
  funext i
  exact C_step_8 i
theorem C_val_10 : C ((10 : Fin 12) : ℕ) = Cvec (10 : Fin 12) := by
  have h : C ((10 : Fin 12) : ℕ) = Twave.mulVec (C ((9 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_9]
  funext i
  exact C_step_9 i
theorem C_val_11 : C ((11 : Fin 12) : ℕ) = Cvec (11 : Fin 12) := by
  have h : C ((11 : Fin 12) : ℕ) = Twave.mulVec (C ((10 : Fin 12) : ℕ)) := rfl
  rw [h, C_val_10]
  funext i
  exact C_step_10 i

/-- The coordinate cell basis vector. -/
def eIdx (i : Fin 12) : Fin 12 → ℚ := fun j => if j = i then 1 else 0

/-- The certificate coefficients (the same Gauss-Jordan certificate,
coordinate-indexed). -/
def certRow : Fin 12 → Fin 12 → ℚ :=
  fun s n =>
    if s = (0 : Fin 12) then (if n = (0 : Fin 12) then (2817 / 88804 : ℚ) else if n = (1 : Fin 12) then (-4151 / 44402 : ℚ) else if n = (2 : Fin 12) then (-4307 / 355216 : ℚ) else if n = (3 : Fin 12) then (41361 / 355216 : ℚ) else if n = (4 : Fin 12) then (27141 / 355216 : ℚ) else if n = (5 : Fin 12) then (-116661 / 710432 : ℚ) else if n = (6 : Fin 12) then (27127 / 177608 : ℚ) else if n = (7 : Fin 12) then (-77819 / 710432 : ℚ) else if n = (8 : Fin 12) then (13489 / 177608 : ℚ) else if n = (9 : Fin 12) then (-13191 / 355216 : ℚ) else if n = (10 : Fin 12) then (667 / 44402 : ℚ) else if n = (11 : Fin 12) then (-2519 / 710432 : ℚ) else 0)
    else if s = (1 : Fin 12) then (if n = (0 : Fin 12) then (85987 / 88804 : ℚ) else if n = (1 : Fin 12) then (4151 / 44402 : ℚ) else if n = (2 : Fin 12) then (4307 / 355216 : ℚ) else if n = (3 : Fin 12) then (-41361 / 355216 : ℚ) else if n = (4 : Fin 12) then (-27141 / 355216 : ℚ) else if n = (5 : Fin 12) then (116661 / 710432 : ℚ) else if n = (6 : Fin 12) then (-27127 / 177608 : ℚ) else if n = (7 : Fin 12) then (77819 / 710432 : ℚ) else if n = (8 : Fin 12) then (-13489 / 177608 : ℚ) else if n = (9 : Fin 12) then (13191 / 355216 : ℚ) else if n = (10 : Fin 12) then (-667 / 44402 : ℚ) else if n = (11 : Fin 12) then (2519 / 710432 : ℚ) else 0)
    else if s = (2 : Fin 12) then (if n = (0 : Fin 12) then (-54987181629 / 17963384125 : ℚ) else if n = (1 : Fin 12) then (72568024478 / 17963384125 : ℚ) else if n = (2 : Fin 12) then (416372223563 / 71853536500 : ℚ) else if n = (3 : Fin 12) then (-40959489149 / 14370707300 : ℚ) else if n = (4 : Fin 12) then (-466599137711 / 71853536500 : ℚ) else if n = (5 : Fin 12) then (270656071957 / 28741414600 : ℚ) else if n = (6 : Fin 12) then (-138665140257 / 17963384125 : ℚ) else if n = (7 : Fin 12) then (818730103567 / 143707073000 : ℚ) else if n = (8 : Fin 12) then (-25014609233 / 7185353650 : ℚ) else if n = (9 : Fin 12) then (23515519339 / 14370707300 : ℚ) else if n = (10 : Fin 12) then (-21149886569 / 35926768250 : ℚ) else if n = (11 : Fin 12) then (15310139403 / 143707073000 : ℚ) else 0)
    else if s = (3 : Fin 12) then (if n = (0 : Fin 12) then (235344355839 / 71853536500 : ℚ) else if n = (1 : Fin 12) then (-140767238349 / 35926768250 : ℚ) else if n = (2 : Fin 12) then (-1240041120433 / 287414146000 : ℚ) else if n = (3 : Fin 12) then (66889112959 / 57482829200 : ℚ) else if n = (4 : Fin 12) then (2037508112351 / 287414146000 : ℚ) else if n = (5 : Fin 12) then (-1091847690587 / 114965658400 : ℚ) else if n = (6 : Fin 12) then (1098072784249 / 143707073000 : ℚ) else if n = (7 : Fin 12) then (-3179798397897 / 574828292000 : ℚ) else if n = (8 : Fin 12) then (95880376103 / 28741414600 : ℚ) else if n = (9 : Fin 12) then (-89110733049 / 57482829200 : ℚ) else if n = (10 : Fin 12) then (9914430313 / 17963384125 : ℚ) else if n = (11 : Fin 12) then (-57100925373 / 574828292000 : ℚ) else 0)
    else if s = (4 : Fin 12) then (if n = (0 : Fin 12) then (-321340982133 / 71853536500 : ℚ) else if n = (1 : Fin 12) then (289078573103 / 35926768250 : ℚ) else if n = (2 : Fin 12) then (1972211392251 / 287414146000 : ℚ) else if n = (3 : Fin 12) then (-222341135573 / 57482829200 : ℚ) else if n = (4 : Fin 12) then (-2561034108797 / 287414146000 : ℚ) else if n = (5 : Fin 12) then (1495609060489 / 114965658400 : ℚ) else if n = (6 : Fin 12) then (-1534796826903 / 143707073000 : ℚ) else if n = (7 : Fin 12) then (4537167712259 / 574828292000 : ℚ) else if n = (8 : Fin 12) then (-139786417941 / 28741414600 : ℚ) else if n = (9 : Fin 12) then (132586088003 / 57482829200 : ℚ) else if n = (10 : Fin 12) then (-30218089597 / 35926768250 : ℚ) else if n = (11 : Fin 12) then (88913498431 / 574828292000 : ℚ) else 0)
    else if s = (5 : Fin 12) then (if n = (0 : Fin 12) then (-51024823439 / 35926768250 : ℚ) else if n = (1 : Fin 12) then (10910763949 / 17963384125 : ℚ) else if n = (2 : Fin 12) then (414443825633 / 143707073000 : ℚ) else if n = (3 : Fin 12) then (-40492105359 / 28741414600 : ℚ) else if n = (4 : Fin 12) then (-245488006751 / 143707073000 : ℚ) else if n = (5 : Fin 12) then (149024610587 / 57482829200 : ℚ) else if n = (6 : Fin 12) then (-162809094349 / 71853536500 : ℚ) else if n = (7 : Fin 12) then (494020382697 / 287414146000 : ℚ) else if n = (8 : Fin 12) then (-14993410403 / 14370707300 : ℚ) else if n = (9 : Fin 12) then (14133837449 / 28741414600 : ℚ) else if n = (10 : Fin 12) then (-3050237276 / 17963384125 : ℚ) else if n = (11 : Fin 12) then (8210532573 / 287414146000 : ℚ) else 0)
    else if s = (6 : Fin 12) then (if n = (0 : Fin 12) then (-288498851841 / 71853536500 : ℚ) else if n = (1 : Fin 12) then (282629668531 / 35926768250 : ℚ) else if n = (2 : Fin 12) then (1961849820527 / 287414146000 : ℚ) else if n = (3 : Fin 12) then (-286308061921 / 57482829200 : ℚ) else if n = (4 : Fin 12) then (-2106849859769 / 287414146000 : ℚ) else if n = (5 : Fin 12) then (1350441310853 / 114965658400 : ℚ) else if n = (6 : Fin 12) then (-1402410600131 / 143707073000 : ℚ) else if n = (7 : Fin 12) then (4230376082743 / 574828292000 : ℚ) else if n = (8 : Fin 12) then (-132535781457 / 28741414600 : ℚ) else if n = (9 : Fin 12) then (126875469031 / 57482829200 : ℚ) else if n = (10 : Fin 12) then (-29411688119 / 35926768250 : ℚ) else if n = (11 : Fin 12) then (87994700387 / 574828292000 : ℚ) else 0)
    else if s = (7 : Fin 12) then (if n = (0 : Fin 12) then (-18484938474 / 17963384125 : ℚ) else if n = (1 : Fin 12) then (70955248768 / 17963384125 : ℚ) else if n = (2 : Fin 12) then (69025336639 / 35926768250 : ℚ) else if n = (3 : Fin 12) then (-9026620947 / 7185353650 : ℚ) else if n = (4 : Fin 12) then (-75284274829 / 17963384125 : ℚ) else if n = (5 : Fin 12) then (86187575371 / 14370707300 : ℚ) else if n = (6 : Fin 12) then (-173041802409 / 35926768250 : ℚ) else if n = (7 : Fin 12) then (253224684001 / 71853536500 : ℚ) else if n = (8 : Fin 12) then (-7759511424 / 3592676825 : ℚ) else if n = (9 : Fin 12) then (7329945467 / 7185353650 : ℚ) else if n = (10 : Fin 12) then (-13596395239 / 35926768250 : ℚ) else if n = (11 : Fin 12) then (5120015909 / 71853536500 : ℚ) else 0)
    else if s = (8 : Fin 12) then (if n = (0 : Fin 12) then (51815885871 / 71853536500 : ℚ) else if n = (1 : Fin 12) then (-96081019261 / 35926768250 : ℚ) else if n = (2 : Fin 12) then (-858038351937 / 287414146000 : ℚ) else if n = (3 : Fin 12) then (133696870351 / 57482829200 : ℚ) else if n = (4 : Fin 12) then (598190063039 / 287414146000 : ℚ) else if n = (5 : Fin 12) then (-450500330043 / 114965658400 : ℚ) else if n = (6 : Fin 12) then (481499971361 / 143707073000 : ℚ) else if n = (7 : Fin 12) then (-1462486375433 / 574828292000 : ℚ) else if n = (8 : Fin 12) then (46993605767 / 28741414600 : ℚ) else if n = (9 : Fin 12) then (-45387163161 / 57482829200 : ℚ) else if n = (10 : Fin 12) then (5380263132 / 17963384125 : ℚ) else if n = (11 : Fin 12) then (-33605757597 / 574828292000 : ℚ) else 0)
    else if s = (9 : Fin 12) then (if n = (0 : Fin 12) then (166017736617 / 71853536500 : ℚ) else if n = (1 : Fin 12) then (-178262080147 / 35926768250 : ℚ) else if n = (2 : Fin 12) then (-1413167004999 / 287414146000 : ℚ) else if n = (3 : Fin 12) then (239714383577 / 57482829200 : ℚ) else if n = (4 : Fin 12) then (1103938403953 / 287414146000 : ℚ) else if n = (5 : Fin 12) then (-823196332861 / 114965658400 : ℚ) else if n = (6 : Fin 12) then (872543813347 / 143707073000 : ℚ) else if n = (7 : Fin 12) then (-2666085924991 / 574828292000 : ℚ) else if n = (8 : Fin 12) then (85001878409 / 28741414600 : ℚ) else if n = (9 : Fin 12) then (-82030112447 / 57482829200 : ℚ) else if n = (10 : Fin 12) then (19304859153 / 35926768250 : ℚ) else if n = (11 : Fin 12) then (-58949539819 / 574828292000 : ℚ) else 0)
    else if s = (10 : Fin 12) then (if n = (0 : Fin 12) then (239420727589 / 71853536500 : ℚ) else if n = (1 : Fin 12) then (-182688004599 / 35926768250 : ℚ) else if n = (2 : Fin 12) then (-1246528684683 / 287414146000 : ℚ) else if n = (3 : Fin 12) then (78828885109 / 57482829200 : ℚ) else if n = (4 : Fin 12) then (2077088889101 / 287414146000 : ℚ) else if n = (5 : Fin 12) then (-1125457772137 / 114965658400 : ℚ) else if n = (6 : Fin 12) then (1137148666999 / 143707073000 : ℚ) else if n = (7 : Fin 12) then (-3291744078147 / 574828292000 : ℚ) else if n = (8 : Fin 12) then (99763852453 / 28741414600 : ℚ) else if n = (9 : Fin 12) then (-92897761699 / 57482829200 : ℚ) else if n = (10 : Fin 12) then (20787673751 / 35926768250 : ℚ) else if n = (11 : Fin 12) then (-60695058623 / 574828292000 : ℚ) else 0)
    else if s = (11 : Fin 12) then (if n = (0 : Fin 12) then (-2221 / 88804 : ℚ) else if n = (1 : Fin 12) then (3257 / 44402 : ℚ) else if n = (2 : Fin 12) then (3711 / 355216 : ℚ) else if n = (3 : Fin 12) then (-32421 / 355216 : ℚ) else if n = (4 : Fin 12) then (-21777 / 355216 : ℚ) else if n = (5 : Fin 12) then (91033 / 710432 : ℚ) else if n = (6 : Fin 12) then (-21167 / 177608 : ℚ) else if n = (7 : Fin 12) then (60535 / 710432 : ℚ) else if n = (8 : Fin 12) then (-10509 / 177608 : ℚ) else if n = (9 : Fin 12) then (10211 / 355216 : ℚ) else if n = (10 : Fin 12) then (-259 / 22201 : ℚ) else if n = (11 : Fin 12) then (1923 / 710432 : ℚ) else 0)
    else 0

theorem eIdx_eq_cert (s : Fin 12) :
    eIdx s = (certRow s (0 : Fin 12)) • C ((0 : Fin 12) : ℕ) + (certRow s (1 : Fin 12)) • C ((1 : Fin 12) : ℕ) + (certRow s (2 : Fin 12)) • C ((2 : Fin 12) : ℕ) + (certRow s (3 : Fin 12)) • C ((3 : Fin 12) : ℕ) + (certRow s (4 : Fin 12)) • C ((4 : Fin 12) : ℕ) + (certRow s (5 : Fin 12)) • C ((5 : Fin 12) : ℕ) + (certRow s (6 : Fin 12)) • C ((6 : Fin 12) : ℕ) + (certRow s (7 : Fin 12)) • C ((7 : Fin 12) : ℕ) + (certRow s (8 : Fin 12)) • C ((8 : Fin 12) : ℕ) + (certRow s (9 : Fin 12)) • C ((9 : Fin 12) : ℕ) + (certRow s (10 : Fin 12)) • C ((10 : Fin 12) : ℕ) + (certRow s (11 : Fin 12)) • C ((11 : Fin 12) : ℕ) := by
  rw [C_val_0, C_val_1, C_val_2, C_val_3, C_val_4, C_val_5, C_val_6, C_val_7, C_val_8, C_val_9, C_val_10, C_val_11]
  funext t
  fin_cases s <;> fin_cases t <;>
    simp [eIdx, certRow, Cvec] <;>
    norm_num

theorem eIdx_mem_span (s : Fin 12) :
    eIdx s ∈ Submodule.span ℚ (Set.range C) := by
  rw [eIdx_eq_cert s]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))) (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))

theorem w12_decompose (u : Fin 12 → ℚ) :
    u = u (0 : Fin 12) • eIdx (0 : Fin 12) + u (1 : Fin 12) • eIdx (1 : Fin 12) + u (2 : Fin 12) • eIdx (2 : Fin 12) + u (3 : Fin 12) • eIdx (3 : Fin 12) + u (4 : Fin 12) • eIdx (4 : Fin 12) + u (5 : Fin 12) • eIdx (5 : Fin 12) + u (6 : Fin 12) • eIdx (6 : Fin 12) + u (7 : Fin 12) • eIdx (7 : Fin 12) + u (8 : Fin 12) • eIdx (8 : Fin 12) + u (9 : Fin 12) • eIdx (9 : Fin 12) + u (10 : Fin 12) • eIdx (10 : Fin 12) + u (11 : Fin 12) • eIdx (11 : Fin 12) := by
  funext s
  fin_cases s <;>
    simp [eIdx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add]

/-- **THE COORDINATE SPANNING LAW.** The fold orbit of the seed spans the
entire coordinate world. -/
theorem span_range_C_eq_top :
    Submodule.span ℚ (Set.range C) = ⊤ := by
  apply top_unique
  intro u _
  rw [w12_decompose u]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (eIdx_mem_span (0 : Fin 12))) (Submodule.smul_mem _ _ (eIdx_mem_span (1 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (2 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (3 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (4 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (5 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (6 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (7 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (8 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (9 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (10 : Fin 12)))) (Submodule.smul_mem _ _ (eIdx_mem_span (11 : Fin 12)))

/-! ## §3 The transfer through the wave compiler -/

section Frame

variable {A : Type u} [AddCommGroup A] [Module ℚ A]
variable {B : Type v} [AddCommGroup B] [Module ℚ B]
variable (Fr : IntersectionChowFrame (Fin 12) A B)

/-- The native source-combination map. -/
def phiNat : (Fin 12 → ℚ) →ₗ[ℚ] A where
  toFun c := ∑ j : Fin 12, c j • Fr.source j
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' k c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- The Betti source-class map. -/
def sourceClassMap : (Fin 12 → ℚ) →ₗ[ℚ] B where
  toFun c := ∑ j : Fin 12, c j • Fr.cycleClass (Fr.source j)
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' k c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

/-- The compiler fold: the owner's wave matrix acting through the frame. -/
def compilerFold : GSTFold A B where
  cycleClass := Fr.cycleClass
  native := nativeMatrixFold Fr Twave
  betti := bettiMatrixFold Fr Twave
  natural z := nativeMatrixFold_class Fr Twave z

/-- The designated native seed: the two leading sources of the frame. -/
def worldSeedNative : A := Fr.source 0 + Fr.source 1

theorem phiNat_eIdx (i : Fin 12) : phiNat Fr (eIdx i) = Fr.source i := by
  simp only [phiNat, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
    (fun j _ hj => by simp [eIdx, hj])]
  simp [eIdx]

theorem phiNat_coordSeed : phiNat Fr coordSeed = worldSeedNative Fr := by
  have h : coordSeed = eIdx 0 + eIdx 1 := by
    funext i; fin_cases i <;> simp [coordSeed, eIdx]
  rw [h, map_add, phiNat_eIdx, phiNat_eIdx]
  rfl

theorem cycleClass_phiNat (c : Fin 12 → ℚ) :
    Fr.cycleClass (phiNat Fr c) = sourceClassMap Fr c := by
  simp only [phiNat, sourceClassMap, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, map_smul]

/-! ### The fold commutes with the coordinate action -/

theorem nativeMatrixFold_phiNat (c : Fin 12 → ℚ) :
    nativeMatrixFold Fr Twave (phiNat Fr c) =
      phiNat Fr (Twave.mulVec c) := by
  have h1 : phiNat Fr c = ∑ j : Fin 12, c j • Fr.source j := rfl
  rw [h1, map_sum]
  have h2 : ∀ j : Fin 12,
      nativeMatrixFold Fr Twave (c j • Fr.source j)
        = ∑ i : Fin 12, (c j * Twave i j) • Fr.source i := by
    intro j
    rw [map_smul, nativeMatrixFold_source Fr Twave j, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [← smul_smul])
  rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_comm]
  have h3 : ∀ i : Fin 12,
      (∑ j : Fin 12, (c j * Twave i j) • Fr.source i)
        = (∑ j : Fin 12, c j * Twave i j) • Fr.source i := by
    intro i
    rw [Finset.sum_smul]
  rw [Finset.sum_congr rfl (fun i _ => h3 i)]
  have h4 : ∀ i : Fin 12,
      (∑ j : Fin 12, c j * Twave i j) = (Twave.mulVec c) i := by
    intro i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [Finset.sum_congr rfl (fun i _ => by rw [h4 i])]
  rfl

/-! ### The orbit is the certificate image -/

theorem orbit_native_eq (n : ℕ) :
    nativeOrbit (compilerFold Fr) (worldSeedNative Fr) n = phiNat Fr (C n) := by
  induction n with
  | zero =>
      show worldSeedNative Fr = phiNat Fr coordSeed
      exact (phiNat_coordSeed Fr).symm
  | succ n ih =>
      show nativeMatrixFold Fr Twave
          (nativeOrbit (compilerFold Fr) (worldSeedNative Fr) n)
        = phiNat Fr (Twave.mulVec (C n))
      rw [ih, nativeMatrixFold_phiNat]

theorem orbit_class_eq (n : ℕ) :
    Fr.cycleClass (nativeOrbit (compilerFold Fr) (worldSeedNative Fr) n)
      = sourceClassMap Fr (C n) := by
  rw [orbit_native_eq, cycleClass_phiNat]

/-- **THE SPAN TRANSFER.** The span of the fold-orbit classes of the seed
equals the entire source-class span — on every certified frame. -/
theorem span_orbitClasses_eq_sourceClassSpan :
    Submodule.span ℚ
        (orbitClassSet (compilerFold Fr) (worldSeedNative Fr))
      = LinearMap.range (sourceClassMap Fr) := by
  have hf : (fun n : ℕ =>
      (compilerFold Fr).cycleClass (nativeOrbit (compilerFold Fr) (worldSeedNative Fr) n))
    = (fun n : ℕ => sourceClassMap Fr (C n)) := by
    funext n
    exact orbit_class_eq Fr n
  unfold orbitClassSet
  rw [hf]
  have h1 : (fun n : ℕ => sourceClassMap Fr (C n))
      = (sourceClassMap Fr) ∘ C := rfl
  rw [h1, Set.range_comp, ← Submodule.map_span, span_range_C_eq_top]
  exact (LinearMap.range_eq_map _).symm

/-! ## §4 THE GST HYPOTHESIS ON THE COMPILER FACE -/

/-- The compiler hypothesis data: the owner's fold, the source-class fiber,
the two-source native seed. -/
def compilerData : GSTHypothesisData A B where
  fold := compilerFold Fr
  hodgeFiber := LinearMap.range (sourceClassMap Fr)
  seed := worldSeedNative Fr

/-- **THE GST HYPOTHESIS, PROVED ON THE COMPILER FACE** — for every
certified frame. -/
theorem gst_hypothesis_complete_compiler :
    GSTHypothesisComplete (compilerData Fr) := by
  show LinearMap.range (sourceClassMap Fr) ≤
    Submodule.span ℚ (orbitClassSet (compilerFold Fr) (worldSeedNative Fr))
  rw [span_orbitClasses_eq_sourceClassSpan]

/-- **THE COMPILER LANDING** — a formality on this face (every
source-class combination is `cl (phiNat c)` by linearity). Recorded to
instantiate the general reduction `gst_hypothesis_landing`; the content of
this module is `span_orbitClasses_eq_sourceClassSpan`. -/
theorem the_compiler_landing :
    ∀ β : B, β ∈ LinearMap.range (sourceClassMap Fr) →
      ∃ z : A, (compilerData Fr).fold.cycleClass z = β := by
  exact gst_hypothesis_landing (compilerData Fr)
    (gst_hypothesis_complete_compiler Fr)

end Frame

/-! ## Receipts -/

#check Twave
#check C
#check Cvec
#check span_range_C_eq_top
#check compilerData
#check gst_hypothesis_complete_compiler
#check the_compiler_landing
#check span_orbitClasses_eq_sourceClassSpan

#print axioms span_range_C_eq_top
#print axioms gst_hypothesis_complete_compiler
#print axioms the_compiler_landing
#print axioms span_orbitClasses_eq_sourceClassSpan

end GSTHypothesisSpanningCompilerFace
