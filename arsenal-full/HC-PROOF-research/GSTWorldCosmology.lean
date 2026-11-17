import Mathlib
import waves.GSTWaveCohomology

/-!
# GST WORLD COSMOLOGY — dimension-free native carrier

This layer removes the fixed twelve-cell ceiling from the wave geometry.
The unbounded carrier is `Nat × Nat`. Finite-support algebraic fields and
completed fields are distinct; arbitrary rectangular worlds are exact observations.

No geometric interpretation is assumed.  The laws below are internal:
axis transport, transport composition, axis commutation, boundary
extinction, and the exact embedding of the original twelve-cell chart.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTWorldCosmology

open GSTWaveCohomology

/-- A native GST world with arbitrary carry-depth and digit-depth. -/
abbrev WorldCell (carryDepth digitDepth : Nat) : Type :=
  Fin carryDepth × Fin digitDepth

/-- Integer amplitudes on a native GST world. -/
def WorldCoef (carryDepth digitDepth : Nat) : Type :=
  WorldCell carryDepth digitDepth → ℤ

/-- Pointwise additive group structure on world amplitudes.  WorldCoef is a
named function-space definition, so the pointwise instance is exposed
explicitly for downstream linear/operator algebra. -/
instance worldCoefAddCommGroup (carryDepth digitDepth : Nat) :
    AddCommGroup (WorldCoef carryDepth digitDepth) :=
  inferInstanceAs
    (AddCommGroup (WorldCell carryDepth digitDepth → ℤ))

/-- Pointwise integer module structure on world amplitudes. -/
instance worldCoefIntModule (carryDepth digitDepth : Nat) :
    Module ℤ (WorldCoef carryDepth digitDepth) :=
  inferInstanceAs
    (Module ℤ (WorldCell carryDepth digitDepth → ℤ))



/-! ## Limitless carriers and exact finite observations -/

abbrev CosmicCell := ℕ × ℕ
abbrev CompletedCosmos := CosmicCell → ℤ
abbrev CompactCosmos := CosmicCell →₀ ℤ

def observe (A B : ℕ) (f : CompletedCosmos) : WorldCoef A B :=
  fun c => f (c.1.val, c.2.val)

def extendWindow {A B : ℕ} (f : WorldCoef A B) : CompletedCosmos :=
  fun c => if h : c.1 < A ∧ c.2 < B then
    f (⟨c.1, h.1⟩, ⟨c.2, h.2⟩) else 0

@[simp] theorem observe_extendWindow {A B : ℕ} (f : WorldCoef A B) :
    observe A B (extendWindow f) = f := by
  funext c
  simp [observe, extendWindow, c.1.isLt, c.2.isLt]

def SupportedIn (A B : ℕ) (f : CompletedCosmos) : Prop :=
  ∀ c, ¬ (c.1 < A ∧ c.2 < B) → f c = 0

theorem extendWindow_observe_iff (A B : ℕ) (f : CompletedCosmos) :
    extendWindow (observe A B f) = f ↔ SupportedIn A B f := by
  constructor
  · intro h c hc
    rw [← h]
    simp [extendWindow, hc]
  · intro h
    funext c
    by_cases hc : c.1 < A ∧ c.2 < B
    · simp [extendWindow, observe, hc]
    · simp [extendWindow, hc, h c hc]

theorem observations_separate {f g : CompletedCosmos}
    (h : ∀ A B, observe A B f = observe A B g) : f = g := by
  funext c
  exact congrFun (h (c.1 + 1) (c.2 + 1))
    (⟨c.1, by omega⟩, ⟨c.2, by omega⟩)

def restrictWindow {A B C D : ℕ} (hA : A ≤ C) (hB : B ≤ D)
    (f : WorldCoef C D) : WorldCoef A B :=
  fun c => f (⟨c.1.val, lt_of_lt_of_le c.1.isLt hA⟩,
    ⟨c.2.val, lt_of_lt_of_le c.2.isLt hB⟩)

@[simp] theorem restrict_observe {A B C D : ℕ} (hA : A ≤ C) (hB : B ≤ D)
    (f : CompletedCosmos) :
    restrictWindow hA hB (observe C D f) = observe A B f := rfl

theorem restrictWindow_trans {A B C D E F : ℕ}
    (hAC : A ≤ C) (hBD : B ≤ D) (hCE : C ≤ E) (hDF : D ≤ F)
    (f : WorldCoef E F) :
    restrictWindow hAC hBD (restrictWindow hCE hDF f) =
      restrictWindow (hAC.trans hCE) (hBD.trans hDF) f := rfl

/-- Completed observations carry coherence, not a terminal window. -/
structure CosmicObservations where
  window : ∀ A B, WorldCoef A B
  coherent : ∀ {A B C D} (hA : A ≤ C) (hB : B ≤ D),
    restrictWindow hA hB (window C D) = window A B

def completeObservations (f : CompletedCosmos) : CosmicObservations where
  window := fun A B => observe A B f
  coherent := fun _ _ => rfl

def reconstructCosmos (X : CosmicObservations) : CompletedCosmos :=
  fun c => X.window (c.1 + 1) (c.2 + 1)
    (⟨c.1, by omega⟩, ⟨c.2, by omega⟩)

@[simp] theorem reconstruct_complete (f : CompletedCosmos) :
    reconstructCosmos (completeObservations f) = f := rfl

@[simp] theorem observe_reconstruct (X : CosmicObservations) (A B : ℕ) :
    observe A B (reconstructCosmos X) = X.window A B := by
  funext c
  have h := congrFun (X.coherent
    (A := c.1.val + 1) (B := c.2.val + 1) (C := A) (D := B)
    (by omega) (by omega)) (⟨c.1.val, by omega⟩, ⟨c.2.val, by omega⟩)
  exact h.symm

@[ext] theorem CosmicObservations.ext {X Y : CosmicObservations}
    (h : ∀ A B, X.window A B = Y.window A B) : X = Y := by
  cases X with
  | mk X hX =>
    cases Y with
    | mk Y hY =>
      have hXY : X = Y := by
        funext A B
        exact h A B
      subst Y
      rfl

def cosmicObservationEquiv : CompletedCosmos ≃ CosmicObservations where
  toFun := completeObservations
  invFun := reconstructCosmos
  left_inv := reconstruct_complete
  right_inv := by
    intro X
    apply CosmicObservations.ext
    intro A B
    exact observe_reconstruct X A B

noncomputable def compactWindow {A B : ℕ} (f : WorldCoef A B) : CompactCosmos :=
  Finsupp.onFinset (Finset.range A ×ˢ Finset.range B) (extendWindow f) (by
    intro c hc
    by_contra hout
    have h : ¬ (c.1 < A ∧ c.2 < B) := by simpa using hout
    exact hc (by simp [extendWindow, h]))

@[simp] theorem compactWindow_apply {A B : ℕ} (f : WorldCoef A B) (c : CosmicCell) :
    compactWindow f c = extendWindow f c := rfl

/-- Every finite-support field has an exact finite recovery window. -/
theorem compact_has_window (f : CompactCosmos) :
    ∃ A B, SupportedIn A B f := by
  refine ⟨f.support.sup Prod.fst + 1, f.support.sup Prod.snd + 1, ?_⟩
  intro c hc
  by_contra hn
  have hm : c ∈ f.support := Finsupp.mem_support_iff.mpr hn
  have hA : c.1 ≤ f.support.sup Prod.fst := Finset.le_sup hm
  have hB : c.2 ≤ f.support.sup Prod.snd := Finset.le_sup hm
  exact hc ⟨by omega, by omega⟩

theorem compact_exact_recovery (f : CompactCosmos) :
    ∃ A B, compactWindow (observe A B f) = f := by
  obtain ⟨A, B, h⟩ := compact_has_window f
  refine ⟨A, B, ?_⟩
  apply Finsupp.ext
  intro c
  exact congrFun ((extendWindow_observe_iff A B f).mpr h) c

/-- The completed sector is strictly larger than finite support. -/
theorem constant_one_not_compact :
    ¬ ∃ f : CompactCosmos, (fun c => f c) = (fun _ => (1 : ℤ)) := by
  rintro ⟨f, hf⟩
  obtain ⟨A, B, h⟩ := compact_has_window f
  have hz := h (A, B) (by simp)
  have ho := congrFun hf (A, B)
  omega

/-- Global forward transport has no upper wall. -/
def cosmicDigitShift (n : ℕ) (f : CompletedCosmos) : CompletedCosmos :=
  fun c => if n ≤ c.2 then f (c.1, c.2 - n) else 0

def cosmicCarryShift (n : ℕ) (f : CompletedCosmos) : CompletedCosmos :=
  fun c => if n ≤ c.1 then f (c.1 - n, c.2) else 0

@[simp] theorem cosmicDigitShift_zero (f : CompletedCosmos) :
    cosmicDigitShift 0 f = f := by funext c; simp [cosmicDigitShift]

@[simp] theorem cosmicCarryShift_zero (f : CompletedCosmos) :
    cosmicCarryShift 0 f = f := by funext c; simp [cosmicCarryShift]

theorem cosmicDigitShift_add (m n : ℕ) (f : CompletedCosmos) :
    cosmicDigitShift m (cosmicDigitShift n f) = cosmicDigitShift (m+n) f := by
  funext c
  by_cases hm : m ≤ c.2
  · by_cases hn : n ≤ c.2-m
    · have hmn : m+n ≤ c.2 := by omega
      simp [cosmicDigitShift, hm, hn, hmn, Nat.sub_sub]
    · have hmn : ¬ m+n ≤ c.2 := by omega
      simp [cosmicDigitShift, hm, hn, hmn]
  · have hmn : ¬ m+n ≤ c.2 := by omega
    simp [cosmicDigitShift, hm, hmn]

theorem cosmicCarryShift_add (m n : ℕ) (f : CompletedCosmos) :
    cosmicCarryShift m (cosmicCarryShift n f) = cosmicCarryShift (m+n) f := by
  funext c
  by_cases hm : m ≤ c.1
  · by_cases hn : n ≤ c.1-m
    · have hmn : m+n ≤ c.1 := by omega
      simp [cosmicCarryShift, hm, hn, hmn, Nat.sub_sub]
    · have hmn : ¬ m+n ≤ c.1 := by omega
      simp [cosmicCarryShift, hm, hn, hmn]
  · have hmn : ¬ m+n ≤ c.1 := by omega
    simp [cosmicCarryShift, hm, hmn]

theorem cosmic_axes_commute (m n : ℕ) (f : CompletedCosmos) :
    cosmicDigitShift n (cosmicCarryShift m f) =
      cosmicCarryShift m (cosmicDigitShift n f) := by
  funext c
  by_cases hm : m ≤ c.1 <;> by_cases hn : n ≤ c.2 <;>
    simp [cosmicDigitShift, cosmicCarryShift, hm, hn]

theorem cosmicDigitShift_injective (n : ℕ) : Function.Injective (cosmicDigitShift n) := by
  intro f g h
  funext c
  have hx := congrFun h (c.1, c.2+n)
  simpa [cosmicDigitShift] using hx

theorem cosmicCarryShift_injective (n : ℕ) : Function.Injective (cosmicCarryShift n) := by
  intro f g h
  funext c
  have hx := congrFun h (c.1+n, c.2)
  simpa [cosmicCarryShift] using hx

/-- Native digit-axis transport by `n` layers.  No truncation constant is
built into the operator: the active world supplies the boundary. -/
def digitShiftN {carryDepth digitDepth : Nat} (n : Nat)
    (g : WorldCoef carryDepth digitDepth) :
    WorldCoef carryDepth digitDepth :=
  fun c =>
    if h : n ≤ c.2.1 then
      g (c.1, ⟨c.2.1 - n, by omega⟩)
    else 0

/-- Native carry-axis transport by `n` layers. -/
def carryShiftN {carryDepth digitDepth : Nat} (n : Nat)
    (g : WorldCoef carryDepth digitDepth) :
    WorldCoef carryDepth digitDepth :=
  fun c =>
    if h : n ≤ c.1.1 then
      g (⟨c.1.1 - n, by omega⟩, c.2)
    else 0


/-- Finite transport is exactly observation of global transport. -/
@[simp] theorem observe_cosmicDigitShift (A B n : ℕ) (f : CompletedCosmos) :
    observe A B (cosmicDigitShift n f) = digitShiftN n (observe A B f) := by
  funext c
  simp only [observe, cosmicDigitShift, digitShiftN]
  split_ifs <;> rfl

@[simp] theorem observe_cosmicCarryShift (A B n : ℕ) (f : CompletedCosmos) :
    observe A B (cosmicCarryShift n f) = carryShiftN n (observe A B f) := by
  funext c
  simp only [observe, cosmicCarryShift, carryShiftN]
  split_ifs <;> rfl

/-- Zero transport is the identity on every GST world. -/
theorem digitShiftN_zero {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    digitShiftN 0 g = g := by
  funext c
  simp [digitShiftN]

/-- Zero carry transport is the identity on every GST world. -/
theorem carryShiftN_zero {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    carryShiftN 0 g = g := by
  funext c
  simp [carryShiftN]

/-- Digit transport composes additively: traversing `m` layers and then
`n` layers is exactly one traversal of `m+n` layers. -/
theorem digitShiftN_add {carryDepth digitDepth : Nat}
    (m n : Nat) (g : WorldCoef carryDepth digitDepth) :
    digitShiftN m (digitShiftN n g) = digitShiftN (m + n) g := by
  have h := congrArg (observe carryDepth digitDepth)
    (cosmicDigitShift_add m n (extendWindow g))
  simpa using h

/-- Carry transport composes additively. -/
theorem carryShiftN_add {carryDepth digitDepth : Nat}
    (m n : Nat) (g : WorldCoef carryDepth digitDepth) :
    carryShiftN m (carryShiftN n g) = carryShiftN (m + n) g := by
  have h := congrArg (observe carryDepth digitDepth)
    (cosmicCarryShift_add m n (extendWindow g))
  simpa using h

/-- **THE NATIVE RECTANGLE LAW.**  Carry transport and digit transport
commute at every depth in every rectangular GST world.  The old
twelve-cell cup commutation is therefore one finite chart of a
dimension-free law. -/
theorem axes_commute {carryDepth digitDepth : Nat}
    (m n : Nat) (g : WorldCoef carryDepth digitDepth) :
    digitShiftN n (carryShiftN m g) =
      carryShiftN m (digitShiftN n g) := by
  have h := congrArg (observe carryDepth digitDepth)
    (cosmic_axes_commute m n (extendWindow g))
  simpa using h

/-- The digit axis extinguishes exactly at the world depth. -/
theorem digit_boundary_extinction {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    digitShiftN digitDepth g = fun _ => 0 := by
  funext c
  have h : ¬ digitDepth ≤ c.2.1 := by omega
  simp [digitShiftN, h]

/-- The carry axis extinguishes exactly at the world depth. -/
theorem carry_boundary_extinction {carryDepth digitDepth : Nat}
    (g : WorldCoef carryDepth digitDepth) :
    carryShiftN carryDepth g = fun _ => 0 := by
  funext c
  have h : ¬ carryDepth ≤ c.1.1 := by omega
  simp [carryShiftN, h]

/-- Any transport which crosses either world boundary is annihilated.
This is the mixed extinction law of the native rectangle. -/
theorem mixed_boundary_extinction {carryDepth digitDepth m n : Nat}
    (g : WorldCoef carryDepth digitDepth)
    (h : carryDepth ≤ m ∨ digitDepth ≤ n) :
    digitShiftN n (carryShiftN m g) = fun _ => 0 := by
  funext c
  rcases h with hm | hn
  · have hcm : ¬ m ≤ c.1.1 := by omega
    by_cases hd : n ≤ c.2.1
    · simp [digitShiftN, carryShiftN, hd, hcm]
    · simp [digitShiftN, hd]
  · have hdn : ¬ n ≤ c.2.1 := by omega
    simp [digitShiftN, hdn]

/-! ## The old twelve-cell world as one exact chart -/

/-- Embed an original twelve-cell wave cell into the native `4 × 3` world. -/
def waveToWorld (c : WaveCell) : WorldCell 4 3 :=
  (⟨c.carry, c.hcarry⟩, ⟨c.digit, c.hdigit⟩)

/-- Read a native `4 × 3` world cell back as an original wave cell. -/
def worldToWave (c : WorldCell 4 3) : WaveCell :=
  ⟨c.1.1, c.2.1, c.1.2, c.2.2⟩

/-- The two cell presentations are exactly inverse. -/
theorem worldToWave_waveToWorld (c : WaveCell) :
    worldToWave (waveToWorld c) = c := by
  cases c
  rfl

/-- The inverse direction of the chart identity. -/
theorem waveToWorld_worldToWave (c : WorldCell 4 3) :
    waveToWorld (worldToWave c) = c := by
  rcases c with ⟨C, d⟩
  rfl

/-- The old twelve-cell carrier is exactly one native `4 × 3` chart. -/
def waveWorldEquiv : WaveCell ≃ WorldCell 4 3 where
  toFun := waveToWorld
  invFun := worldToWave
  left_inv := worldToWave_waveToWorld
  right_inv := waveToWorld_worldToWave

/-- Export an old wave coefficient into the native `4 × 3` chart. -/
def liftWave (f : WaveCoef) : WorldCoef 4 3 :=
  fun c => f (worldToWave c)

/-- Import a native `4 × 3` coefficient into the old wave chart. -/
def lowerWave (f : WorldCoef 4 3) : WaveCoef :=
  fun c => f (waveToWorld c)

/-- Coefficient transport from the old chart into the native world loses
no information. -/
theorem lowerWave_liftWave (f : WaveCoef) :
    lowerWave (liftWave f) = f := by
  funext c
  simp [lowerWave, liftWave, worldToWave_waveToWorld]

/-- Coefficient transport back into the old chart also loses no information. -/
theorem liftWave_lowerWave (f : WorldCoef 4 3) :
    liftWave (lowerWave f) = f := by
  funext c
  simp [lowerWave, liftWave, waveToWorld_worldToWave]

/-- **THE FIRST COSMOLOGY UPGRADE.**  The original twelve-cell universe is
not a terminal geometry: it is an exact finite chart inside the
dimension-free GST world family, while the native axis laws are valid at
arbitrary carry-depth and digit-depth. -/
theorem twelve_cell_is_native_chart :
    Function.Bijective waveToWorld
    ∧ (∀ (carryDepth digitDepth : Nat)
        (g : WorldCoef carryDepth digitDepth),
        digitShiftN digitDepth g = fun _ => 0)
    ∧ (∀ (carryDepth digitDepth : Nat)
        (g : WorldCoef carryDepth digitDepth),
        carryShiftN carryDepth g = fun _ => 0)
    ∧ (∀ (carryDepth digitDepth m n : Nat)
        (g : WorldCoef carryDepth digitDepth),
        digitShiftN n (carryShiftN m g) =
          carryShiftN m (digitShiftN n g)) := by
  refine ⟨waveWorldEquiv.bijective, ?_, ?_, ?_⟩
  · intro carryDepth digitDepth g
    exact digit_boundary_extinction g
  · intro carryDepth digitDepth g
    exact carry_boundary_extinction g
  · intro carryDepth digitDepth m n g
    exact axes_commute m n g

#check digitShiftN
#check carryShiftN
#check digitShiftN_add
#check carryShiftN_add
#check axes_commute
#check digit_boundary_extinction
#check carry_boundary_extinction
#check mixed_boundary_extinction
#check waveWorldEquiv
#check lowerWave_liftWave
#check liftWave_lowerWave
#check twelve_cell_is_native_chart

#print axioms digitShiftN_add
#print axioms carryShiftN_add
#print axioms axes_commute
#print axioms digit_boundary_extinction
#print axioms carry_boundary_extinction
#print axioms mixed_boundary_extinction
#print axioms twelve_cell_is_native_chart


/-! ## Compact algebraic transport embeds into completed transport -/
def cosmicTranslation (m n : ℕ) : CosmicCell ↪ CosmicCell where
  toFun := fun c => (c.1+m,c.2+n)
  inj' := by intro c d h; apply Prod.ext <;> have h1 := congrArg Prod.fst h <;>
    have h2 := congrArg Prod.snd h <;> simp_all

noncomputable def compactTranslate (m n : ℕ) (f : CompactCosmos) : CompactCosmos :=
  Finsupp.embDomain (cosmicTranslation m n) f

theorem compactTranslate_completed (m n : ℕ) (f : CompactCosmos) :
    (fun c => compactTranslate m n f c) = cosmicDigitShift n (cosmicCarryShift m f) := by
  funext c
  by_cases hr : c ∈ Set.range (cosmicTranslation m n)
  · rcases hr with ⟨d, rfl⟩
    rw [compactTranslate, Finsupp.embDomain_apply_self]
    change f d = cosmicDigitShift n (cosmicCarryShift m f) (d.1 + m, d.2 + n)
    simp [cosmicDigitShift, cosmicCarryShift]
  · rw [compactTranslate, Finsupp.embDomain_of_notMem_range _ _ _ hr]
    by_cases hm : m ≤ c.1
    · by_cases hn : n ≤ c.2
      · exfalso
        apply hr
        refine ⟨(c.1 - m, c.2 - n), ?_⟩
        change ((c.1 - m) + m, (c.2 - n) + n) = c
        apply Prod.ext
        · exact Nat.sub_add_cancel hm
        · exact Nat.sub_add_cancel hn
      · simp [cosmicDigitShift, hn]
    · simp [cosmicDigitShift, cosmicCarryShift, hm]

#print axioms cosmicObservationEquiv
#print axioms compact_exact_recovery
#print axioms constant_one_not_compact

end GSTWorldCosmology
