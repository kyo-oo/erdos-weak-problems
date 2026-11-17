import GSTClassicalHodgeFiberedDefectProjectiveCocycle
import GSTClassicalHodgeFiberedNativeProjectiveTransport
import GSTClassicalHodgeFiberedNativeOperatorLift
import GSTClassicalHodgeSynchronizedDefectOrbit

/-!
# GST CLASSICAL HODGE — GLOBAL FIBERED PROJECTIVE DEFECT COCYCLE

The atom-level projective defect law extends to every finite fibered-native
state.

For an actual scheme endomorphism `f`, the fibered-native pushforward commutes
with the genuine native cycle projection.  Primitive cycle-class naturality
then gives the exact global cocycle

  defect(f_* Phi)
    = f_*^H(defect Phi)
      + (f_*^H(hodgeFace Phi) - hodgeFace(f_* Phi)).

Thus genuine projective geometry can change the classical landing defect only
through the mismatch between its actual cohomological pushforward and the
multiplicity/Hodge face transported by the common fibered state.

This statement is fully linear and target-free.  It contains no ghost, no
chosen bad sheet, no Hodge-surjectivity premise, no branch packet, and no
projective apex-spoke existence hypothesis.
-/

set_option maxHeartbeats 90000000
set_option maxRecDepth 1000000

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace GSTClassicalHodgeFiberedDefectProjectiveGlobalCocycle

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeFiberedNativePullback
open GSTClassicalHodgeFiberedCycleClassDefect
open GSTClassicalHodgeFiberedNativeProjectiveTransport
open GSTClassicalHodgeProjectivePointTransport
open GSTClassicalHodgePrimitivePushforwardNaturality
open GSTNativeCodimensionCyclePresentation
open GSTClassicalHodgeFiberedNativeOperatorLift
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeSynchronizedDefectOrbit

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- **GLOBAL NATIVE-FACE FUNCTORIALITY.**
The fibered finite-state transport projects to exactly the genuine native
smooth-projective pushforward on every state, not merely on atoms. -/
theorem nativeFace_fiberedPushforward
    (f : V.X ⟶ V.X)
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (fiberedNativePushforward f Φ) =
      smoothProjectiveNativePushforward V f p (toNativeCycle V H p Φ) := by
  classical
  induction Φ using Finsupp.induction_linear with
  | zero =>
      simp
  | add a b ha hb =>
      simp [ha, hb]
  | single ix q =>
      rcases ix with ⟨i, x⟩
      have hsingle :
          Finsupp.single (i, x) q =
            q • atom V H p i x := by
        simp [atom]
      rw [hsingle]
      simp only [map_smul, fiberedNativePushforward_atom,
        nativeFace_transportAtom, toNativeCycle_atom,
        smoothProjectiveNativePushforward_point]

/-- The actual native cohomology face of the fibered transport is exactly the
geometric cohomological pushforward of the original native face. -/
theorem nativeCycleClass_fiberedPushforward
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (Φ : FiberedNativeAddress V H p) :
    fiberedNativeCycleClass (V := V) (H := H) (p := p)
        (fiberedNativePushforward f Φ) =
      N.cohomologyPushforward
        (fiberedNativeCycleClass (V := V) (H := H) (p := p) Φ) := by
  unfold fiberedNativeCycleClass
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [nativeFace_fiberedPushforward]
  exact N.naturality _

/-- **GLOBAL PROJECTIVE DEFECT COCYCLE.**

For every finite fibered-native state, the defect after genuine projective
transport equals the transported old defect plus one explicit Hodge-face
transport mismatch. -/
theorem fiberedCycleClassDefect_pushforward_cocycle
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f Φ) =
      N.cohomologyPushforward
        (fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ)
      +
      (N.cohomologyPushforward
          (fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ)
        -
        fiberedHodgeAmbient (V := V) (H := H) (p := p)
          (fiberedNativePushforward f Φ)) := by
  unfold fiberedCycleClassDefect
  simp only [LinearMap.sub_apply]
  rw [nativeCycleClass_fiberedPushforward f N Φ]
  rw [LinearMap.map_sub]
  abel

/-- If the source state is already a genuine classical landing state, then the
entire transported defect is exactly the Hodge-face transport mismatch. -/
theorem defect_pushforward_of_source_zero
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (Φ : FiberedNativeAddress V H p)
    (hΦ :
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f Φ) =
      N.cohomologyPushforward
          (fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ)
        -
        fiberedHodgeAmbient (V := V) (H := H) (p := p)
          (fiberedNativePushforward f Φ) := by
  rw [fiberedCycleClassDefect_pushforward_cocycle f N Φ, hΦ,
    LinearMap.map_zero, zero_add]

/-- **EXACT GLOBAL ZERO-DEFECT TRANSPORT CRITERION.**
For a defect-zero source, genuine projective transport remains defect-zero iff
its actual cohomological action agrees with the transported Hodge face. -/
theorem pushforward_defect_zero_iff_hodgeFace_natural
    (f : V.X ⟶ V.X)
    (N : GeometricPushforwardNaturality V H p f)
    (Φ : FiberedNativeAddress V H p)
    (hΦ :
      fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativePushforward f Φ) = 0 ↔
      N.cohomologyPushforward
          (fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ) =
        fiberedHodgeAmbient (V := V) (H := H) (p := p)
          (fiberedNativePushforward f Φ) := by
  rw [defect_pushforward_of_source_zero f N Φ hΦ]
  exact sub_eq_zero

#check nativeFace_fiberedPushforward
#check nativeCycleClass_fiberedPushforward
#check fiberedCycleClassDefect_pushforward_cocycle
#check defect_pushforward_of_source_zero
#check pushforward_defect_zero_iff_hodgeFace_natural

#print axioms nativeFace_fiberedPushforward
#print axioms nativeCycleClass_fiberedPushforward
#print axioms fiberedCycleClassDefect_pushforward_cocycle
#print axioms pushforward_defect_zero_iff_hodgeFace_natural

/-! ## Full native words and their exact Hodge-face cocycle

The cocycle extends beyond one projective generator to every cycle-natural
native operator and every finite word. The correction is a linear map on the
whole common refinement, so intermediate mismatches telescope exactly.
-/

/-- The Hodge-face mismatch of a full state operator and an ambient operator. -/
noncomputable def hodgeFaceMismatch
    (U : Module.End ℚ (FiberedNativeAddress V H p))
    (T : Module.End ℚ
      (RationalSingularCohomology H.analytification (2 * p))) :
    FiberedNativeAddress V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  T.comp (fiberedHodgeAmbient (V := V) (H := H) (p := p)) -
    (fiberedHodgeAmbient (V := V) (H := H) (p := p)).comp U

theorem hodgeFaceMismatch_apply
    (U : Module.End ℚ (FiberedNativeAddress V H p))
    (T : Module.End ℚ
      (RationalSingularCohomology H.analytification (2 * p)))
    (Φ : FiberedNativeAddress V H p) :
    hodgeFaceMismatch U T Φ =
      T (fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ) -
        fiberedHodgeAmbient (V := V) (H := H) (p := p) (U Φ) := rfl

/-- **EXACT COCYCLE COMPOSITION.** The intermediate Hodge face cancels;
only the transported old mismatch and the new mismatch survive. -/
theorem hodgeFaceMismatch_comp
    (U W : Module.End ℚ (FiberedNativeAddress V H p))
    (T S : Module.End ℚ
      (RationalSingularCohomology H.analytification (2 * p))) :
    hodgeFaceMismatch (U.comp W) (T.comp S) =
      T.comp (hodgeFaceMismatch W S) + (hodgeFaceMismatch U T).comp W := by
  apply LinearMap.ext
  intro Φ
  simp only [hodgeFaceMismatch, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, map_sub]
  abel

@[simp] theorem hodgeFaceMismatch_id :
    hodgeFaceMismatch (V := V) (H := H) (p := p)
      LinearMap.id LinearMap.id = 0 := by
  apply LinearMap.ext
  intro Φ
  simp [hodgeFaceMismatch]

/-- The global defect law for an arbitrary state lift with its exact genuine
native commuting square. -/
theorem defect_transport_cocycle
    (U : Module.End ℚ (FiberedNativeAddress V H p))
    (T : CycleClassOperatorPair V H p)
    (hnative : ∀ Φ : FiberedNativeAddress V H p,
      toNativeCycle V H p (U Φ) = T.cycleOperator (toNativeCycle V H p Φ))
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p) (U Φ) =
      T.cohomologyOperator
        (fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ) +
      hodgeFaceMismatch U T.cohomologyOperator Φ := by
  change H.cycleClass p (toNativeCycle V H p (U Φ)) -
      fiberedHodgeAmbient (V := V) (H := H) (p := p) (U Φ) =
    T.cohomologyOperator
      (H.cycleClass p (toNativeCycle V H p Φ) -
        fiberedHodgeAmbient (V := V) (H := H) (p := p) Φ) +
      hodgeFaceMismatch U T.cohomologyOperator Φ
  rw [hnative Φ, T.cycleClass_cycleOperator, hodgeFaceMismatch_apply, map_sub]
  abel

theorem defect_liftNativeOperator_cocycle
    (T : CycleClassOperatorPair V H p)
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (liftNativeOperator T.cycleOperator Φ) =
      T.cohomologyOperator
        (fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ) +
      hodgeFaceMismatch (liftNativeOperator T.cycleOperator)
        T.cohomologyOperator Φ :=
  defect_transport_cocycle (liftNativeOperator T.cycleOperator) T
    (toNativeCycle_liftNativeOperator T.cycleOperator) Φ

theorem lift_defect_zero_iff_mismatch_zero
    (T : CycleClassOperatorPair V H p)
    (Φ : FiberedNativeAddress V H p)
    (hΦ : fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (liftNativeOperator T.cycleOperator Φ) = 0 ↔
      hodgeFaceMismatch (liftNativeOperator T.cycleOperator)
        T.cohomologyOperator Φ = 0 := by
  rw [defect_liftNativeOperator_cocycle T Φ, hΦ, map_zero, zero_add]

/-- Evaluate a finite native/cohomological word, with the head acting last. -/
noncomputable def nativePairWord :
    List (CycleClassOperatorPair V H p) → CycleClassOperatorPair V H p
  | [] => pairId
  | T :: word => pairComp T (nativePairWord word)

/-- Evaluate the same word on the full labelled native state. -/
noncomputable def fiberedNativeWord
    (word : List (CycleClassOperatorPair V H p)) :
    Module.End ℚ (FiberedNativeAddress V H p) :=
  liftNativeOperator (nativePairWord word).cycleOperator

@[simp] theorem fiberedNativeWord_nil :
    fiberedNativeWord (V := V) (H := H) (p := p) [] = LinearMap.id := by
  simp [fiberedNativeWord, nativePairWord, pairId, liftNativeOperator_id]

theorem fiberedNativeWord_cons
    (T : CycleClassOperatorPair V H p)
    (word : List (CycleClassOperatorPair V H p)) :
    fiberedNativeWord (T :: word) =
      (liftNativeOperator T.cycleOperator).comp (fiberedNativeWord word) := by
  change liftNativeOperator
      (T.cycleOperator.comp (nativePairWord word).cycleOperator) = _
  exact liftNativeOperator_comp _ _

theorem nativeFace_fiberedNativeWord
    (word : List (CycleClassOperatorPair V H p))
    (Φ : FiberedNativeAddress V H p) :
    toNativeCycle V H p (fiberedNativeWord word Φ) =
      (nativePairWord word).cycleOperator (toNativeCycle V H p Φ) :=
  toNativeCycle_liftNativeOperator _ Φ

/-- Exact genuine cycle-class naturality holds for every finite native word. -/
theorem nativeClass_fiberedNativeWord
    (word : List (CycleClassOperatorPair V H p))
    (Φ : FiberedNativeAddress V H p) :
    fiberedNativeCycleClass (V := V) (H := H) (p := p)
        (fiberedNativeWord word Φ) =
      (nativePairWord word).cohomologyOperator
        (fiberedNativeCycleClass (V := V) (H := H) (p := p) Φ) := by
  change H.cycleClass p (toNativeCycle V H p (fiberedNativeWord word Φ)) =
      (nativePairWord word).cohomologyOperator
        (H.cycleClass p (toNativeCycle V H p Φ))
  rw [nativeFace_fiberedNativeWord,
    CycleClassOperatorPair.cycleClass_cycleOperator]

noncomputable def wordHodgeFaceMismatch
    (word : List (CycleClassOperatorPair V H p)) :
    FiberedNativeAddress V H p →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p) :=
  hodgeFaceMismatch (fiberedNativeWord word)
    (nativePairWord word).cohomologyOperator

@[simp] theorem wordHodgeFaceMismatch_nil :
    wordHodgeFaceMismatch (V := V) (H := H) (p := p) [] = 0 := by
  simp [wordHodgeFaceMismatch, nativePairWord, pairId]

/-- **TELESCOPING FINITE-WORD LAW.** This recurrence keeps every intermediate
state and every ambient action explicit. -/
theorem wordHodgeFaceMismatch_cons
    (T : CycleClassOperatorPair V H p)
    (word : List (CycleClassOperatorPair V H p)) :
    wordHodgeFaceMismatch (T :: word) =
      T.cohomologyOperator.comp (wordHodgeFaceMismatch word) +
      (hodgeFaceMismatch (liftNativeOperator T.cycleOperator)
        T.cohomologyOperator).comp (fiberedNativeWord word) := by
  unfold wordHodgeFaceMismatch
  rw [fiberedNativeWord_cons]
  change hodgeFaceMismatch
      ((liftNativeOperator T.cycleOperator).comp (fiberedNativeWord word))
      (T.cohomologyOperator.comp (nativePairWord word).cohomologyOperator) = _
  exact hodgeFaceMismatch_comp _ _ _ _

theorem defect_fiberedNativeWord_cocycle
    (word : List (CycleClassOperatorPair V H p))
    (Φ : FiberedNativeAddress V H p) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativeWord word Φ) =
      (nativePairWord word).cohomologyOperator
        (fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ) +
      wordHodgeFaceMismatch word Φ :=
  defect_liftNativeOperator_cocycle (nativePairWord word) Φ

/-- Each genuinely compatible generator contributes zero mismatch, hence the
whole word has zero mismatch by the exact cocycle recurrence. -/
theorem wordHodgeFaceMismatch_zero_of_generators
    (word : List (CycleClassOperatorPair V H p))
    (hword : ∀ T ∈ word,
      hodgeFaceMismatch (liftNativeOperator T.cycleOperator)
        T.cohomologyOperator = 0) :
    wordHodgeFaceMismatch word = 0 := by
  revert hword
  induction word with
  | nil =>
    intro _
    exact wordHodgeFaceMismatch_nil
  | cons T word ih =>
    intro hword
    have hT := hword T (by simp)
    have ht : ∀ S ∈ word,
        hodgeFaceMismatch (liftNativeOperator S.cycleOperator)
          S.cohomologyOperator = 0 := by
      intro S hS
      exact hword S (by simp [hS])
    rw [wordHodgeFaceMismatch_cons, ih ht, hT]
    simp

theorem defectZero_fiberedNativeWord_of_compatible_generators
    (word : List (CycleClassOperatorPair V H p))
    (hword : ∀ T ∈ word,
      hodgeFaceMismatch (liftNativeOperator T.cycleOperator)
        T.cohomologyOperator = 0)
    (Φ : FiberedNativeAddress V H p)
    (hΦ : fiberedCycleClassDefect (V := V) (H := H) (p := p) Φ = 0) :
    fiberedCycleClassDefect (V := V) (H := H) (p := p)
        (fiberedNativeWord word Φ) = 0 := by
  rw [defect_fiberedNativeWord_cocycle, hΦ, map_zero,
    wordHodgeFaceMismatch_zero_of_generators word hword]
  simp

#print axioms hodgeFaceMismatch_comp
#print axioms defect_fiberedNativeWord_cocycle
#print axioms defectZero_fiberedNativeWord_of_compatible_generators

end GSTClassicalHodgeFiberedDefectProjectiveGlobalCocycle
