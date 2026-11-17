import GSTClassicalHodgeNativeOperatorCohomologyRealization
import GSTClassicalHodgeProjectiveCorrespondenceAlgebra
import GSTClassicalHodgeRangeLiftedSpectralOperator

/-!
# GST CLASSICAL HODGE — KERNEL-STABLE NATIVE OPERATOR ALGEBRA

The cohomological realization of a native cycle operator only requires one
well-definedness law: preservation of the kernel of cycle class.  This law is
closed under the complete operator algebra used by the limitless cosmology.

Consequently kernel stability never needs to be reproved for a polynomial,
projector, Lefschetz iterate, or finite rational combination.  It is enough to
establish it on primitive native geometric generators; all generated
operators inherit a canonical ambient cohomological realization.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra
open GSTClassicalHodgeNativeOperatorCohomologyRealization
open GSTClassicalHodgeRangeLiftedSpectralOperator

namespace GSTClassicalHodgeKernelStableOperatorAlgebra

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev NativeEnd
    (V : SmoothProjectiveComplexScheme) (p : Nat) : Type _ :=
  codimensionCycles V.X p →ₗ[ℚ] codimensionCycles V.X p

/-- The zero native operator is kernel-stable. -/
theorem zero_kernelStable :
    KernelStable (H := H) (0 : NativeEnd V p) := by
  intro Z hZ
  simp

/-- The identity native operator is kernel-stable. -/
theorem id_kernelStable :
    KernelStable (H := H) (1 : NativeEnd V p) := by
  intro Z hZ
  have hid : (1 : NativeEnd V p) Z = Z := rfl
  rw [hid]
  exact hZ

/-- Kernel stability is preserved by addition. -/
theorem add_kernelStable
    {A B : NativeEnd V p}
    (hA : KernelStable (H := H) A)
    (hB : KernelStable (H := H) B) :
    KernelStable (H := H) (A + B) := by
  intro Z hZ
  simp [hA Z hZ, hB Z hZ]

/-- Kernel stability is preserved by negation. -/
theorem neg_kernelStable
    {A : NativeEnd V p}
    (hA : KernelStable (H := H) A) :
    KernelStable (H := H) (-A) := by
  intro Z hZ
  simp [hA Z hZ]

/-- Kernel stability is preserved by subtraction. -/
theorem sub_kernelStable
    {A B : NativeEnd V p}
    (hA : KernelStable (H := H) A)
    (hB : KernelStable (H := H) B) :
    KernelStable (H := H) (A - B) := by
  intro Z hZ
  rw [LinearMap.sub_apply, map_sub, hA Z hZ, hB Z hZ, sub_zero]

/-- Kernel stability is preserved by rational scaling. -/
theorem smul_kernelStable
    (q : ℚ) {A : NativeEnd V p}
    (hA : KernelStable (H := H) A) :
    KernelStable (H := H) (q • A) := by
  intro Z hZ
  simp [hA Z hZ]

/-- Kernel stability is preserved by composition. -/
theorem comp_kernelStable
    {A B : NativeEnd V p}
    (hA : KernelStable (H := H) A)
    (hB : KernelStable (H := H) B) :
    KernelStable (H := H) (A.comp B) := by
  intro Z hZ
  exact hA (B Z) (hB Z hZ)

/-- Every iterate of a kernel-stable native operator is kernel-stable. -/
theorem pow_kernelStable
    {A : NativeEnd V p}
    (hA : KernelStable (H := H) A) :
    ∀ n : Nat, KernelStable (H := H) (A ^ n)
  | 0 => id_kernelStable (V := V) (H := H) (p := p)
  | n + 1 => comp_kernelStable (pow_kernelStable hA n) hA

/-- Finite sums of kernel-stable native operators are kernel-stable. -/
theorem finset_sum_kernelStable
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (A : ι → NativeEnd V p)
    (hA : ∀ i ∈ s, KernelStable (H := H) (A i)) :
    KernelStable (H := H) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero_kernelStable (V := V) (H := H) (p := p))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact add_kernelStable (hA a (by simp))
        (ih (fun i hi => hA i (by simp [hi])))

/-- Kernel-stable native endomorphisms form a rational submodule of the full
native operator space. -/
noncomputable def kernelStableSubmodule :
    Submodule ℚ (NativeEnd V p) where
  carrier := {A | KernelStable (H := H) A}
  zero_mem' := zero_kernelStable
  add_mem' := fun hA hB => add_kernelStable hA hB
  smul_mem' := fun q A hA => smul_kernelStable q hA

/-- If every actual scheme-endomorphism generator preserves the cycle-class
kernel, then the entire rational projective-correspondence span does. -/
theorem projectiveCorrespondence_kernelStable
    (hgeom : ∀ f : V.X ⟶ V.X,
      KernelStable (H := H) (geometricGenerator V p f)) :
    ∀ A : NativeEnd V p,
      A ∈ projectiveCorrespondenceSpan V p →
        KernelStable (H := H) A := by
  intro A hA
  have hsubset : geometricGeneratorSet V p ⊆
      (kernelStableSubmodule (V := V) (H := H) (p := p) : Set (NativeEnd V p)) := by
    rintro T ⟨f, rfl⟩
    exact hgeom f
  exact (Submodule.span_le.mpr hsubset) hA

/-- Every kernel-stable projective-correspondence operator acquires the
canonical ambient cohomological action constructed in the previous module. -/
noncomputable def projectiveCorrespondenceOperatorPair
    (K : ProjectiveNativeKernel V p)
    (hgeom : ∀ f : V.X ⟶ V.X,
      KernelStable (H := H) (geometricGenerator V p f)) :=
  projectiveKernelToOperatorPair K
    (projectiveCorrespondence_kernelStable hgeom K.1 K.2)

#check zero_kernelStable
#check id_kernelStable
#check add_kernelStable
#check smul_kernelStable
#check comp_kernelStable
#check pow_kernelStable
#check finset_sum_kernelStable
#check kernelStableSubmodule
#check projectiveCorrespondence_kernelStable
#check projectiveCorrespondenceOperatorPair

#print axioms projectiveCorrespondence_kernelStable
#print axioms projectiveCorrespondenceOperatorPair

/-! ## Full native block geometry

These blocks act on the actual class range and the actual native kernel.
They do not replace either space by a Hodge coordinate carrier.  In particular,
the class-from-kernel block measures precisely the failure of native descent.
-/

abbrev NativeClass (H : HodgeBigradedBettiData V) (p : Nat) :=
  LinearMap.range (H.cycleClass p)

abbrev NativeKernel (H : HodgeBigradedBettiData V) (p : Nat) :=
  LinearMap.ker (H.cycleClass p)

/-- Synthesize an actual native operator from its four class/kernel blocks.
`F` is the class produced from a null-class input; `C` is the kernel-valued
response to an actual class.  No native cycle is left unspecified. -/
noncomputable def nativeBlockOperator
    (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) : NativeEnd V p :=
  (cycleClassRangeSection V H p).comp
      ((B.comp ((H.cycleClass p).rangeRestrict)) +
        (F.comp (nativeKernelCoordinate (H := H)))) +
    ((LinearMap.ker (H.cycleClass p)).subtype).comp
      ((C.comp ((H.cycleClass p).rangeRestrict)) +
        (D.comp (nativeKernelCoordinate (H := H))))

/-- The constructed operator has exactly the requested four blocks. -/
theorem nativeBlockOperator_coordinates
    (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) (Z : codimensionCycles V.X p) :
    nativeClassKernelEquiv (H := H) (nativeBlockOperator B F C D Z) =
      (B ((H.cycleClass p).rangeRestrict Z) +
          F (nativeKernelCoordinate (H := H) Z),
        C ((H.cycleClass p).rangeRestrict Z) +
          D (nativeKernelCoordinate (H := H) Z)) :=
  by
    change (nativeClassKernelEquiv (H := H))
      ((nativeClassKernelEquiv (H := H)).symm
        (B ((H.cycleClass p).rangeRestrict Z) +
          F (nativeKernelCoordinate (H := H) Z),
         C ((H.cycleClass p).rangeRestrict Z) +
          D (nativeKernelCoordinate (H := H) Z))) = _
    exact (nativeClassKernelEquiv (H := H)).apply_symm_apply _

theorem nativeBlockOperator_rangeCoordinate
    (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) (Z : codimensionCycles V.X p) :
    (H.cycleClass p).rangeRestrict (nativeBlockOperator B F C D Z) =
      B ((H.cycleClass p).rangeRestrict Z) +
        F (nativeKernelCoordinate (H := H) Z) :=
  congrArg Prod.fst (nativeBlockOperator_coordinates B F C D Z)

theorem nativeBlockOperator_kernelCoordinate
    (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) (Z : codimensionCycles V.X p) :
    nativeKernelCoordinate (H := H) (nativeBlockOperator B F C D Z) =
      C ((H.cycleClass p).rangeRestrict Z) +
        D (nativeKernelCoordinate (H := H) Z) :=
  congrArg Prod.snd (nativeBlockOperator_coordinates B F C D Z)

/-- Class-to-class block of an arbitrary actual native operator. -/
noncomputable def classClassBlock (A : NativeEnd V p) :
    Module.End ℚ (NativeClass H p) :=
  (H.cycleClass p).rangeRestrict.comp (A.comp (cycleClassRangeSection V H p))

/-- Class response to the complete null-class native coordinate. -/
noncomputable def kernelClassBlock (A : NativeEnd V p) :
    NativeKernel H p →ₗ[ℚ] NativeClass H p :=
  (H.cycleClass p).rangeRestrict.comp
    (A.comp (LinearMap.ker (H.cycleClass p)).subtype)

/-- Kernel-valued response to the class coordinate. -/
noncomputable def classKernelBlock (A : NativeEnd V p) :
    NativeClass H p →ₗ[ℚ] NativeKernel H p :=
  (nativeKernelCoordinate (H := H)).comp (A.comp (cycleClassRangeSection V H p))

/-- Kernel-to-kernel block, without presupposing kernel stability. -/
noncomputable def kernelKernelBlock (A : NativeEnd V p) :
    Module.End ℚ (NativeKernel H p) :=
  (nativeKernelCoordinate (H := H)).comp
    (A.comp (LinearMap.ker (H.cycleClass p)).subtype)

/-- **UNCONDITIONAL FOUR-BLOCK NORMAL FORM.** Every actual native operator
is reconstructed exactly from these four blocks, even when it does not
descend through cycle class. -/
theorem nativeBlockOperator_reconstruct (A : NativeEnd V p) :
    nativeBlockOperator (classClassBlock (H := H) A)
      (kernelClassBlock (H := H) A) (classKernelBlock (H := H) A)
      (kernelKernelBlock (H := H) A) = A := by
  apply LinearMap.ext
  intro Z
  apply (nativeClassKernelEquiv (H := H)).injective
  have hsplit :
      cycleClassRangeSection V H p ((H.cycleClass p).rangeRestrict Z) +
        (nativeKernelCoordinate (H := H) Z).1 = Z := by
    have h := native_projection_decomposition (H := H) Z
    change cycleClassRangeSection V H p ((H.cycleClass p).rangeRestrict Z) +
      (nativeKernelCoordinate (H := H) Z).1 = Z at h
    exact h
  rw [nativeBlockOperator_coordinates, nativeClassKernelEquiv_apply]
  apply Prod.ext
  · apply Subtype.ext
    change
      H.cycleClass p (A (cycleClassRangeSection V H p
        ((H.cycleClass p).rangeRestrict Z))) +
      H.cycleClass p (A (nativeKernelCoordinate (H := H) Z).1) =
      H.cycleClass p (A Z)
    have h := congrArg (fun W : codimensionCycles V.X p =>
      H.cycleClass p (A W)) hsplit
    simpa only [map_add] using h
  · change
      nativeKernelCoordinate (H := H)
        (A (cycleClassRangeSection V H p ((H.cycleClass p).rangeRestrict Z))) +
      nativeKernelCoordinate (H := H)
        (A (nativeKernelCoordinate (H := H) Z).1) =
      nativeKernelCoordinate (H := H) (A Z)
    have h := congrArg (fun W : codimensionCycles V.X p =>
      nativeKernelCoordinate (H := H) (A W)) hsplit
    simpa only [map_add] using h

@[simp]
theorem nativeBlockOperator_zero :
    nativeBlockOperator (H := H) (p := p) 0 0 0 0 = (0 : NativeEnd V p) := by
  apply LinearMap.ext
  intro Z
  apply (nativeClassKernelEquiv (H := H)).injective
  rw [nativeBlockOperator_coordinates]
  simp

theorem nativeBlockOperator_id :
    nativeBlockOperator (H := H) (p := p) LinearMap.id 0 0 LinearMap.id =
      (LinearMap.id : NativeEnd V p) := by
  apply LinearMap.ext
  intro Z
  apply (nativeClassKernelEquiv (H := H)).injective
  rw [nativeBlockOperator_coordinates]
  simp

/-- The complete noncommutative block composition law.  The two feedback
terms are retained, including for operators that fail native descent. -/
theorem nativeBlockOperator_comp
    (B B' : Module.End ℚ (NativeClass H p))
    (F F' : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C C' : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D D' : Module.End ℚ (NativeKernel H p)) :
    (nativeBlockOperator B F C D).comp (nativeBlockOperator B' F' C' D') =
      nativeBlockOperator
        (B.comp B' + F.comp C') (B.comp F' + F.comp D')
        (C.comp B' + D.comp C') (C.comp F' + D.comp D') := by
  apply LinearMap.ext
  intro Z
  apply (nativeClassKernelEquiv (H := H)).injective
  change nativeClassKernelEquiv (H := H)
      (nativeBlockOperator B F C D (nativeBlockOperator B' F' C' D' Z)) =
    nativeClassKernelEquiv (H := H)
      (nativeBlockOperator (B.comp B' + F.comp C')
        (B.comp F' + F.comp D')
        (C.comp B' + D.comp C') (C.comp F' + D.comp D') Z)
  rw [nativeBlockOperator_coordinates, nativeBlockOperator_coordinates]
  apply Prod.ext
  · simp only [nativeBlockOperator_rangeCoordinate,
      nativeBlockOperator_kernelCoordinate, LinearMap.add_apply,
      LinearMap.comp_apply, map_add, Prod.fst]
    abel
  · simp only [nativeBlockOperator_rangeCoordinate,
      nativeBlockOperator_kernelCoordinate, LinearMap.add_apply,
      LinearMap.comp_apply, map_add, Prod.snd]
    abel

theorem nativeBlockOperator_add
    (B B' : Module.End ℚ (NativeClass H p))
    (F F' : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C C' : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D D' : Module.End ℚ (NativeKernel H p)) :
    nativeBlockOperator (B + B') (F + F') (C + C') (D + D') =
      nativeBlockOperator B F C D + nativeBlockOperator B' F' C' D' := by
  apply LinearMap.ext
  intro Z
  apply (nativeClassKernelEquiv (H := H)).injective
  change nativeClassKernelEquiv (H := H)
      (nativeBlockOperator (B + B') (F + F') (C + C') (D + D') Z) =
    nativeClassKernelEquiv (H := H)
      (nativeBlockOperator B F C D Z + nativeBlockOperator B' F' C' D' Z)
  rw [nativeBlockOperator_coordinates, nativeClassKernelEquiv_apply]
  apply Prod.ext
  · simp only [LinearMap.add_apply, map_add, Prod.fst,
      nativeBlockOperator_rangeCoordinate]
    abel
  · simp only [LinearMap.add_apply, map_add, Prod.snd,
      nativeBlockOperator_kernelCoordinate]
    abel

theorem nativeBlockOperator_smul
    (q : ℚ) (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) :
    nativeBlockOperator (q • B) (q • F) (q • C) (q • D) =
      q • nativeBlockOperator B F C D := by
  apply LinearMap.ext
  intro Z
  apply (nativeClassKernelEquiv (H := H)).injective
  change nativeClassKernelEquiv (H := H)
      (nativeBlockOperator (q • B) (q • F) (q • C) (q • D) Z) =
    nativeClassKernelEquiv (H := H) (q • nativeBlockOperator B F C D Z)
  rw [nativeBlockOperator_coordinates, nativeClassKernelEquiv_apply]
  apply Prod.ext
  · simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply,
      Prod.fst, nativeBlockOperator_rangeCoordinate, smul_add]
  · simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply,
      Prod.snd, nativeBlockOperator_kernelCoordinate, smul_add]

theorem nativeBlockOperator_kernelClassBlock
    (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) :
    kernelClassBlock (H := H) (nativeBlockOperator B F C D) = F := by
  apply LinearMap.ext
  intro k
  change (H.cycleClass p).rangeRestrict (nativeBlockOperator B F C D k.1) = F k
  rw [nativeBlockOperator_rangeCoordinate]
  have hr : (H.cycleClass p).rangeRestrict k.1 = 0 := Subtype.ext k.2
  rw [hr, nativeKernelCoordinate_kernel]
  simp

theorem nativeBlockOperator_classClassBlock
    (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) :
    classClassBlock (H := H) (nativeBlockOperator B F C D) = B := by
  apply LinearMap.ext
  intro a
  change (H.cycleClass p).rangeRestrict
    (nativeBlockOperator B F C D (cycleClassRangeSection V H p a)) = B a
  rw [nativeBlockOperator_rangeCoordinate]
  simp

theorem nativeBlockOperator_classKernelBlock
    (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) :
    classKernelBlock (H := H) (nativeBlockOperator B F C D) = C := by
  apply LinearMap.ext
  intro a
  change nativeKernelCoordinate (H := H)
    (nativeBlockOperator B F C D (cycleClassRangeSection V H p a)) = C a
  rw [nativeBlockOperator_kernelCoordinate]
  simp

theorem nativeBlockOperator_kernelKernelBlock
    (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) :
    kernelKernelBlock (H := H) (nativeBlockOperator B F C D) = D := by
  apply LinearMap.ext
  intro k
  change nativeKernelCoordinate (H := H) (nativeBlockOperator B F C D k.1) = D k
  rw [nativeBlockOperator_kernelCoordinate]
  have hr : (H.cycleClass p).rangeRestrict k.1 = 0 := Subtype.ext k.2
  rw [hr, nativeKernelCoordinate_kernel]
  simp

/-- The four-block normal form is unique, as well as exhaustive. -/
theorem nativeBlockOperator_eq_iff
    (B B' : Module.End ℚ (NativeClass H p))
    (F F' : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C C' : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D D' : Module.End ℚ (NativeKernel H p)) :
    nativeBlockOperator B F C D = nativeBlockOperator B' F' C' D' ↔
      B = B' ∧ F = F' ∧ C = C' ∧ D = D' := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [nativeBlockOperator_classClassBlock] using
        congrArg (classClassBlock (H := H)) h
    · simpa only [nativeBlockOperator_kernelClassBlock] using
        congrArg (kernelClassBlock (H := H)) h
    · simpa only [nativeBlockOperator_classKernelBlock] using
        congrArg (classKernelBlock (H := H)) h
    · simpa only [nativeBlockOperator_kernelKernelBlock] using
        congrArg (kernelKernelBlock (H := H)) h
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- **EXACT DESCENT TEST.** Native descent fails precisely when a null-class
input creates a nonzero class coordinate.  The other three blocks are free. -/
theorem kernelStable_iff_kernelClassBlock_eq_zero (A : NativeEnd V p) :
    KernelStable (H := H) A ↔ kernelClassBlock (H := H) A = 0 := by
  constructor
  · intro hA
    apply LinearMap.ext
    intro k
    apply Subtype.ext
    exact hA k.1 k.2
  · intro hA Z hZ
    have h := LinearMap.congr_fun hA (⟨Z, hZ⟩ : NativeKernel H p)
    exact congrArg Subtype.val h

theorem nativeBlockOperator_kernelStable_iff
    (B : Module.End ℚ (NativeClass H p))
    (F : NativeKernel H p →ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) :
    KernelStable (H := H) (nativeBlockOperator B F C D) ↔ F = 0 := by
  rw [kernelStable_iff_kernelClassBlock_eq_zero,
    nativeBlockOperator_kernelClassBlock]

theorem nativeBlockOperator_kernelStable
    (B : Module.End ℚ (NativeClass H p))
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : Module.End ℚ (NativeKernel H p)) :
    KernelStable (H := H) (nativeBlockOperator B 0 C D) :=
  (nativeBlockOperator_kernelStable_iff B 0 C D).2 rfl

theorem kernelStable_nativeBlock_reconstruct
    (A : NativeEnd V p) (hA : KernelStable (H := H) A) :
    nativeBlockOperator (classClassBlock (H := H) A) 0
      (classKernelBlock (H := H) A) (kernelKernelBlock (H := H) A) = A := by
  have h := nativeBlockOperator_reconstruct (H := H) A
  rw [(kernelStable_iff_kernelClassBlock_eq_zero A).1 hA] at h
  exact h

/-- Kernel feedback has a precise semidirect composition law; it cannot be
silently folded into the descended class operator. -/
theorem nativeTriangularOperator_comp
    (B B' : Module.End ℚ (NativeClass H p))
    (C C' : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D D' : Module.End ℚ (NativeKernel H p)) :
    (nativeBlockOperator B 0 C D).comp (nativeBlockOperator B' 0 C' D') =
      nativeBlockOperator (B.comp B') 0
        (C.comp B' + D.comp C') (D.comp D') := by
  simpa using nativeBlockOperator_comp B B' 0 0 C C' D D'

/-- The full native family preserving every actual cycle class. -/
theorem classPreserving_iff_blocks (A : NativeEnd V p) :
    (∀ Z, H.cycleClass p (A Z) = H.cycleClass p Z) ↔
      classClassBlock (H := H) A = LinearMap.id ∧
        kernelClassBlock (H := H) A = 0 := by
  constructor
  · intro hA
    constructor
    · apply LinearMap.ext
      intro a
      apply Subtype.ext
      exact (hA (cycleClassRangeSection V H p a)).trans
        (cycleClassRangeSection_class a)
    · apply (kernelStable_iff_kernelClassBlock_eq_zero A).1
      intro Z hZ
      exact (hA Z).trans hZ
  · rintro ⟨hB, hF⟩ Z
    have h := nativeBlockOperator_rangeCoordinate
      (classClassBlock (H := H) A) (kernelClassBlock (H := H) A)
      (classKernelBlock (H := H) A) (kernelKernelBlock (H := H) A) Z
    rw [nativeBlockOperator_reconstruct, hB, hF] at h
    simpa using congrArg Subtype.val h

/-- A native descent's class block is exactly the actual descended action,
despite the arbitrary choice of a range section. -/
theorem classClassBlock_eq_rangeOperator
    (A : NativeEnd V p) (hA : KernelStable (H := H) A) :
    classClassBlock (H := H) A = rangeOperator A hA := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  apply class_congr_of_kernelStable A hA
  exact (cycleClassRangeSection_class a).trans (rangeRepresentative_spec a).symm

/-! ## Invertible native kernel feedback -/

/-- A triangular change of native coordinates is invertible when its two
diagonal actions are invertible.  The inverse removes the full feedback. -/
noncomputable def triangularCoordinateEquiv
    (B : NativeClass H p ≃ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : NativeKernel H p ≃ₗ[ℚ] NativeKernel H p) :
    (NativeClass H p × NativeKernel H p) ≃ₗ[ℚ]
      (NativeClass H p × NativeKernel H p) where
  toLinearMap := {
    toFun := fun a => (B a.1, C a.1 + D a.2)
    map_add' := by
      intro a b
      apply Prod.ext
      · change B (a.1 + b.1) = B a.1 + B b.1
        exact map_add B a.1 b.1
      · change C (a.1 + b.1) + D (a.2 + b.2) =
            (C a.1 + D a.2) + (C b.1 + D b.2)
        rw [map_add, map_add]
        abel
    map_smul' := by
      intro q a
      apply Prod.ext
      · change B (q • a.1) = q • B a.1
        exact map_smul B q a.1
      · change C (q • a.1) + D (q • a.2) =
            q • (C a.1 + D a.2)
        rw [map_smul, map_smul, smul_add]
  }
  invFun a := (B.symm a.1, D.symm (a.2 - C (B.symm a.1)))
  left_inv := by
    intro a
    apply Prod.ext
    · simp
    · simp only [LinearEquiv.symm_apply_apply]
      have key : C a.1 + D a.2 - C a.1 = D a.2 := by abel
      rw [key]
      simp
  right_inv := by
    intro a
    apply Prod.ext
    · simp
    · simp only [Prod.snd, map_sub, LinearEquiv.apply_symm_apply] <;> abel

/-- The triangular coordinate change is its own inverse-pair carrier: the
symmetric application law used by the invertible native feedback theory. -/
theorem triangularCoordinateEquiv_symm_apply
    (B : NativeClass H p ≃ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : NativeKernel H p ≃ₗ[ℚ] NativeKernel H p)
    (a : NativeClass H p × NativeKernel H p) :
    (triangularCoordinateEquiv B C D).symm a =
      (B.symm a.1, D.symm (a.2 - C (B.symm a.1))) := rfl

/-- Construct the corresponding invertible operator on actual native cycles. -/
noncomputable def nativeTriangularEquiv
    (B : NativeClass H p ≃ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : NativeKernel H p ≃ₗ[ℚ] NativeKernel H p) :
    codimensionCycles V.X p ≃ₗ[ℚ] codimensionCycles V.X p :=
  ((nativeClassKernelEquiv (H := H)).trans (triangularCoordinateEquiv B C D)).trans
    (nativeClassKernelEquiv (H := H)).symm

theorem nativeTriangularEquiv_toLinearMap
    (B : NativeClass H p ≃ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : NativeKernel H p ≃ₗ[ℚ] NativeKernel H p) :
    (nativeTriangularEquiv B C D).toLinearMap =
      nativeBlockOperator B.toLinearMap 0 C D.toLinearMap := by
  apply LinearMap.ext
  intro Z
  simp [nativeTriangularEquiv, triangularCoordinateEquiv,
    nativeBlockOperator, nativeClassKernelEquiv_symm_apply]

/-- The actual inverse is another constructed native operator, with the
negative conjugated feedback in its lower-left block. -/
theorem nativeTriangularEquiv_inverse_toLinearMap
    (B : NativeClass H p ≃ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : NativeKernel H p ≃ₗ[ℚ] NativeKernel H p) :
    (nativeTriangularEquiv B C D).symm.toLinearMap =
      nativeBlockOperator B.symm.toLinearMap 0
        ((-1 : ℚ) • (D.symm.toLinearMap.comp (C.comp B.symm.toLinearMap)))
        D.symm.toLinearMap := by
  apply LinearMap.ext
  intro Z
  apply (nativeClassKernelEquiv (H := H)).injective
  change (nativeClassKernelEquiv (H := H))
      ((nativeClassKernelEquiv (H := H)).symm
        ((triangularCoordinateEquiv B C D).symm
          ((H.cycleClass p).rangeRestrict Z,
            nativeKernelCoordinate (H := H) Z))) =
    nativeClassKernelEquiv (H := H)
      (nativeBlockOperator B.symm.toLinearMap 0
        ((-1 : ℚ) • (D.symm.toLinearMap.comp (C.comp B.symm.toLinearMap)))
        D.symm.toLinearMap Z)
  rw [LinearEquiv.apply_symm_apply, nativeBlockOperator_coordinates]
  apply Prod.ext
  · rw [triangularCoordinateEquiv_symm_apply]
    simp only [LinearMap.zero_apply, add_zero]
    rfl
  · change D.symm.toLinearMap (nativeKernelCoordinate (H := H) Z -
        C (B.symm ((H.cycleClass p).rangeRestrict Z))) =
      (-1 : ℚ) • D.symm.toLinearMap (C (B.symm ((H.cycleClass p).rangeRestrict Z))) +
        D.symm.toLinearMap (nativeKernelCoordinate (H := H) Z)
    rw [map_sub (D.symm.toLinearMap) (nativeKernelCoordinate (H := H) Z)
        (C (B.symm ((H.cycleClass p).rangeRestrict Z)))]
    rw [show (-1 : ℚ) • D.symm.toLinearMap (C (B.symm ((H.cycleClass p).rangeRestrict Z))) =
        -(D.symm.toLinearMap (C (B.symm ((H.cycleClass p).rangeRestrict Z)))) from
        _root_.neg_one_smul ℚ
          (D.symm.toLinearMap (C (B.symm ((H.cycleClass p).rangeRestrict Z))))]
    abel

theorem nativeTriangularEquiv_kernelStable
    (B : NativeClass H p ≃ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : NativeKernel H p ≃ₗ[ℚ] NativeKernel H p) :
    KernelStable (H := H) (nativeTriangularEquiv B C D).toLinearMap := by
  rw [nativeTriangularEquiv_toLinearMap]
  exact nativeBlockOperator_kernelStable _ _ _

theorem nativeTriangularEquiv_inverse_kernelStable
    (B : NativeClass H p ≃ₗ[ℚ] NativeClass H p)
    (C : NativeClass H p →ₗ[ℚ] NativeKernel H p)
    (D : NativeKernel H p ≃ₗ[ℚ] NativeKernel H p) :
    KernelStable (H := H) (nativeTriangularEquiv B C D).symm.toLinearMap := by
  rw [nativeTriangularEquiv_inverse_toLinearMap]
  exact nativeBlockOperator_kernelStable _ _ _

/-! ## The cohomological escape block: the new exact geometry gate

Four-block native endomorphisms are complete, but all of their classes stay
inside the algebraic image.  The ambient class/defect splitting proves a
substantially sharper criterion: the class-to-defect block of a rational
cohomology operator is ZERO exactly when a genuine native operator can
realize its action on all cycle classes.

This identifies which GST ambient motions are geometric, without supplying
a requested missing Hodge class, ghost-targeted spoke, or Hodge conclusion as
an axiom.  A nonzero class-to-defect block is an exact obstruction to native
realizability, not simply a shortage of more elaborate words.
-/

/-- The intrinsic class -> missing-cohomology block of an ambient motion.
It is defined from the actual cycle-class image and the intrinsic defect
projection, never from an assumed Hodge-basis representative. -/
noncomputable def cohomologyClassToDefectBlock
    (T : Module.End ℚ (Coh H p)) :
    NativeClass H p →ₗ[ℚ]
      NativeCohomologicalDefect (V := V) (H := H) (p := p) :=
  (cohomologicalDefectCoordinate (H := H)).comp
    (T.comp (LinearMap.range (H.cycleClass p)).subtype)

/-- **EXACT AMBIENT RANGE-STABILITY LAW.**
An arbitrary cohomological motion preserves the actual algebraic-class range
if and only if its class-to-defect block vanishes.  This is a directly proved
matrix-block criterion, not a geometric hypothesis. -/
theorem classToDefectBlock_eq_zero_iff_rangeStable
    (T : Module.End ℚ (Coh H p)) :
    cohomologyClassToDefectBlock (H := H) T = 0 ↔
      ∀ alpha : Coh H p,
        alpha ∈ LinearMap.range (H.cycleClass p) →
          T alpha ∈ LinearMap.range (H.cycleClass p) := by
  constructor
  · intro hT alpha halpha
    have h := LinearMap.congr_fun hT
      (⟨alpha, halpha⟩ : NativeClass H p)
    have hz : offRangeProjection (H := H) (T alpha) = 0 :=
      congrArg Subtype.val h
    exact (offRangeProjection_eq_zero_iff_range _).1 hz
  · intro hT
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    change offRangeProjection (H := H) (T a.1) = 0
    exact (offRangeProjection_eq_zero_iff_range _).2 (hT a.1 a.2)

/-- Any cohomological action that is genuinely implemented by a native
cycle operator necessarily has ZERO class-to-defect block.  No kernel-stable
assumption is needed on the supplied operator: the naturality equation itself
already enforces the geometry. -/
theorem classToDefectBlock_zero_of_nativeRealization
    (T : Module.End ℚ (Coh H p))
    (A : NativeEnd V p)
    (hA : ∀ Z : Cycles V p,
      H.cycleClass p (A Z) = T (H.cycleClass p Z)) :
    cohomologyClassToDefectBlock (H := H) T = 0 := by
  apply (classToDefectBlock_eq_zero_iff_rangeStable T).2
  intro alpha halpha
  obtain ⟨Z, hZ⟩ := halpha
  rw [← hZ, ← hA Z]
  exact ⟨A Z, rfl⟩

/-- **FULL LINEAR NATIVE-REALIZABILITY CLASSIFICATION.**
A rational cohomological endomorphism admits a linear native-cycle
realization, commuting with the cycle class on ALL native cycles, if and only
if its class-to-defect block is zero.

The reverse direction is explicitly constructed using the same exact
native class-range section.  This is an algebraic *linear lifting* result,
not evidence that the lifted operator is induced by an algebraic
correspondence.  It exposes the gap left by the old input/output packages. -/
theorem cohomologyNativeRealizable_iff_classToDefectBlock_zero
    (T : Module.End ℚ (Coh H p)) :
    (∃ A : NativeEnd V p,
      ∀ Z : Cycles V p,
        H.cycleClass p (A Z) = T (H.cycleClass p Z)) ↔
      cohomologyClassToDefectBlock (H := H) T = 0 := by
  constructor
  · rintro ⟨A, hA⟩
    exact classToDefectBlock_zero_of_nativeRealization T A hA
  · intro hT
    have hstable :
        ∀ alpha : Coh H p,
          alpha ∈ LinearMap.range (H.cycleClass p) →
            T alpha ∈ LinearMap.range (H.cycleClass p) :=
      (classToDefectBlock_eq_zero_iff_rangeStable T).1 hT
    exact ⟨liftedCycleOperator T hstable,
      fun Z => cycleClass_liftedCycleOperator T hstable Z⟩

/-- A nonzero algebraic-class -> defect block is a definitive proof that the
operator has NO native cycle-class natural realization.  This is much
stronger than a failure to find a particular projective correspondence. -/
theorem no_nativeRealization_of_nonzero_classToDefect
    (T : Module.End ℚ (Coh H p))
    (hne : cohomologyClassToDefectBlock (H := H) T ≠ 0) :
    ¬ ∃ A : NativeEnd V p,
      ∀ Z : Cycles V p,
        H.cycleClass p (A Z) = T (H.cycleClass p Z) := by
  intro hex
  exact hne
    ((cohomologyNativeRealizable_iff_classToDefectBlock_zero T).1 hex)

/-- Every abstract linear map from actual algebraic classes into the exact
unreached defect sector DOES extend to an ambient cohomology endomorphism.
Such a formal operator is easy to construct; geometric realization is the
genuinely restrictive part. -/
noncomputable def pureClassToDefectOperator
    (F : NativeClass H p →ₗ[ℚ]
      NativeCohomologicalDefect (V := V) (H := H) (p := p)) :
    Module.End ℚ (Coh H p) :=
  (LinearMap.ker (classRangeProjection (H := H))).subtype.comp
    (F.comp (classRangeRetraction (H := H)))

/-- **EXACT SYNTHESIS OF THE ESCAPE BLOCK.**
The previous abstract operator has precisely the requested class-to-defect
block, showing that ambient freedom alone does not confer geometric origin. -/
theorem pureClassToDefectOperator_block
    (F : NativeClass H p →ₗ[ℚ]
      NativeCohomologicalDefect (V := V) (H := H) (p := p)) :
    cohomologyClassToDefectBlock (H := H)
      (pureClassToDefectOperator F) = F := by
  apply LinearMap.ext
  intro a
  change cohomologicalDefectCoordinate (H := H)
    ((F (classRangeRetraction (H := H) a.1)).1) = F a
  rw [classRangeRetraction_range]
  exact cohomologicalDefectCoordinate_pureDefect (F a)

/-- An ambient 'escape' operator with a nonzero requested block can never
be implemented by a native cycle operator.  This is the exact non-geometric
sector of the enlarged GST motion algebra. -/
theorem pureClassToDefectOperator_nonGeometric
    (F : NativeClass H p →ₗ[ℚ]
      NativeCohomologicalDefect (V := V) (H := H) (p := p))
    (hF : F ≠ 0) :
    ¬ ∃ A : NativeEnd V p,
      ∀ Z : Cycles V p,
        H.cycleClass p (A Z) =
          pureClassToDefectOperator F (H.cycleClass p Z) := by
  apply no_nativeRealization_of_nonzero_classToDefect
  rw [pureClassToDefectOperator_block]
  exact hF

/-! ## The autonomous defect action and its precise limits

When an ambient cohomological motion preserves genuine algebraic classes,
its complete action on the unreached sector can be computed with NO
new native-cycle representative and NO Hodge-input assumption.

The defect sector is a genuine invariant quotient coordinate.  If its
induced action is injective, the motion cannot make a missing Hodge
direction become algebraic.  Thus iterating more invertible GST motions
cannot erase a real obstruction; a proof needs an actual geometric
reason that the obstruction was zero in the first place.
-/

/-- The full defect-to-defect block of an arbitrary ambient cohomology
endomorphism.  In the class-stable case this is precisely its induced
action on cohomology modulo the actual algebraic range. -/
noncomputable def cohomologyDefectAction
    (T : Module.End ℚ (Coh H p)) :
    Module.End ℚ
      (NativeCohomologicalDefect (V := V) (H := H) (p := p)) :=
  (cohomologicalDefectCoordinate (H := H)).comp
    (T.comp (LinearMap.ker
      (classRangeProjection (H := H))).subtype)

/-- **AUTONOMOUS QUOTIENT DYNAMICS.**
When an ambient motion preserves the true native cycle-class range, its
effect on any cohomological defect is entirely controlled by the defect
itself.  The algebraic component of the input contributes exactly zero. -/
theorem cohomologicalDefect_after_rangeStable
    (T : Module.End ℚ (Coh H p))
    (hT : cohomologyClassToDefectBlock (H := H) T = 0)
    (alpha : Coh H p) :
    cohomologicalDefectCoordinate (H := H) (T alpha) =
      cohomologyDefectAction T
        (cohomologicalDefectCoordinate (H := H) alpha) := by
  have hstable := (classToDefectBlock_eq_zero_iff_rangeStable T).1 hT
  have hz :
      cohomologicalDefectCoordinate (H := H)
        (T (classRangeProjection (H := H) alpha)) = 0 := by
    apply Subtype.ext
    change offRangeProjection (H := H)
      (T (classRangeProjection (H := H) alpha)) = 0
    exact (offRangeProjection_eq_zero_iff_range _).2
      (hstable _ (classRangeProjection_mem_range alpha))
  calc
    cohomologicalDefectCoordinate (H := H) (T alpha) =
      cohomologicalDefectCoordinate (H := H)
        (T (classRangeProjection (H := H) alpha +
          offRangeProjection (H := H) alpha)) := by
            rw [ambient_range_decomposition]
    _ =
      cohomologicalDefectCoordinate (H := H)
        (T (classRangeProjection (H := H) alpha)) +
      cohomologicalDefectCoordinate (H := H)
        (T (offRangeProjection (H := H) alpha)) := by
          simp only [map_add]
    _ = cohomologyDefectAction T
          (cohomologicalDefectCoordinate (H := H) alpha) := by
          rw [hz, zero_add]
          rfl

/-- **DEFECT-DYNAMICS COMPOSITION LAW.**
The quotient sector carries a genuine representation of the monoid of
class-stable cohomological motions.  Composition does not need a separately
supplied Hodge-basis operator or a projective-spoke input. -/
theorem cohomologyDefectAction_comp_of_rangeStable
    (T U : Module.End ℚ (Coh H p))
    (hT : cohomologyClassToDefectBlock (H := H) T = 0)
    (hU : cohomologyClassToDefectBlock (H := H) U = 0) :
    cohomologyDefectAction (T.comp U) =
      (cohomologyDefectAction T).comp (cohomologyDefectAction U) := by
  apply LinearMap.ext
  intro k
  change cohomologicalDefectCoordinate (H := H) (T (U k.1)) =
    cohomologyDefectAction T (cohomologyDefectAction U k)
  rw [cohomologicalDefect_after_rangeStable T hT (U k.1)]
  rw [cohomologicalDefect_after_rangeStable U hU k.1]
  rw [cohomologicalDefectCoordinate_pureDefect]

/-- The entire native-generated coherent ambient algebra acts trivially
on the quotient sector, not merely on one hand-selected ghost detector. -/
theorem nativeCore_defectAction_zero
    (A : NativeEnd V p) (hA : KernelStable (H := H) A) :
    cohomologyDefectAction (supportedAmbientOperator A hA) = 0 := by
  apply LinearMap.ext
  intro k
  exact supportedAmbientOperator_defect_zero A hA k.1

/-- **NON-COLLAPSE UNDER INJECTIVE DEFECT DYNAMICS.**
A range-stable GST motion whose induced defect action is injective cannot
send a class with a genuine nonzero defect into the native algebraic range.
This remains true independently of how large the native operator algebra is. -/
theorem nonzero_defect_survives_injective_dynamics
    (T : Module.End ℚ (Coh H p))
    (hT : cohomologyClassToDefectBlock (H := H) T = 0)
    (hinj : Function.Injective (cohomologyDefectAction T))
    (alpha : Coh H p)
    (hbad : cohomologicalDefectCoordinate (H := H) alpha ≠ 0) :
    cohomologicalDefectCoordinate (H := H) (T alpha) ≠ 0 := by
  intro hz
  have heq :
      cohomologyDefectAction T
        (cohomologicalDefectCoordinate (H := H) alpha) = 0 := by
    rw [← cohomologicalDefect_after_rangeStable T hT alpha]
    exact hz
  apply hbad
  apply hinj
  simpa using heq

#check cohomologyDefectAction
#check cohomologicalDefect_after_rangeStable
#check cohomologyDefectAction_comp_of_rangeStable
#check nativeCore_defectAction_zero
#check nonzero_defect_survives_injective_dynamics

#print axioms cohomologyDefectAction_comp_of_rangeStable
#print axioms nativeCore_defectAction_zero
#print axioms nonzero_defect_survives_injective_dynamics

#check cohomologyClassToDefectBlock
#check classToDefectBlock_eq_zero_iff_rangeStable
#check cohomologyNativeRealizable_iff_classToDefectBlock_zero
#check pureClassToDefectOperator
#check pureClassToDefectOperator_block
#check pureClassToDefectOperator_nonGeometric

#print axioms cohomologyNativeRealizable_iff_classToDefectBlock_zero
#print axioms pureClassToDefectOperator_block

#print axioms nativeBlockOperator_reconstruct
#print axioms nativeBlockOperator_comp
#print axioms nativeBlockOperator_kernelStable_iff
#print axioms nativeTriangularEquiv
#print axioms nativeTriangularEquiv_inverse_toLinearMap

end GSTClassicalHodgeKernelStableOperatorAlgebra

