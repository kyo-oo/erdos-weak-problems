import Mathlib.Algebra.Module.Projective
import GSTClassicalHodgeNativeArsenalRepresentation
import GSTClassicalHodgeProjectiveCorrespondenceAlgebra

/-!
# GST CLASSICAL HODGE — NATIVE OPERATOR COHOMOLOGY REALIZATION

A native algebraic-cycle operator should not require an independently supplied
cohomological operator.  The only well-definedness condition is that it
preserve the kernel of the cycle-class map.  Under that condition it descends
to the quotient represented by the actual cycle-class range.  Since rational
vector spaces are projective/injective enough for linear extension, the range
operator extends to ambient rational singular cohomology.

This module therefore turns a native projective-correspondence operator plus
kernel preservation into a complete `CycleClassOperatorPair` automatically.
The cycle-class commuting square is proved, not stored as unrelated data.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeProjectiveCorrespondenceAlgebra

namespace GSTClassicalHodgeNativeOperatorCohomologyRealization

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Cycles (V : SmoothProjectiveComplexScheme) (p : Nat) : Type _ :=
  codimensionCycles V.X p
abbrev Coh (H : HodgeBigradedBettiData V) (p : Nat) : Type _ :=
  RationalSingularCohomology H.analytification (2 * p)

/-- A native cycle operator respects cycle-class equivalence precisely when it
maps the kernel of cycle class into itself. -/
def KernelStable
    (A : Cycles V p →ₗ[ℚ] Cycles V p) : Prop :=
  ∀ Z : Cycles V p,
    H.cycleClass p Z = 0 → H.cycleClass p (A Z) = 0

/-- Kernel stability says equal cycle classes have equal transformed cycle
classes. -/
theorem class_congr_of_kernelStable
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A)
    {Z W : Cycles V p}
    (hZW : H.cycleClass p Z = H.cycleClass p W) :
    H.cycleClass p (A Z) = H.cycleClass p (A W) := by
  have hker : H.cycleClass p (Z - W) = 0 := by
    simp [hZW]
  have himage := hA (Z - W) hker
  rw [map_sub, map_sub] at himage
  exact eq_of_sub_eq_zero himage

/-- Canonical chosen representative of a class in the actual cycle-class
range. -/
noncomputable def rangeRepresentative
    (x : LinearMap.range (H.cycleClass p)) : Cycles V p :=
  Classical.choose x.2

@[simp]
theorem rangeRepresentative_spec
    (x : LinearMap.range (H.cycleClass p)) :
    H.cycleClass p (rangeRepresentative x) = x.1 :=
  Classical.choose_spec x.2

/-- Native operator descended to the actual cycle-class range. -/
noncomputable def rangeOperator
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ]
      LinearMap.range (H.cycleClass p) where
  toFun := fun x => ⟨H.cycleClass p (A (rangeRepresentative x)),
    ⟨A (rangeRepresentative x), rfl⟩⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    have hrep :
        H.cycleClass p (rangeRepresentative (x + y)) =
          H.cycleClass p (rangeRepresentative x + rangeRepresentative y) := by
      simp [rangeRepresentative_spec]
    have key : H.cycleClass p (A (rangeRepresentative (x + y))) =
        H.cycleClass p (A (rangeRepresentative x)) +
          H.cycleClass p (A (rangeRepresentative y)) := by
      rw [class_congr_of_kernelStable A hA hrep, map_add A, map_add]
    simp only [Submodule.coe_add]
    exact key
  map_smul' := by
    intro q x
    apply Subtype.ext
    have hrep :
        H.cycleClass p (rangeRepresentative (q • x)) =
          H.cycleClass p (q • rangeRepresentative x) := by
      simp [rangeRepresentative_spec]
    have key : H.cycleClass p (A (rangeRepresentative (q • x))) =
        q • H.cycleClass p (A (rangeRepresentative x)) := by
      rw [class_congr_of_kernelStable A hA hrep, map_smul A, map_smul]
    simp only [SetLike.val_smul, RingHom.id_apply]
    exact key

/-- The descended range operator has the expected action on every actual
cycle class. -/
theorem rangeOperator_rangeRestrict
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A)
    (Z : Cycles V p) :
    (rangeOperator A hA) ((H.cycleClass p).rangeRestrict Z) =
      (H.cycleClass p).rangeRestrict (A Z) := by
  apply Subtype.ext
  apply class_congr_of_kernelStable A hA
  exact rangeRepresentative_spec _

/-- Include the range operator back into ambient cohomology. -/
noncomputable def rangeOperatorIntoAmbient
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    LinearMap.range (H.cycleClass p) →ₗ[ℚ] Coh H p :=
  (LinearMap.range (H.cycleClass p)).subtype.comp (rangeOperator A hA)

/-- **ONE FIXED CLASS-RANGE RETRACTION FOR THE ENTIRE NATIVE ALGEBRA.**

This is chosen ONCE, not once per native word.  Its existence is the
linear splitting of the actual cycle-class image.  The Hodge statement,
basis-cycle representatives, and spectral completeness are not inputs. -/
noncomputable def classRangeRetraction :
    Coh H p →ₗ[ℚ] LinearMap.range (H.cycleClass p) :=
  Classical.choose (LinearMap.exists_extend
    (LinearMap.id : Module.End ℚ (LinearMap.range (H.cycleClass p))))

theorem classRangeRetraction_spec :
    (classRangeRetraction (V := V) (H := H) (p := p)).comp
      (LinearMap.range (H.cycleClass p)).subtype = LinearMap.id :=
  Classical.choose_spec (LinearMap.exists_extend
    (LinearMap.id : Module.End ℚ (LinearMap.range (H.cycleClass p))))

@[simp]
theorem classRangeRetraction_range
    (a : LinearMap.range (H.cycleClass p)) :
    classRangeRetraction (H := H) a.1 = a :=
  LinearMap.congr_fun classRangeRetraction_spec a

/-- **REBUILT CORE AMBIENT OPERATOR.**

Unlike the historical independently selected extension, this is the unique
extension prescribed by one fixed class-range retraction with ZERO action on
its complementary sector.  Its composition law is therefore coherent across
the full native operator algebra, not only on classes already in the image. -/
noncomputable def ambientOperator
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    Coh H p →ₗ[ℚ] Coh H p :=
  (rangeOperatorIntoAmbient A hA).comp
    (classRangeRetraction (H := H))

/-- The rebuilt ambient operator has exact naturality on genuine native
cycle classes, with no independent output extension selection. -/
theorem ambientOperator_comp_rangeSubtype
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    (ambientOperator A hA).comp
        (LinearMap.range (H.cycleClass p)).subtype =
      rangeOperatorIntoAmbient A hA := by
  apply LinearMap.ext
  intro a
  change rangeOperatorIntoAmbient A hA
      (classRangeRetraction (H := H) a.1) =
    rangeOperatorIntoAmbient A hA a
  rw [classRangeRetraction_range]

/-- **AUTOMATIC CYCLE-CLASS NATURALITY.**  The ambient operator manufactured
from a kernel-stable native operator has the exact commuting square. -/
theorem cycleClass_ambientOperator
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A)
    (Z : Cycles V p) :
    ambientOperator A hA (H.cycleClass p Z) =
      H.cycleClass p (A Z) := by
  have hcomp := LinearMap.congr_fun (ambientOperator_comp_rangeSubtype A hA)
    ((H.cycleClass p).rangeRestrict Z)
  have hrange := rangeOperator_rangeRestrict A hA Z
  simpa [rangeOperatorIntoAmbient, hrange] using hcomp

/-- Every kernel-stable native operator canonically gives a complete
cycle/cohomology operator pair. -/
noncomputable def toCycleClassOperatorPair
    (A : Cycles V p →ₗ[ℚ] Cycles V p)
    (hA : KernelStable (H := H) A) :
    CycleClassOperatorPair V H p where
  cycleOperator := A
  cohomologyOperator := ambientOperator A hA
  cycleClass_natural := by
    ext Z
    symm
    exact cycleClass_ambientOperator A hA Z

/-- Kernel-stable actual projective-correspondence operators therefore acquire
a canonical ambient cohomological realization. -/
noncomputable def projectiveKernelToOperatorPair
    (K : ProjectiveNativeKernel V p)
    (hK : KernelStable (H := H) K.operator) :
    CycleClassOperatorPair V H p :=
  toCycleClassOperatorPair K.operator hK

/-! ## Coherent descent on the actual range

Choosing an unrelated ambient extension for each operator does not establish
composition on the ambient space.  First descend on the actual range, then
use one fixed range retraction for every operator.  This constructs the exact
composition algebra and identifies all remaining ambient freedom.
-/

theorem rangeOperator_id :
    rangeOperator (H := H) (LinearMap.id : Module.End ℚ (Cycles V p))
      (fun _ hZ => hZ) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact rangeRepresentative_spec a

theorem rangeOperator_zero :
    rangeOperator (H := H) (0 : Module.End ℚ (Cycles V p)) (by intro Z hZ; simp) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp [rangeOperator]

theorem rangeOperator_add
    (A B : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) (hB : KernelStable (H := H) B)
    (hAB : KernelStable (H := H) (A + B)) :
    rangeOperator (H := H) (A + B) hAB =
      rangeOperator A hA + rangeOperator B hB := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp [rangeOperator, map_add]

theorem rangeOperator_smul
    (q : ℚ) (A : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A)
    (h' : KernelStable (H := H) (q • A)) :
    rangeOperator (H := H) (q • A) h' =
      q • rangeOperator A hA := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp [rangeOperator, map_smul]

theorem rangeOperator_comp
    (A B : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) (hB : KernelStable (H := H) B) :
    rangeOperator (H := H) (A.comp B) (fun Z hZ => hA (B Z) (hB Z hZ)) =
      (rangeOperator A hA).comp (rangeOperator B hB) := by
  apply LinearMap.ext
  intro a
  obtain ⟨Z, hZ⟩ := a.2
  have ha : (H.cycleClass p).rangeRestrict Z = a := Subtype.ext hZ
  rw [← ha]
  have hstep := rangeOperator_rangeRestrict (A.comp B)
    (fun Z hZ => hA (B Z) (hB Z hZ)) Z
  rw [hstep]
  simp only [LinearMap.comp_apply, rangeOperator_rangeRestrict]

/-- Ambient projection onto classes of actual native cycles. -/
noncomputable def classRangeProjection : Module.End ℚ (Coh H p) :=
  (LinearMap.range (H.cycleClass p)).subtype.comp
    (classRangeRetraction (H := H))

@[simp]
theorem classRangeProjection_range
    (a : LinearMap.range (H.cycleClass p)) :
    classRangeProjection (H := H) a.1 = a.1 := by
  simp [classRangeProjection]

theorem classRangeProjection_mem_range (alpha : Coh H p) :
    classRangeProjection (H := H) alpha ∈ LinearMap.range (H.cycleClass p) :=
  (classRangeRetraction (H := H) alpha).2

theorem classRangeProjection_idempotent :
    (classRangeProjection (V := V) (H := H) (p := p)).comp
      (classRangeProjection (H := H)) = classRangeProjection (H := H) := by
  apply LinearMap.ext
  intro alpha
  exact classRangeProjection_range (classRangeRetraction (H := H) alpha)

theorem classRangeProjection_eq_self_iff (alpha : Coh H p) :
    classRangeProjection (H := H) alpha = alpha ↔
      alpha ∈ LinearMap.range (H.cycleClass p) := by
  constructor
  · intro h
    rw [← h]
    exact classRangeProjection_mem_range alpha
  · intro h
    exact classRangeProjection_range ⟨alpha, h⟩

/-- The complement records the ambient extension freedom. -/
noncomputable def offRangeProjection : Module.End ℚ (Coh H p) :=
  LinearMap.id - classRangeProjection (H := H)

@[simp]
theorem offRangeProjection_range
    (a : LinearMap.range (H.cycleClass p)) :
    offRangeProjection (H := H) a.1 = 0 := by
  simp [offRangeProjection]

theorem ambient_range_decomposition (alpha : Coh H p) :
    classRangeProjection (H := H) alpha + offRangeProjection (H := H) alpha =
      alpha := by
  simp only [offRangeProjection, LinearMap.sub_apply, LinearMap.id_apply]
  abel

/-- Composition-coherent ambient action manufactured from native descent.
It is supported on the actual range and kills the chosen complement. -/
noncomputable def supportedAmbientOperator
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A) :
    Module.End ℚ (Coh H p) :=
  (LinearMap.range (H.cycleClass p)).subtype.comp
    ((rangeOperator A hA).comp (classRangeRetraction (H := H)))

theorem supportedAmbientOperator_mem_range
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A)
    (alpha : Coh H p) :
    supportedAmbientOperator A hA alpha ∈ LinearMap.range (H.cycleClass p) :=
  (rangeOperator A hA (classRangeRetraction (H := H) alpha)).2

theorem supportedAmbientOperator_cycleClass
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A)
    (Z : Cycles V p) :
    supportedAmbientOperator A hA (H.cycleClass p Z) =
      H.cycleClass p (A Z) := by
  have hret : classRangeRetraction (H := H) (H.cycleClass p Z) =
      (H.cycleClass p).rangeRestrict Z :=
    classRangeRetraction_range ((H.cycleClass p).rangeRestrict Z)
  simp only [supportedAmbientOperator, LinearMap.comp_apply, hret,
    rangeOperator_rangeRestrict] <;> rfl

theorem supportedAmbientOperator_id :
    supportedAmbientOperator (H := H) (LinearMap.id : Module.End ℚ (Cycles V p))
      (fun _ hZ => hZ) = classRangeProjection (H := H) := by
  simp [supportedAmbientOperator, rangeOperator_id, classRangeProjection]

theorem supportedAmbientOperator_zero :
    supportedAmbientOperator (H := H) (0 : Module.End ℚ (Cycles V p))
      (by intro Z hZ; simp) = 0 := by
  apply LinearMap.ext
  intro alpha
  simp [supportedAmbientOperator, rangeOperator_zero]

theorem supportedAmbientOperator_comp
    (A B : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) (hB : KernelStable (H := H) B) :
    supportedAmbientOperator (H := H) (A.comp B) (fun Z hZ => hA (B Z) (hB Z hZ)) =
      (supportedAmbientOperator A hA).comp (supportedAmbientOperator B hB) := by
  apply LinearMap.ext
  intro alpha
  simp [supportedAmbientOperator, LinearMap.comp_apply,
    classRangeRetraction_range, rangeOperator_comp]

theorem supportedAmbientOperator_add
    (A B : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) (hB : KernelStable (H := H) B) :
    supportedAmbientOperator (H := H) (A + B) (by intro Z hZ; simp [hA Z hZ, hB Z hZ]) =
      supportedAmbientOperator A hA + supportedAmbientOperator B hB := by
  apply LinearMap.ext
  intro alpha
  let hAB : KernelStable (H := H) (A + B) := by
    intro Z hZ
    simp [hA Z hZ, hB Z hZ]
  have hstep := LinearMap.congr_fun
    (rangeOperator_add (H := H) A B hA hB hAB)
    (classRangeRetraction (H := H) alpha)
  have hval := congrArg Subtype.val hstep
  simpa [supportedAmbientOperator, LinearMap.comp_apply] using hval

theorem supportedAmbientOperator_smul
    (q : ℚ) (A : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) :
    supportedAmbientOperator (H := H) (q • A) (by intro Z hZ; simp [hA Z hZ]) =
      q • supportedAmbientOperator A hA := by
  apply LinearMap.ext
  intro alpha
  let hqA : KernelStable (H := H) (q • A) := by
    intro Z hZ
    simp [hA Z hZ]
  have hstep := LinearMap.congr_fun
    (rangeOperator_smul (H := H) q A hA hqA)
    (classRangeRetraction (H := H) alpha)
  have hval := congrArg Subtype.val hstep
  simpa [supportedAmbientOperator, LinearMap.comp_apply] using hval

/-- **ALL AMBIENT EXTENSIONS, EXACTLY.** The coherent native core is fixed;
every remaining term factors through the chosen off-range projection.  This
also applies to the original independently chosen `ambientOperator`. -/
theorem ambientNatural_core_decomposition
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A)
    (T : Module.End ℚ (Coh H p))
    (hT : ∀ Z, T (H.cycleClass p Z) = H.cycleClass p (A Z)) :
    T = supportedAmbientOperator A hA + T.comp (offRangeProjection (H := H)) := by
  apply LinearMap.ext
  intro alpha
  have hcore : T (classRangeProjection (H := H) alpha) =
      supportedAmbientOperator A hA alpha := by
    change T (classRangeRetraction (H := H) alpha).1 =
      H.cycleClass p (A (rangeRepresentative (classRangeRetraction (H := H) alpha)))
    rw [← rangeRepresentative_spec (classRangeRetraction (H := H) alpha)]
    exact hT _
  calc
    T alpha = T (classRangeProjection (H := H) alpha +
        offRangeProjection (H := H) alpha) :=
      congrArg T (ambient_range_decomposition alpha).symm
    _ = supportedAmbientOperator A hA alpha +
        T (offRangeProjection (H := H) alpha) := by rw [map_add, hcore]
    _ = _ := rfl

theorem ambientOperator_core_decomposition
    (A : Module.End ℚ (Cycles V p)) (hA : KernelStable (H := H) A) :
    ambientOperator A hA = supportedAmbientOperator A hA +
      (ambientOperator A hA).comp (offRangeProjection (H := H)) :=
  ambientNatural_core_decomposition A hA (ambientOperator A hA)
    (cycleClass_ambientOperator A hA)

/-! ## Intrinsic repair of the original operator law

The historically independent ambient extension has now been replaced at its
DEFINITION SITE by the unique coherent extension that kills the fixed
off-range complement.  The already-derived supported operator is thus
extensionally the original one, and the original API inherits the full
composition law.
-/

/-- The original operator is now exactly the shared-retraction action,
rather than an unrelated independently chosen extension at each word. -/
theorem ambientOperator_eq_supported
    (A : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A) :
    ambientOperator A hA = supportedAmbientOperator A hA := by
  apply LinearMap.ext
  intro alpha
  rfl

/-- **FULL AMBIENT COMPOSITION COHERENCE FOR THE ORIGINAL API.**
The once-uncontrolled cohomology extension now respects native operator
composition on ALL cohomology states, including off-range ones. -/
theorem ambientOperator_comp_coherent
    (A B : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A)
    (hB : KernelStable (H := H) B) :
    ambientOperator (H := H) (A.comp B) (fun Z hZ => hA (B Z) (hB Z hZ)) =
      (ambientOperator A hA).comp (ambientOperator B hB) := by
  simp only [ambientOperator]
  exact supportedAmbientOperator_comp A B hA hB

/-- The native identity is ALWAYS mapped to its real cohomological corner
unit.  It can be promoted to the full ambient identity only under the
precise range-surjectivity condition proved below. -/
theorem ambientOperator_nativeIdentity_is_cornerUnit :
    ambientOperator (H := H)
      (LinearMap.id : Module.End ℚ (Cycles V p))
      (fun _ hZ => hZ) =
        classRangeProjection (H := H) := by
  have h1 : ambientOperator (H := H) (LinearMap.id : Module.End ℚ (Cycles V p))
      (fun _ hZ => hZ) = supportedAmbientOperator (H := H)
      (LinearMap.id : Module.End ℚ (Cycles V p)) (fun _ hZ => hZ) :=
    ambientOperator_eq_supported (LinearMap.id : Module.End ℚ (Cycles V p)) (fun _ hZ => hZ)
  rw [h1]
  exact supportedAmbientOperator_id

/-- **THE CORNER-UNIT OBSTRUCTION.**

The coherent ambient image of the native identity is the projection onto
actual algebraic classes, not necessarily the identity on ALL cohomology.
Those become equal if and only if the genuine native cycle-class range
already fills all ambient cohomology.

This is an unconditional mathematical reason a faithful native algebra
extension must not be mistaken for a unital representation of the full
ambient correspondence geometry.  A class outside the genuine native
range is *not* manufactured by rewriting the operator API. -/
theorem ambientOperator_id_eq_fullIdentity_iff_fullRange :
    ambientOperator (H := H)
      (LinearMap.id : Module.End ℚ (Cycles V p))
      (fun _ hZ => hZ) =
        (LinearMap.id : Module.End ℚ (Coh H p)) ↔
      ∀ alpha : Coh H p,
        alpha ∈ LinearMap.range (H.cycleClass p) := by
  rw [ambientOperator_nativeIdentity_is_cornerUnit]
  constructor
  · intro h alpha
    have hh := LinearMap.congr_fun h alpha
    exact (classRangeProjection_eq_self_iff alpha).1 hh
  · intro h
    apply LinearMap.ext
    intro alpha
    exact (classRangeProjection_eq_self_iff alpha).2 (h alpha)

#check ambientOperator_id_eq_fullIdentity_iff_fullRange
#print axioms ambientOperator_id_eq_fullIdentity_iff_fullRange

/-- The algebraic component of every defect is identically zero. -/
theorem classRangeProjection_offRange_zero (alpha : Coh H p) :
    classRangeProjection (H := H)
      (offRangeProjection (H := H) alpha) = 0 := by
  change classRangeProjection (H := H)
    (alpha - classRangeProjection (H := H) alpha) = 0
  rw [map_sub]
  have h := LinearMap.congr_fun
    (classRangeProjection_idempotent (V := V) (H := H) (p := p)) alpha
  rw [LinearMap.comp_apply] at h
  rw [h, sub_self]

/-- Every rebuilt native ambient motion annihilates the off-range complement
at the definition level.  No uncontrolled arbitrary extension survives. -/
theorem ambientOperator_offRange_zero
    (A : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A)
    (alpha : Coh H p) :
    ambientOperator A hA (offRangeProjection (H := H) alpha) = 0 := by
  have hz :
      classRangeRetraction (H := H)
        (offRangeProjection (H := H) alpha) = 0 := by
    apply Subtype.ext
    exact classRangeProjection_offRange_zero alpha
  simp [ambientOperator, hz]

#check ambientOperator_comp_coherent
#print axioms ambientOperator_comp_coherent

/-! ## The intrinsic cohomological defect sector

The native class/kernel splitting does not yet separate what Hodge can see
from what native geometry can actually realize.  The following strengthens
the ambient laws into one **exact class/defect splitting**, using the SAME
fixed retraction for every native operator.

Unlike a new matrix-unit postulate, this sector exists before any Hodge
surjectivity assertion and before selecting a separator ghost.
-/

/-- The off-range part vanishes precisely for genuine algebraic classes.
This is the exact, unassumed boundary between native geometry and the
unreached ambient cohomology directions. -/
theorem offRangeProjection_eq_zero_iff_range (alpha : Coh H p) :
    offRangeProjection (H := H) alpha = 0 ↔
      alpha ∈ LinearMap.range (H.cycleClass p) := by
  change alpha - classRangeProjection (H := H) alpha = 0 ↔ _
  rw [sub_eq_zero, eq_comm]
  exact classRangeProjection_eq_self_iff alpha

/-- The defect component is an honest idempotent geometric projection,
not an arbitrary coordinate reassignment. -/
theorem offRangeProjection_idempotent :
    (offRangeProjection (V := V) (H := H) (p := p)).comp
      (offRangeProjection (H := H)) = offRangeProjection (H := H) := by
  apply LinearMap.ext
  intro alpha
  change offRangeProjection (H := H)
    (alpha - classRangeProjection (H := H) alpha) =
      offRangeProjection (H := H) alpha
  rw [map_sub]
  have hr :
      offRangeProjection (H := H)
        (classRangeProjection (H := H) alpha) = 0 :=
    offRangeProjection_range
      (⟨classRangeProjection (H := H) alpha,
        classRangeProjection_mem_range alpha⟩ :
        LinearMap.range (H.cycleClass p))
  rw [hr, sub_zero]

/-- A class whose algebraic projection vanishes is already a pure defect. -/
theorem offRangeProjection_eq_self_of_classProjection_zero
    (alpha : Coh H p)
    (h : classRangeProjection (H := H) alpha = 0) :
    offRangeProjection (H := H) alpha = alpha := by
  simp [offRangeProjection, h]

/-- Genuine ambient defect space: kernel of the *algebraic-range*
projection, not an independently invented Hodge coordinate type. -/
abbrev NativeCohomologicalDefect :=
  LinearMap.ker (classRangeProjection (V := V) (H := H) (p := p))

/-- The complete missing-class component, taking values in its intrinsic
subspace. -/
noncomputable def cohomologicalDefectCoordinate :
    Coh H p →ₗ[ℚ] NativeCohomologicalDefect (V := V) (H := H) (p := p) where
  toFun alpha :=
    ⟨offRangeProjection (H := H) alpha,
      classRangeProjection_offRange_zero alpha⟩
  map_add' := by
    intro alpha beta
    apply Subtype.ext
    exact map_add (offRangeProjection (H := H)) alpha beta
  map_smul' := by
    intro q alpha
    apply Subtype.ext
    exact map_smul (offRangeProjection (H := H)) q alpha

@[simp]
theorem cohomologicalDefectCoordinate_range
    (a : LinearMap.range (H.cycleClass p)) :
    cohomologicalDefectCoordinate (H := H) a.1 = 0 := by
  apply Subtype.ext
  exact offRangeProjection_range a

@[simp]
theorem cohomologicalDefectCoordinate_pureDefect
    (a : NativeCohomologicalDefect (V := V) (H := H) (p := p)) :
    cohomologicalDefectCoordinate (H := H) a.1 = a := by
  apply Subtype.ext
  exact offRangeProjection_eq_self_of_classProjection_zero a.1 a.2

/-- **UNCONDITIONAL AMBIENT CLASS/DEFECT SPLIT.**
All rational cohomology is uniquely a class of genuine native cycles plus
an exact defect component.  Neither side is replaced by a hypothetical
source/target Hodge representative.  This is the missing geometric
normal form dual to the native class/kernel splitting. -/
noncomputable def ambientClassDefectEquiv :
    Coh H p ≃ₗ[ℚ]
      (LinearMap.range (H.cycleClass p) ×
        NativeCohomologicalDefect (V := V) (H := H) (p := p)) where
  toLinearMap := {
    toFun := fun alpha =>
      (classRangeRetraction (H := H) alpha,
        cohomologicalDefectCoordinate (H := H) alpha)
    map_add' := by intro alpha beta; apply Prod.ext <;> simp
    map_smul' := by intro q alpha; apply Prod.ext <;> simp
  }
  invFun a := a.1.1 + a.2.1
  left_inv := by
    intro alpha
    exact ambient_range_decomposition alpha
  right_inv := by
    intro a
    apply Prod.ext
    · change classRangeRetraction (H := H) (a.1.1 + a.2.1) = a.1
      rw [map_add, classRangeRetraction_range]
      have hz : classRangeRetraction (H := H) a.2.1 = 0 := by
        apply Subtype.ext
        exact a.2.2
      rw [hz, add_zero]
    · change cohomologicalDefectCoordinate (H := H)
        (a.1.1 + a.2.1) = a.2
      rw [map_add, cohomologicalDefectCoordinate_range,
        cohomologicalDefectCoordinate_pureDefect, zero_add]

/-- **NO-GENERATION LAW FOR ALL NATIVE OPERATORS.**
This is deliberately stronger than the kernel-stability assumption:
EVEN an arbitrary native operator cannot manufacture a nonzero
cohomological defect by applying cycle class to its output.  Compositions,
rational words, projective correspondences and arbitrary native kernels are
therefore all confined to the same actual algebraic range. -/
theorem everyNativeOperator_has_zero_defect
    (A : Module.End ℚ (Cycles V p)) (Z : Cycles V p) :
    cohomologicalDefectCoordinate (H := H) (H.cycleClass p (A Z)) = 0 := by
  exact cohomologicalDefectCoordinate_range
    ((H.cycleClass p).rangeRestrict (A Z))

/-- Any ambient class with a detected defect cannot be the image of any
native operator evaluated on any native cycle.  No input family of larger
native operators removes this boundary without changing the cycle-class
geometry itself. -/
theorem nonzero_defect_blocks_every_native_operator
    (alpha : Coh H p)
    (hbad : cohomologicalDefectCoordinate (H := H) alpha ≠ 0)
    (A : Module.End ℚ (Cycles V p)) (Z : Cycles V p) :
    H.cycleClass p (A Z) ≠ alpha := by
  intro h
  apply hbad
  rw [← h]
  exact everyNativeOperator_has_zero_defect A Z

/-- The coherent ambient action generated by ANY kernel-stable native
operator has zero defect on every ambient input.  This explains why merely
extending the native algebra to all cohomology cannot add a missing class. -/
theorem supportedAmbientOperator_defect_zero
    (A : Module.End ℚ (Cycles V p))
    (hA : KernelStable (H := H) A)
    (alpha : Coh H p) :
    cohomologicalDefectCoordinate (H := H)
      (supportedAmbientOperator A hA alpha) = 0 := by
  apply Subtype.ext
  change offRangeProjection (H := H)
    (supportedAmbientOperator A hA alpha) = 0
  exact (offRangeProjection_eq_zero_iff_range _).2
    (supportedAmbientOperator_mem_range A hA alpha)

/-- **EXACT HODGE FRONTIER, BEFORE CHOOSING A GHOST.**
The Hodge-weight conclusion holds iff the ACTUAL intrinsic defect coordinate
vanishes on its whole Hodge fiber.  This is an exact test, not a premise being
relabelled as a theorem. -/
theorem hodgeWeight_iff_intrinsicDefect_zero :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) ↔
    ∀ alpha : Coh H p,
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        cohomologicalDefectCoordinate (H := H) alpha = 0 := by
  constructor
  · intro h alpha halpha
    apply Subtype.ext
    change offRangeProjection (H := H) alpha = 0
    exact (offRangeProjection_eq_zero_iff_range alpha).2 (h halpha)
  · intro h alpha halpha
    have hz := h alpha halpha
    have hz' : offRangeProjection (H := H) alpha = 0 :=
      congrArg Subtype.val hz
    exact (offRangeProjection_eq_zero_iff_range alpha).1 hz'

#check ambientClassDefectEquiv
#check everyNativeOperator_has_zero_defect
#check nonzero_defect_blocks_every_native_operator
#check supportedAmbientOperator_defect_zero
#check hodgeWeight_iff_intrinsicDefect_zero

#print axioms ambientClassDefectEquiv
#print axioms everyNativeOperator_has_zero_defect
#print axioms hodgeWeight_iff_intrinsicDefect_zero

#print axioms classRangeRetraction
#print axioms supportedAmbientOperator_comp
#print axioms ambientNatural_core_decomposition

#check KernelStable
#check class_congr_of_kernelStable
#check rangeOperator
#check ambientOperator
#check cycleClass_ambientOperator
#check toCycleClassOperatorPair
#check projectiveKernelToOperatorPair

#print axioms class_congr_of_kernelStable
#print axioms rangeOperator_rangeRestrict
#print axioms cycleClass_ambientOperator
#print axioms toCycleClassOperatorPair
#print axioms projectiveKernelToOperatorPair

end GSTClassicalHodgeNativeOperatorCohomologyRealization

