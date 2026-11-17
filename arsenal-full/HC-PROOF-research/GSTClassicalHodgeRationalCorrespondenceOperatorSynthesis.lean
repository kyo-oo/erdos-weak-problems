import GSTClassicalHodgeFiniteClosedCorrespondenceOperator
import GSTClassicalHodgeCycleOperatorNaturality

/-!
# GST CLASSICAL HODGE — RATIONAL CORRESPONDENCE OPERATOR SYNTHESIS

The correct algebraic correspondence carrier is rational-linear.  This file
shows that exact cycle-class-natural operator pairs are closed under rational
linear synthesis and then applies that closure to finite rational combinations
of genuine one-sided finite closed correspondences.

No new geometric realization equation is assumed for the sum.  Each primitive
correspondence K must independently realize its own cohomological operator on
point cycles.  The global rational correspondence operator is then derived by
linearity from the already-proved pointwise-to-full naturality theorem.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeRationalCorrespondenceOperatorSynthesis

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCycleOperatorNaturality
open GSTClassicalHodgeFiniteClosedCorrespondence
open GSTClassicalHodgeFiniteClosedCorrespondenceOperator
open GSTClassicalHodgeFiniteClosedCorrespondence.FiniteClosedCorrespondence

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

abbrev Pair := CycleClassOperatorPair V H p

namespace Pair

/-- Zero natural operator pair. -/
noncomputable def zero : Pair (V := V) (H := H) (p := p) where
  cycleOperator := 0
  cohomologyOperator := 0
  cycleClass_natural := by ext Z; simp

/-- Sum of two exact natural operator pairs. -/
noncomputable def add
    (A B : Pair (V := V) (H := H) (p := p)) :
    Pair (V := V) (H := H) (p := p) where
  cycleOperator := A.cycleOperator + B.cycleOperator
  cohomologyOperator := A.cohomologyOperator + B.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [A.cycleClass_cycleOperator, B.cycleClass_cycleOperator]

/-- Rational scaling of an exact natural operator pair. -/
noncomputable def smul
    (q : ℚ)
    (A : Pair (V := V) (H := H) (p := p)) :
    Pair (V := V) (H := H) (p := p) where
  cycleOperator := q • A.cycleOperator
  cohomologyOperator := q • A.cohomologyOperator
  cycleClass_natural := by
    ext Z
    simp [A.cycleClass_cycleOperator]

@[simp] theorem zero_cycleOperator :
    (zero (V := V) (H := H) (p := p)).cycleOperator = 0 := rfl

@[simp] theorem zero_cohomologyOperator :
    (zero (V := V) (H := H) (p := p)).cohomologyOperator = 0 := rfl

@[simp] theorem add_cycleOperator
    (A B : Pair (V := V) (H := H) (p := p)) :
    (add A B).cycleOperator = A.cycleOperator + B.cycleOperator := rfl

@[simp] theorem add_cohomologyOperator
    (A B : Pair (V := V) (H := H) (p := p)) :
    (add A B).cohomologyOperator = A.cohomologyOperator + B.cohomologyOperator := rfl

@[simp] theorem smul_cycleOperator
    (q : ℚ) (A : Pair (V := V) (H := H) (p := p)) :
    (smul q A).cycleOperator = q • A.cycleOperator := rfl

@[simp] theorem smul_cohomologyOperator
    (q : ℚ) (A : Pair (V := V) (H := H) (p := p)) :
    (smul q A).cohomologyOperator = q • A.cohomologyOperator := rfl

/-- Structure equality from equality of the two operator data fields; the
naturality proof component is proof-irrelevant. -/
theorem ext_data
    {f g : Pair (V := V) (H := H) (p := p)}
    (ho : f.cycleOperator = g.cycleOperator)
    (hh : f.cohomologyOperator = g.cohomologyOperator) :
    f = g := by
  rcases f with ⟨fo, fh, _⟩
  rcases g with ⟨go, gh, _⟩
  have ho' : fo = go := ho
  have hh' : fh = gh := hh
  subst ho'
  subst hh'
  rfl

end Pair

/-- Componentwise algebraic structure on exact natural operator pairs: the
operator and cohomology components are combined like module endomorphisms,
and the naturality proof component is closed under these operations. -/
instance instAddCommMonoidPair :
    AddCommMonoid (Pair (V := V) (H := H) (p := p)) where
  add := Pair.add
  zero := Pair.zero
  add_assoc A B C := Pair.ext_data
    (by
      show (Pair.add (Pair.add A B) C).cycleOperator =
        (Pair.add A (Pair.add B C)).cycleOperator
      rw [Pair.add_cycleOperator, Pair.add_cycleOperator,
        Pair.add_cycleOperator, Pair.add_cycleOperator, add_assoc])
    (by
      show (Pair.add (Pair.add A B) C).cohomologyOperator =
        (Pair.add A (Pair.add B C)).cohomologyOperator
      rw [Pair.add_cohomologyOperator, Pair.add_cohomologyOperator,
        Pair.add_cohomologyOperator, Pair.add_cohomologyOperator, add_assoc])
  add_comm A B := Pair.ext_data
    (by
      show (Pair.add A B).cycleOperator = (Pair.add B A).cycleOperator
      rw [Pair.add_cycleOperator, Pair.add_cycleOperator, add_comm])
    (by
      show (Pair.add A B).cohomologyOperator = (Pair.add B A).cohomologyOperator
      rw [Pair.add_cohomologyOperator, Pair.add_cohomologyOperator, add_comm])
  zero_add A := Pair.ext_data
    (by
      show (Pair.add Pair.zero A).cycleOperator = A.cycleOperator
      rw [Pair.add_cycleOperator, Pair.zero_cycleOperator, zero_add])
    (by
      show (Pair.add Pair.zero A).cohomologyOperator = A.cohomologyOperator
      rw [Pair.add_cohomologyOperator, Pair.zero_cohomologyOperator, zero_add])
  add_zero A := Pair.ext_data
    (by
      show (Pair.add A Pair.zero).cycleOperator = A.cycleOperator
      rw [Pair.add_cycleOperator, Pair.zero_cycleOperator, add_zero])
    (by
      show (Pair.add A Pair.zero).cohomologyOperator = A.cohomologyOperator
      rw [Pair.add_cohomologyOperator, Pair.zero_cohomologyOperator, add_zero])
  nsmul := fun n A => Pair.smul (n : ℚ) A
  nsmul_zero := by
    intro A
    exact Pair.ext_data
      (by
        show (Pair.smul (0 : ℚ) A).cycleOperator = (Pair.zero).cycleOperator
        rw [Pair.smul_cycleOperator, Pair.zero_cycleOperator, zero_smul])
      (by
        show (Pair.smul (0 : ℚ) A).cohomologyOperator = (Pair.zero).cohomologyOperator
        rw [Pair.smul_cohomologyOperator, Pair.zero_cohomologyOperator, zero_smul])
  nsmul_succ := by
    intro n A
    exact Pair.ext_data
      (by
        show (Pair.smul ((n + 1 : ℕ) : ℚ) A).cycleOperator =
          (Pair.add (Pair.smul (n : ℚ) A) A).cycleOperator
        rw [Pair.smul_cycleOperator, Pair.add_cycleOperator, Pair.smul_cycleOperator,
          Nat.cast_succ, add_smul, one_smul])
      (by
        show (Pair.smul ((n + 1 : ℕ) : ℚ) A).cohomologyOperator =
          (Pair.add (Pair.smul (n : ℚ) A) A).cohomologyOperator
        rw [Pair.smul_cohomologyOperator, Pair.add_cohomologyOperator,
          Pair.smul_cohomologyOperator, Nat.cast_succ, add_smul, one_smul])

theorem smul_zero_pair (A : Pair (V := V) (H := H) (p := p)) :
    Pair.smul (0 : ℚ) A = 0 := Pair.ext_data
  (by
    show (Pair.smul (0 : ℚ) A).cycleOperator =
      (Pair.zero (V := V) (H := H) (p := p)).cycleOperator
    rw [Pair.smul_cycleOperator, Pair.zero_cycleOperator, zero_smul])
  (by
    show (Pair.smul (0 : ℚ) A).cohomologyOperator =
      (Pair.zero (V := V) (H := H) (p := p)).cohomologyOperator
    rw [Pair.smul_cohomologyOperator, Pair.zero_cohomologyOperator, zero_smul])

theorem add_smul_pair (q₁ q₂ : ℚ) (A : Pair (V := V) (H := H) (p := p)) :
    Pair.smul (q₁ + q₂) A =
      Pair.add (Pair.smul q₁ A) (Pair.smul q₂ A) := Pair.ext_data
  (by
    show (Pair.smul (q₁ + q₂) A).cycleOperator =
      (Pair.add (Pair.smul q₁ A) (Pair.smul q₂ A)).cycleOperator
    rw [Pair.smul_cycleOperator, Pair.add_cycleOperator,
      Pair.smul_cycleOperator, Pair.smul_cycleOperator, add_smul])
  (by
    show (Pair.smul (q₁ + q₂) A).cohomologyOperator =
      (Pair.add (Pair.smul q₁ A) (Pair.smul q₂ A)).cohomologyOperator
    rw [Pair.smul_cohomologyOperator, Pair.add_cohomologyOperator,
      Pair.smul_cohomologyOperator, Pair.smul_cohomologyOperator, add_smul])

/-- Exact operator pair carried by one genuine one-sided finite closed
correspondence and its independently verified pointwise Betti realization. -/
noncomputable def primitivePair
    (K : FiniteClosedCorrespondence V)
    (T : RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p))
    (hT : K.RealizesAmbientOnPoints (H := H) T) :
    Pair (V := V) (H := H) (p := p) :=
  K.toCycleClassOperatorPair T hT

/-- Fold a finite rational correspondence cycle into one exact natural
operator pair.  The input `T` and `hT` are primitive geometric realization
proofs; naturality of the rational sum is derived. -/
noncomputable def rationalPair
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K)) :
    Pair (V := V) (H := H) (p := p) := by
  classical
  exact A.sum fun K q => Pair.smul q (primitivePair K (T K) (hT K))

/-- Native operator of the synthesized pair is exactly the rational sum of
native correspondence operators. -/
theorem rationalPair_cycleOperator
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K)) :
    (rationalPair A T hT).cycleOperator =
      correspondenceCycleNativeOperator A p := by
  classical
  induction A using Finsupp.induction with
  | zero =>
      show (Pair.zero (V := V) (H := H) (p := p)).cycleOperator = 0
      rw [Pair.zero_cycleOperator]
  | single_add K q A hsup hne ih =>
      have h0 : ∀ K : FiniteClosedCorrespondence V,
          Pair.smul (0 : ℚ) (primitivePair K (T K) (hT K)) = 0 :=
        fun K => smul_zero_pair _
      have h1 : ∀ (K : FiniteClosedCorrespondence V) (q₁ q₂ : ℚ),
          Pair.smul (q₁ + q₂) (primitivePair K (T K) (hT K)) =
            Pair.add (Pair.smul q₁ (primitivePair K (T K) (hT K)))
              (Pair.smul q₂ (primitivePair K (T K) (hT K))) :=
        fun K q₁ q₂ => add_smul_pair q₁ q₂ _
      have h0' : ∀ K : FiniteClosedCorrespondence V,
          (fun K q => q • K.nativeOperator p) K (0 : ℚ) = 0 :=
        fun K => zero_smul _ _
      have h1' : ∀ (K : FiniteClosedCorrespondence V) (q₁ q₂ : ℚ),
          (fun K q => q • K.nativeOperator p) K (q₁ + q₂) =
            (fun K q => q • K.nativeOperator p) K q₁ +
              (fun K q => q • K.nativeOperator p) K q₂ :=
        fun K q₁ q₂ => add_smul q₁ q₂ _
      have ih' : (A.sum fun K q =>
          Pair.smul q (K.toCycleClassOperatorPair (T K) (hT K))).cycleOperator =
          A.sum fun K q => q • K.nativeOperator p := ih
      show ((Finsupp.single K q + A).sum
          fun K q => Pair.smul q (primitivePair K (T K) (hT K))).cycleOperator =
        correspondenceCycleNativeOperator (Finsupp.single K q + A) p
      rw [Finsupp.sum_add_index' h0 h1]
      have hR : correspondenceCycleNativeOperator (Finsupp.single K q + A) p =
          (Finsupp.single K q).sum (fun K q => q • K.nativeOperator p) +
            A.sum (fun K q => q • K.nativeOperator p) := by
        show ((Finsupp.single K q + A).sum
            fun K q => q • K.nativeOperator p) =
          (Finsupp.single K q).sum (fun K q => q • K.nativeOperator p) +
            A.sum (fun K q => q • K.nativeOperator p)
        exact Finsupp.sum_add_index' h0' h1'
      rw [hR]
      show (Pair.add ((Finsupp.single K q).sum
            fun K q => Pair.smul q (primitivePair K (T K) (hT K)))
          (A.sum fun K q => Pair.smul q (primitivePair K (T K) (hT K)))).cycleOperator =
        (Finsupp.single K q).sum (fun K q => q • K.nativeOperator p) +
          A.sum (fun K q => q • K.nativeOperator p)
      simp only [Pair.add_cycleOperator,
        Finsupp.sum_single_index (a := K) (b := q)
          (h := fun K' q' => Pair.smul q'
            (K'.toCycleClassOperatorPair (T K') (hT K')))
          (h0 K),
        Finsupp.sum_single_index (a := K) (b := q)
          (h := fun K' q' => q' • K'.nativeOperator p)
          (h0' K), Pair.smul_cycleOperator,
        primitivePair, toCycleClassOperatorPair_cycleOperator, ih']

/-- The cohomological action is the matching rational sum of the independently
realized primitive correspondence actions. -/
theorem rationalPair_cohomologyOperator
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K)) :
    (rationalPair A T hT).cohomologyOperator =
      A.sum (fun K q => q • T K) := by
  classical
  induction A using Finsupp.induction with
  | zero =>
      show (Pair.zero (V := V) (H := H) (p := p)).cohomologyOperator = 0
      rw [Pair.zero_cohomologyOperator]
  | single_add K q A hsup hne ih =>
      have h0 : ∀ K : FiniteClosedCorrespondence V,
          Pair.smul (0 : ℚ) (primitivePair K (T K) (hT K)) = 0 :=
        fun K => smul_zero_pair _
      have h1 : ∀ (K : FiniteClosedCorrespondence V) (q₁ q₂ : ℚ),
          Pair.smul (q₁ + q₂) (primitivePair K (T K) (hT K)) =
            Pair.add (Pair.smul q₁ (primitivePair K (T K) (hT K)))
              (Pair.smul q₂ (primitivePair K (T K) (hT K))) :=
        fun K q₁ q₂ => add_smul_pair q₁ q₂ _
      have h0' : ∀ K : FiniteClosedCorrespondence V,
          (fun K q => q • T K) K (0 : ℚ) = 0 :=
        fun K => zero_smul _ _
      have h1' : ∀ (K : FiniteClosedCorrespondence V) (q₁ q₂ : ℚ),
          (fun K q => q • T K) K (q₁ + q₂) =
            (fun K q => q • T K) K q₁ + (fun K q => q • T K) K q₂ :=
        fun K q₁ q₂ => add_smul q₁ q₂ _
      have ih' : (A.sum fun K q =>
          Pair.smul q (K.toCycleClassOperatorPair (T K) (hT K))).cohomologyOperator =
          A.sum fun K q => q • T K := ih
      show ((Finsupp.single K q + A).sum
          fun K q => Pair.smul q (primitivePair K (T K) (hT K))).cohomologyOperator =
        (Finsupp.single K q + A).sum fun K q => q • T K
      rw [Finsupp.sum_add_index' h0 h1, Finsupp.sum_add_index' h0' h1']
      show (Pair.add ((Finsupp.single K q).sum
            fun K q => Pair.smul q (primitivePair K (T K) (hT K)))
          (A.sum fun K q => Pair.smul q (primitivePair K (T K) (hT K)))).cohomologyOperator =
        (Finsupp.single K q).sum (fun K q => q • T K) +
          A.sum (fun K q => q • T K)
      simp only [Pair.add_cohomologyOperator,
        Finsupp.sum_single_index (a := K) (b := q)
          (h := fun K' q' => Pair.smul q'
            (K'.toCycleClassOperatorPair (T K') (hT K')))
          (h0 K),
        Finsupp.sum_single_index (a := K) (b := q)
          (h := fun K' q' => q' • T K')
          (h0' K), Pair.smul_cohomologyOperator,
        primitivePair]
      rw [show (K.toCycleClassOperatorPair (T K) (hT K)).cohomologyOperator = T K from rfl,
        ih']

/-- Direct naturality formula for the synthesized rational correspondence
cycle. -/
theorem rational_cycleClass_natural
    (A : RationalClosedCorrespondenceCycle V)
    (T : ∀ K : FiniteClosedCorrespondence V,
      RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
        RationalSingularCohomology H.analytification (2 * p))
    (hT : ∀ K : FiniteClosedCorrespondence V,
      K.RealizesAmbientOnPoints (H := H) (T K))
    (Z : codimensionCycles V.X p) :
    H.cycleClass p (correspondenceCycleNativeOperator A p Z) =
      (A.sum (fun K q => q • T K)) (H.cycleClass p Z) := by
  let P := rationalPair A T hT
  have h := P.cycleClass_cycleOperator Z
  rw [rationalPair_cycleOperator A T hT,
    rationalPair_cohomologyOperator A T hT] at h
  exact h

#check Pair.zero
#check Pair.add
#check Pair.smul
#check primitivePair
#check rationalPair
#check rationalPair_cycleOperator
#check rationalPair_cohomologyOperator
#check rational_cycleClass_natural

#print axioms rational_cycleClass_natural

end GSTClassicalHodgeRationalCorrespondenceOperatorSynthesis
