import GSTClassicalHodgeCMCoefficientDescentCore
import GSTClassicalHodgeExactClayStatement
import GSTUniversalChowRetractToTarget
import GSTClassicalHodgeCrossCarrierGeometricTransfer

/-!
# Rational algebraic cycle recovery from arbitrary coefficient extensions

This bridges the general field-extension descent lemma to HC-PROOF's actual
projective codimension cycles and rational singular Betti cohomology.

If a rational Betti class is a FINITE extension-linear combination of genuine
native cycle classes, we construct an actual RATIONAL native algebraic cycle
with exactly that class. No rationality assumption on the extension
coefficients and no finite-degree/Galois hypothesis is necessary.

It directly addresses the coefficient-descent part of the CM surface proof.
The hypothesis requires extension-coordinate identities for given concrete
cycles; it does not assert that arbitrary Hodge classes satisfy them.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 35000000
set_option maxRecDepth 900000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeCMCoefficientDescentCore
open GSTUniversalChowRetractToTarget

namespace GSTClassicalHodgeCMNativeRationalDescent

variable {K : Type*} [Field K] [Algebra ℚ K]
variable {J : Type*}
variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {q : Nat}

/-- From an extension-linear representation by native algebraic cycles,
construct a RATIONAL native algebraic cycle representing the same class.
All geometric cycles and their cohomology classes are genuine repository
objects. Only the coefficients are allowed to lie in K. -/
theorem rational_native_cycle_of_extended_span
    (s : Finset J)
    (cycles : J → codimensionCycles V.X q)
    (coefficient : J → K)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (hExtended :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2 * q))
      ∀ i : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2 * q)),
        algebraMap ℚ K ((b.repr alpha) i) =
          ∑ j ∈ s,
            coefficient j * algebraMap ℚ K
              ((b.repr (H.cycleClass q (cycles j))) i)) :
    ∃ Z : codimensionCycles V.X q,
      H.cycleClass q Z = alpha := by
  let b := Module.Free.chooseBasis ℚ
    (RationalSingularCohomology H.analytification (2 * q))
  obtain ⟨d, hd⟩ :=
    finite_span_descends (K := K)
      (s := s) coefficient
      (fun j i => (b.repr (H.cycleClass q (cycles j))) i)
      (fun i => (b.repr alpha) i) hExtended
  let Z : codimensionCycles V.X q :=
    ∑ j ∈ s, d j • cycles j
  refine ⟨Z, ?_⟩
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  calc
    (b.repr (H.cycleClass q Z)) i =
      ∑ j ∈ s,
        d j * (b.repr (H.cycleClass q (cycles j))) i := by
          simp [Z, map_sum, map_smul, Finset.sum_apply, smul_eq_mul]
    _ = (b.repr alpha) i := (hd i).symm

/-- A successful CM extension-coefficient construction gives membership
in the genuine range of the rational native cycle-class map. -/
theorem native_range_of_extended_span
    (s : Finset J)
    (cycles : J → codimensionCycles V.X q)
    (coefficient : J → K)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (hExtended :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2 * q))
      ∀ i : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2 * q)),
        algebraMap ℚ K ((b.repr alpha) i) =
          ∑ j ∈ s,
            coefficient j * algebraMap ℚ K
              ((b.repr (H.cycleClass q (cycles j))) i)) :
    alpha ∈ LinearMap.range (H.cycleClass q) := by
  exact rational_native_cycle_of_extended_span s cycles coefficient alpha hExtended

/-! ## A fixed explicit cycle constructor

The existential theorem above can be strengthened to a single
noncomputable output cycle whose rational coefficients are obtained
by a normalized linear projection K -> Q, rather than by selecting
an arbitrary representative of a Hodge class. -/

/-- One globally fixed rational-linear coefficient projection on K. -/
noncomputable def rationalCoefficientProjection : K →ₗ[ℚ] ℚ :=
  Classical.choose (exists_projection (K := K))

@[simp]
theorem rationalCoefficientProjection_one :
    rationalCoefficientProjection (K := K) 1 = 1 :=
  Classical.choose_spec (exists_projection (K := K))

/-- The constructed rational algebraic cycle, with every source cycle
and coefficient supplied independently of the target cohomology class. -/
noncomputable def rationalCycleFromExtensionCoefficients
    (s : Finset J)
    (cycles : J → codimensionCycles V.X q)
    (coeff : J → K) :
    codimensionCycles V.X q :=
  ∑ j ∈ s, rationalCoefficientProjection (K := K) (coeff j) • cycles j

/-- Exact native cycle-class specification of the explicit constructor. -/
theorem rationalCycleFromExtensionCoefficients_spec
    (s : Finset J)
    (cycles : J → codimensionCycles V.X q)
    (coeff : J → K)
    (alpha : RationalSingularCohomology H.analytification (2 * q))
    (hExtended :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2 * q))
      ∀ i : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2 * q)),
        algebraMap ℚ K ((b.repr alpha) i) =
          ∑ j ∈ s, coeff j * algebraMap ℚ K
            ((b.repr (H.cycleClass q (cycles j))) i)) :
    H.cycleClass q
      (rationalCycleFromExtensionCoefficients s cycles coeff) = alpha := by
  let b := Module.Free.chooseBasis ℚ
    (RationalSingularCohomology H.analytification (2 * q))
  let eps := rationalCoefficientProjection (K := K)
  have heps : eps 1 = 1 := rationalCoefficientProjection_one
  have hcoeff (i : Module.Free.ChooseBasisIndex ℚ
      (RationalSingularCohomology H.analytification (2 * q))) :
      (b.repr alpha) i =
        ∑ j ∈ s, eps (coeff j) *
          (b.repr (H.cycleClass q (cycles j))) i := by
    calc
      (b.repr alpha) i =
          eps (algebraMap ℚ K ((b.repr alpha) i)) := by
            symm
            exact projection_fixes_rat eps heps _
      _ = eps (∑ j ∈ s, coeff j *
          algebraMap ℚ K ((b.repr (H.cycleClass q (cycles j))) i)) := by
            rw [hExtended i]
      _ = ∑ j ∈ s, eps (coeff j) *
          (b.repr (H.cycleClass q (cycles j))) i := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro j hj
            exact projection_mul_rat eps (coeff j) _
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  calc
    (b.repr (H.cycleClass q
      (rationalCycleFromExtensionCoefficients s cycles coeff))) i =
        ∑ j ∈ s, eps (coeff j) *
          (b.repr (H.cycleClass q (cycles j))) i := by
            simp [rationalCycleFromExtensionCoefficients, eps,
              map_sum, map_smul, Finset.sum_apply, smul_eq_mul]
    _ = (b.repr alpha) i := (hcoeff i).symm


/-! ## GST heterogeneous multiverse: true CM-field Chow descent

This module now combines every part of the all-world native route:
different actual smooth projective source SCHEMES, differing Hodge
codimensions, genuine Chow/Gysin geometric transfers into an arbitrary
target X, and unrestricted field-extension coefficients K/Q.

Unlike the earlier all-source-completeness theorem, this constructor
requires only FINITELY MANY actual source algebraic cycles whose
extension-valued geometric Betti combination equals this particular
rational Hodge target. It does not require full Hodge algebraicity
on ANY source and does not assume a native target preimage.

The scalar-field descent uses the exact normalized Q-linear retraction
K -> Q; thus every such CM/cosmology/NM witness becomes a genuinely
RATIONAL target Chow cycle with the CORRECT source codimension shifts.
The extension-coordinate equality is an independent geometric
period/CM eigenspace computation to be proved for each target class.
-/

/-- Actual cross-variety CM-field native construction: finite sources
may have unrelated dimensions and codimensions, and coefficients
may lie in ANY field extension of the rationals. -/
theorem native_target_cycle_of_multisource_CM_field_spanning
    {X : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData X}
    (p : ℕ)
    {ι : Type*} [Fintype ι]
    {K : Type*} [Field K] [Algebra ℚ K]
    (P : GeometricMultiSourceChowBirth X H p ι)
    (sourceCycle : (i : ι) →
      codimensionCycles (P.source i).X (P.codim i))
    (coefficient : ι → K)
    (alpha : RationalSingularCohomology H.analytification (2*p))
    (hExtended :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2*p))
      ∀ j : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2*p)),
        algebraMap ℚ K ((b.repr alpha) j) =
          ∑ i : ι, coefficient i * algebraMap ℚ K
            ((b.repr
              (P.betti i ((P.data i).cycleClass
                (P.codim i) (sourceCycle i)))) j)) :
    ∃ Z : codimensionCycles X.X p,
      H.cycleClass p Z = alpha := by
  classical
  let actualNative : ι → codimensionCycles X.X p :=
    fun i => P.native i (sourceCycle i)
  apply rational_native_cycle_of_extended_span
    (K := K) (s := Finset.univ) actualNative coefficient alpha
  dsimp only at hExtended ⊢
  intro j
  have h := hExtended j
  simpa only [actualNative, P.naturality] using h

#check native_target_cycle_of_multisource_CM_field_spanning
#print axioms native_target_cycle_of_multisource_CM_field_spanning

/-! ## Finite CM source assembly WITHOUT a universal target-span hypothesis

2026-10-28 proof draft, not compiled in this session.
The preceding multisource theorem accepts `GeometricMultiSourceChowBirth`,
which contains a `hodgeSpan` statement for EVERY target. That field is not
needed to descend one independently constructed finite period expansion.
This upgrade removes that stronger input entirely, retaining actual source
cycles, actual cross-carrier naturality, and the exact target-specific
extension-coefficient identity. In particular Qbar periods are allowed.
-/

open GSTClassicalHodgeCrossCarrierGeometricTransfer

/-- Explicit rational original-X cycle from finite heterogeneous CM images.
No `hodgeSpan`, basis supply, or target-cycle selector is an argument. -/
noncomputable def nativeCycleFromCrossCarrierCoefficients
    {X : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData X}
    (p : ℕ) {ι : Type*} [Fintype ι]
    (source : ι → SmoothProjectiveComplexScheme)
    (D : (i : ι) → HodgeBigradedBettiData (source i))
    (q : ι → ℕ)
    (T : (i : ι) → CrossCarrierTransfer (source i) X (D i) H (q i) p)
    (sourceCycle : (i : ι) → codimensionCycles (source i).X (q i))
    (coefficient : ι → K) : codimensionCycles X.X p :=
  rationalCycleFromExtensionCoefficients Finset.univ
    (fun i => (T i).native (sourceCycle i)) coefficient

theorem nativeCycleFromCrossCarrierCoefficients_spec
    {X : SmoothProjectiveComplexScheme} {H : HodgeBigradedBettiData X}
    (p : ℕ) {ι : Type*} [Fintype ι]
    (source : ι → SmoothProjectiveComplexScheme)
    (D : (i : ι) → HodgeBigradedBettiData (source i))
    (q : ι → ℕ)
    (T : (i : ι) → CrossCarrierTransfer (source i) X (D i) H (q i) p)
    (sourceCycle : (i : ι) → codimensionCycles (source i).X (q i))
    (coefficient : ι → K)
    (alpha : RationalSingularCohomology H.analytification (2*p))
    (hExtended :
      let b := Module.Free.chooseBasis ℚ
        (RationalSingularCohomology H.analytification (2*p))
      ∀ j : Module.Free.ChooseBasisIndex ℚ
        (RationalSingularCohomology H.analytification (2*p)),
        algebraMap ℚ K ((b.repr alpha) j) =
          ∑ i : ι, coefficient i * algebraMap ℚ K
            ((b.repr ((T i).betti ((D i).cycleClass (q i) (sourceCycle i)))) j)) :
    H.cycleClass p
      (nativeCycleFromCrossCarrierCoefficients p source D q T sourceCycle coefficient) =
        alpha := by
  classical
  exact rationalCycleFromExtensionCoefficients_spec (K := K)
    (s := Finset.univ) (cycles := fun i => (T i).native (sourceCycle i))
    (coeff := coefficient) (alpha := alpha)
    (fun j => by
      have hNat (i : ι) : H.cycleClass p ((T i).native (sourceCycle i)) =
          (T i).betti ((D i).cycleClass (q i) (sourceCycle i)) :=
        (T i).naturality (sourceCycle i)
      simp only [hNat]
      exact hExtended j)

#check nativeCycleFromCrossCarrierCoefficients_spec
#print axioms nativeCycleFromCrossCarrierCoefficients_spec

#check rational_native_cycle_of_extended_span
#print axioms rational_native_cycle_of_extended_span

end GSTClassicalHodgeCMNativeRationalDescent
