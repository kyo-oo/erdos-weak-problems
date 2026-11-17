import GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
import GSTClassicalHodgeGeometricPeriodDeterminant
import GSTClassicalHodgeProjectiveDegreeTrace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# THE FULL HODGE ATTACK THROUGH ONE REALIZED CORRESPONDENCE, ONE NATIVE
# ALGEBRAIC SEED AND ONE PROJECTIVE-STYLE TRACE

The older GSTClassicalHodgeRealizedCorrespondenceKrylovFinale assumes the
native/cohomological orbit of one actual correspondence word spans the
Hodge fiber. That geometric CYCLICITY property is substantial.

We replace it with a NUMERICAL SCALAR NONVANISHING CRITERION.

Let n be the genuine rational dimension of the p,p Hodge fiber.
Choose ONE genuine realized correspondence word T, ONE native
algebraic cycle Z, and ONE rational linear trace ell. Build
v_j = T^j cl(Z) and the n-by-n moment matrix

             H_ij = ell(T^i v_j)
                  = ell(T^(i+j) cl(Z)).

If det(H) != 0, the native cycles
        Z, T_native Z, ..., T_native^(n-1) Z
span the ENTIRE Hodge fiber under the exact cycle-class map.

The proof is direct: H is the period matrix of the n genuine
native orbit classes against the n rational detectors ell o T^i.
Its nonzero determinant forces the Hodge coordinate matrix to be
invertible. Multiply its inverse by the arbitrary Hodge coordinates
and form the resulting RATIONAL sum of the native orbit cycles.
Naturality of the actual realized correspondence gives its exact class.

THERE IS NO assumption of orbit cyclicity or basis algebraicity.

This is the strongest compact numerical target discovered in the
repo's existing genuine-correspondence line: instead of realizing
every matrix unit or finding n different correspondences, it suffices
to construct ONE scheme-realized correspondence and verify ONE
Hankel determinant by genuine period/intersection geometry.

This DOES NOT prove nonvanishing for every V. A universal nonzero
Hankel construction remains the mathematical theorem to derive.
A word acting by a scalar on a higher-dimensional Hodge fiber
necessarily has a singular Hankel matrix, so a nontrivial geometric
operator is indispensable.

NEEDS CI RUN LATER.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 900000

noncomputable section

open scoped BigOperators
open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTClassicalHodgeFiberedCosmology
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale
open GSTClassicalHodgeRealizedCorrespondenceKrylovFinale.RealizedCorrespondenceKrylovCertificate
open GSTClassicalHodgeGeometricMatrixRankLanding
open GSTClassicalHodgeGeometricPeriodDeterminant

namespace GSTClassicalHodgeGeometricKrylovMomentDeterminant

variable {V : SmoothProjectiveComplexScheme}
variable {H : HodgeBigradedBettiData V}
variable {p : Nat}

/-- The genuine matrix size is the FULL rational Hodge dimension, not
a fixed artificial GST observation-window size. -/
abbrev KrylovRank :=
  Module.finrank ℚ (ClassicalHodgeFiber V H p)

/-- The ith detector reads the ith moment of the EXISTING
correspondence action, followed by one rational geometric trace. -/
noncomputable def krylovMomentDetector
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (trace : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (i : Fin (KrylovRank (V := V) (H := H) (p := p))) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
  trace.comp (C.hodgeOperator ^ i.val)

/-- Entire geometric moment/Hankel matrix from one correspondence, seed,
and trace. Each column is an actual native cycle-class iterate. -/
noncomputable def krylovHankelMatrix
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (trace : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ) :
    Matrix
      (Fin (KrylovRank (V := V) (H := H) (p := p)))
      (Fin (KrylovRank (V := V) (H := H) (p := p))) ℚ :=
  periodMatrix
    (fun j => C.hodgeOrbit j.val)
    (krylovMomentDetector C trace)

/-- A nonsingular scalar Hankel matrix constructs the rational-native
cycle representing an ARBITRARY genuine Hodge fiber vector.

Unlike the historical Krylov finale, NO orbit-cyclicity assumption
is supplied: it is numerically certified by determinant nonvanishing. -/
theorem native_cycle_of_nonzero_krylov_hankel_determinant
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (trace : ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ)
    (hdet : (krylovHankelMatrix C trace).det ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 := by
  classical
  let b := Module.finBasis ℚ (ClassicalHodgeFiber V H p)
  let z : Fin (KrylovRank (V := V) (H := H) (p := p)) →
      ClassicalHodgeFiber V H p :=
    fun j => C.hodgeOrbit j.val
  let M : Matrix
      (Fin (KrylovRank (V := V) (H := H) (p := p)))
      (Fin (KrylovRank (V := V) (H := H) (p := p))) ℚ :=
    geometricCoordinateMatrix b z
  have hMdet : M.det ≠ 0 :=
    coordinate_det_ne_zero_of_period_det_ne_zero
      b z (krylovMomentDetector C trace) hdet
  have hMunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hMdet
  let coefficients :
      Fin (KrylovRank (V := V) (H := H) (p := p)) → ℚ :=
    (M⁻¹).mulVec (fun i => (b.repr alpha) i)
  let Z : codimensionCycles V.X p :=
    ∑ j : Fin (KrylovRank (V := V) (H := H) (p := p)),
      coefficients j • C.nativeOrbit j.val
  have hreconstruct :
      ∑ j : Fin (KrylovRank (V := V) (H := H) (p := p)),
        coefficients j • z j = alpha := by
    exact geometric_matrix_right_inverse_reconstructs
      b z M⁻¹ (Matrix.mul_nonsing_inv M hMunit) alpha
  have hZ :
      H.cycleClass p Z =
        (∑ j : Fin (KrylovRank (V := V) (H := H) (p := p)),
          coefficients j • z j).1 := by
    simp [Z, coefficients, z,
      map_sum, map_smul, C.nativeOrbit_cycleClass,
      Submodule.coe_sum, Submodule.coe_smul_of_tower]
  refine ⟨Z, ?_⟩
  exact hZ.trans (congrArg Subtype.val hreconstruct)

#print axioms native_cycle_of_nonzero_krylov_hankel_determinant
/-- Universal target at all codimensions using ONE genuine realized
correspondence, ONE algebraic seed, and ONE rational trace per weight.
Everything is in HC-PROOF's pre-existing strict correspondence language. -/
def UniversalGSTKrylovHankelNondegeneracy
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H) : Prop :=
  ∀ q : Nat,
    letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
    ∃ C : RealizedCorrespondenceKrylovCertificate V H q,
    ∃ trace : ClassicalHodgeFiber V H q →ₗ[ℚ] ℚ,
      (krylovHankelMatrix C trace).det ≠ 0

/-- FULL rational Hodge on the arbitrary smooth projective carrier V
from the single-correspondence scalar Hankel criterion at every weight.
The proof constructs each target native cycle from genuine iterates. -/
theorem full_hodge_of_universal_Krylov_Hankel_geometry
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h : UniversalGSTKrylovHankelNondegeneracy F) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
  obtain ⟨C, trace, hDet⟩ := h q
  exact native_cycle_of_nonzero_krylov_hankel_determinant
    C trace hDet ⟨alpha, halpha⟩


#print axioms full_hodge_of_universal_Krylov_Hankel_geometry
/-! ## GST POLARIZED SPECTRAL-MOMENT FACTORIZATION

The old universal Hodge Krylov law asks for a nonzero Hankel
determinant. This new law computes the determinant from primitive
polarization, spectral coordinates, and actual rational eigenvalues.

If the genuinely realized correspondence is Q-self-adjoint and has
simple rational eigenvalues lambda_k with Q-orthogonal eigenvectors,
the Hodge orbit seed has spectral weights w_k=Q(v_k,v_k).
Its Gram moments are H_ij=sum_k w_k lambda_k^(i+j).

The matrix identity H=A.transpose * diagonal(w) * A, with
A_kj=lambda_k^j, gives det H=(det A)^2 * product_k w_k.
Thus if the geometric seed has POSITIVE primitive energy in
every eigensector and the realized correspondence has independent
eigenvalue coordinates, the Hankel determinant is AUTOMATICALLY
nonzero. This removes a bare determinant witness and upgrades
the actual GST numerical geometry test.

Neither a realizable T nor a fresh algebraic seed is generated by
the identity. A zero spectral weight is the exact diagnostic for
a missing *geometric* eigensector source.
-/

/-- Rational Vandermonde-coordinate matrix of the spectral action. -/
def gstSpectralPowerMatrix (n : ℕ) (lambda : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun k j => lambda k ^ j.val

/-- The primitive polarized moment matrix for a genuine spectral seed. -/
def gstSpectralMomentMatrix (n : ℕ)
    (lambda weights : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  (gstSpectralPowerMatrix n lambda).transpose *
    Matrix.diagonal weights *
      gstSpectralPowerMatrix n lambda

/-- Exact GST spectral-moment determinant law in EVERY rational rank. -/
theorem gstSpectralMoment_det_factor
    (n : ℕ) (lambda weights : Fin n → ℚ) :
    (gstSpectralMomentMatrix n lambda weights).det =
      (gstSpectralPowerMatrix n lambda).det ^ 2 *
        ∏ k : Fin n, weights k := by
  unfold gstSpectralMomentMatrix
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

#print axioms gstSpectralMoment_det_factor
/-- True positive primitive spectral energy and a nondegenerate
spectral power matrix FORCE the full Hankel test to pass; no
uninterpreted determinant hypothesis remains. -/
theorem gstSpectralMoment_det_nonzero
    (n : ℕ) (lambda weights : Fin n → ℚ)
    (hSpectral : (gstSpectralPowerMatrix n lambda).det ≠ 0)
    (hWeights : ∀ k, 0 < weights k) :
    (gstSpectralMomentMatrix n lambda weights).det ≠ 0 := by
  rw [gstSpectralMoment_det_factor]
  apply mul_ne_zero (pow_ne_zero 2 hSpectral)
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt (hWeights i)

#check gstSpectralMoment_det_factor
#check gstSpectralMoment_det_nonzero
#print axioms gstSpectralMoment_det_nonzero

#print axioms gstSpectralMoment_det_nonzero
/-! ## Genuine projective-degree specialization

Use the already developed GSTProjectiveDegreeTraceSemantics, whose
point-cycle trace is the strictly positive projective degree. The
moments are now scalar projective degrees of actual native
correspondence iterates, not arbitrarily chosen dual functionals. -/

/-- The true projective-degree functional restricted to the rational
Hodge fiber in weight p. No new cohomological functional is assumed. -/
noncomputable def projectiveDegreeHodgeTrace
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H) :
    ClassicalHodgeFiber V H p →ₗ[ℚ] ℚ :=
  (D.trace p).comp
    (rationalHodgeSubspace (H.hodgeBigrading p)).subtype

/-- The already-realized Hodge operator advances exactly along the
existing native/cohomological Krylov orbit. This is a direct computation,
not a new orbit-cyclicity hypothesis. -/
theorem hodgeOperator_pow_orbit
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (i j : Nat) :
    (C.hodgeOperator ^ i) (C.hodgeOrbit j) =
      C.hodgeOrbit (i + j) := by
  induction i with
  | zero =>
      simp
  | succ i ih =>
      rw [pow_succ']
      change
        C.hodgeOperator
          ((C.hodgeOperator ^ i) (C.hodgeOrbit j)) =
            C.hodgeOrbit (Nat.succ i + j)
      rw [ih, Nat.succ_add, Nat.succ_eq_add_one]
      rw [RealizedCorrespondenceKrylovCertificate.hodgeOrbit.eq_2]

#print axioms hodgeOperator_pow_orbit
/-- Hankel matrix of actual projective-degree moments of ONE genuinely
realized closed correspondence acting on ONE genuine native cycle. -/
noncomputable def projectiveDegreeKrylovHankel
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (C : RealizedCorrespondenceKrylovCertificate V H p) :
    Matrix
      (Fin (KrylovRank (V := V) (H := H) (p := p)))
      (Fin (KrylovRank (V := V) (H := H) (p := p))) ℚ :=
  krylovHankelMatrix C (projectiveDegreeHodgeTrace D)

/-- **EXACT SCALAR MOMENT FORMULA.**
Each i,j entry of the Hankel matrix is literally the projective-degree
Betti trace of the genuine native algebraic cycle obtained after
i+j iterates of ONE realized finite closed-correspondence word.

This establishes the promised Hankel identity
     H_ij = degree( T_native^(i+j) Z )
at the repository's actual native cycle-class semantics. -/
theorem projectiveDegreeKrylovHankel_apply
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (i j : Fin (KrylovRank (V := V) (H := H) (p := p))) :
    projectiveDegreeKrylovHankel D C i j =
      D.trace p (H.cycleClass p (C.nativeOrbit (i.val + j.val))) := by
  change D.trace p
      (((C.hodgeOperator ^ i.val) (C.hodgeOrbit j.val)).1) =
        D.trace p (H.cycleClass p
          (C.nativeOrbit (i.val + j.val)))
  rw [hodgeOperator_pow_orbit C i.val j.val]
  rw [C.nativeOrbit_cycleClass]

#print axioms projectiveDegreeKrylovHankel_apply
/-! ## GST degree-eigenfunctional obstruction

An important distinction in the native correspondence route:
projective-degree positivity proves an algebraic seed is NOT zero, but
it cannot by itself prove that a higher-dimensional orbit is cyclic.

If a genuine geometric correspondence acts on the projective-degree
functional by a single rational scalar lam, then every scalar moment
obeys a geometric progression. Its 2x2 moment minor is ZERO.

The following are proved statements about the ACTUAL existing GST
realized-correspondence Hodge operator. They prohibit treating degree
positivity as a universal determinant nonvanishing argument.
-/

/-- Geometric progression identity for the projective-degree moments
when the actual correspondence has degree as a left eigenfunctional. -/
theorem projectiveDegreeMoment_geometric_progression
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (lam : ℚ)
    (hDegreeEigen :
      ∀ a : ClassicalHodgeFiber V H p,
        projectiveDegreeHodgeTrace D (C.hodgeOperator a) =
          lam * projectiveDegreeHodgeTrace D a) :
    ∀ i j : Nat,
      projectiveDegreeHodgeTrace D (C.hodgeOrbit (i + j)) =
        lam ^ i * projectiveDegreeHodgeTrace D (C.hodgeOrbit j) := by
  intro i
  induction i with
  | zero =>
      intro j
      simp
  | succ i ih =>
      intro j
      rw [Nat.succ_add]
      change
        projectiveDegreeHodgeTrace D
            (C.hodgeOperator (C.hodgeOrbit (i + j))) =
          lam ^ (i + 1) *
            projectiveDegreeHodgeTrace D (C.hodgeOrbit j)
      rw [hDegreeEigen, ih j, pow_succ]
      ring

#print axioms projectiveDegreeMoment_geometric_progression
/-- Even with a nonzero projective-degree source, a correspondence that
scales that degree cannot yield an invertible 2x2 moment matrix.
The one-seed, one-degree-functional nonvanishing shortcut is obstructed
at the very first nontrivial Hodge multiplicity. -/
theorem projectiveDegreeMoment_first_minor_zero_of_degree_eigen
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (lam : ℚ)
    (hDegreeEigen :
      ∀ a : ClassicalHodgeFiber V H p,
        projectiveDegreeHodgeTrace D (C.hodgeOperator a) =
          lam * projectiveDegreeHodgeTrace D a) :
    projectiveDegreeHodgeTrace D (C.hodgeOrbit 0) *
        projectiveDegreeHodgeTrace D (C.hodgeOrbit 2) -
      projectiveDegreeHodgeTrace D (C.hodgeOrbit 1) *
        projectiveDegreeHodgeTrace D (C.hodgeOrbit 1) = 0 := by
  have h1 :
      projectiveDegreeHodgeTrace D (C.hodgeOrbit 1) =
        lam * projectiveDegreeHodgeTrace D (C.hodgeOrbit 0) :=
    hDegreeEigen (C.hodgeOrbit 0)
  have h2 :
      projectiveDegreeHodgeTrace D (C.hodgeOrbit 2) =
        lam * projectiveDegreeHodgeTrace D (C.hodgeOrbit 1) :=
    hDegreeEigen (C.hodgeOrbit 1)
  rw [h2, h1]
  ring

#print axioms projectiveDegreeMoment_first_minor_zero_of_degree_eigen
/-- The determinant of the geometric projective-degree Hankel matrix
is a sufficient NUMERICAL PROOF CERTIFICATE for every rational (p,p)
Hodge class to possess an explicitly constructed native algebraic cycle. -/
theorem native_cycle_of_projective_degree_krylov_det
    [FiniteDimensional ℚ (ClassicalHodgeFiber V H p)]
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (C : RealizedCorrespondenceKrylovCertificate V H p)
    (hDet : (projectiveDegreeKrylovHankel D C).det ≠ 0)
    (alpha : ClassicalHodgeFiber V H p) :
    ∃ Z : codimensionCycles V.X p,
      H.cycleClass p Z = alpha.1 :=
  native_cycle_of_nonzero_krylov_hankel_determinant
    C (projectiveDegreeHodgeTrace D) hDet alpha

#print axioms native_cycle_of_projective_degree_krylov_det
/-- Universal Hodge-level target with ONE ordinary projective-degree
trace, rather than an arbitrarily chosen functional per weight. -/
def UniversalProjectiveDegreeKrylovNondegeneracy
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H) : Prop :=
  ∀ q : Nat,
    letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
    ∃ C : RealizedCorrespondenceKrylovCertificate V H q,
      (projectiveDegreeKrylovHankel (p := q) D C).det ≠ 0

/-- Full rational Hodge from genuine scalar projective-degree
measurements of actual closed-correspondence iterates, in every
weight on an arbitrary smooth projective complex variety. -/
theorem full_hodge_of_projective_degree_Krylov_nonvanishing
    (D : GSTClassicalHodgeProjectiveDegreeTrace.ProjectiveDegreeTraceSemantics V H)
    (F : GSTHodgeChannelFinale.Stage2GHodgeFiniteness V H)
    (h : UniversalProjectiveDegreeKrylovNondegeneracy D F) :
    BigradedBettiHodgeStatement V H := by
  intro q alpha halpha
  letI : FiniteDimensional ℚ (ClassicalHodgeFiber V H q) := F.finite q
  obtain ⟨C, hDet⟩ := h q
  exact native_cycle_of_projective_degree_krylov_det
    D C hDet ⟨alpha, halpha⟩

#check krylovHankelMatrix
#check native_cycle_of_nonzero_krylov_hankel_determinant
#check full_hodge_of_universal_Krylov_Hankel_geometry
#print axioms full_hodge_of_universal_Krylov_Hankel_geometry

#print axioms full_hodge_of_projective_degree_Krylov_nonvanishing
end GSTClassicalHodgeGeometricKrylovMomentDeterminant
