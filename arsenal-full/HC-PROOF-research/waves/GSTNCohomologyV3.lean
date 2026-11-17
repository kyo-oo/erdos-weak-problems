import waves.GSTNCohomologyV2

/-!
# Wave II V3: independent N-holes and nonlinear current mass firewall

Upgrade the user's original GST N-cohomology, retaining its actual tower
readouts. The V2 canonicalNCohoBasis ignores the basis index and cannot
establish independence. Here delta coordinates are actually independent.

A rational-linear native mass cannot be universally nonnegative unless
identically zero. Thus it is not the geometric mass functional on integral
rectifiable currents. This theorem blocks an illegitimate substitution
in the universal primitive Hodge residual fixed-homology-current target.

No theorem here asserts the universal Hodge conjecture or its equivalent
fixed-homology almost-calibrated current construction.
-/

set_option maxHeartbeats 10000000

namespace GSTNCohomologyV3

open GSTNCohomology
open GSTNCohomologyV2

/-- The rational linear space of independent N-hole coordinates. -/
abbrev HoleCoordinates (s : NShape) := Fin s.holes → ℚ

/-- Actual Kronecker delta coordinate attached to hole i. -/
def independentHoleBasis (s : NShape) (i : Fin s.holes) :
    HoleCoordinates s :=
  fun j => if i = j then 1 else 0

/-- Every rational N-cohomology channel vector has an exact coordinate
expansion against the honest Kronecker hole basis. -/
theorem independentHoleBasis_reconstruct
    (s : NShape) (coeff : HoleCoordinates s) (j : Fin s.holes) :
    (∑ i : Fin s.holes, coeff i * independentHoleBasis s i j) =
      coeff j := by
  classical
  simp [independentHoleBasis, mul_ite]

/-- The independent basis has unique coordinates: zero sum forces each
coefficient to vanish. -/
theorem independentHoleBasis_coefficients_unique
    (s : NShape) (coeff : HoleCoordinates s)
    (hzero : ∀ j : Fin s.holes,
      (∑ i : Fin s.holes, coeff i * independentHoleBasis s i j) = 0) :
    ∀ i : Fin s.holes, coeff i = 0 := by
  intro i
  have hi := hzero i
  rw [independentHoleBasis_reconstruct s coeff i] at hi
  exact hi

/-- V2's indexed readout vectors are constant in their would-be basis
index. The repaired basis is a separate, honest coordinate object. -/
theorem former_basis_is_constant_in_basis_index
    (R : Nat) (s : NShape) (N : Nat)
    (i j : Fin s.holes) :
    canonicalNCohoBasis R s N i =
      canonicalNCohoBasis R s N j := by
  rfl

/-- Actual original N-tower data inserted into the independent coordinates. -/
def towerHoleCoefficients (R : Nat) (s : NShape) :
    HoleCoordinates s :=
  fun i => (waveIIAmplitude R (s.channel i) : ℚ)

theorem towerHoleCoefficients_reconstructed
    (R : Nat) (s : NShape) (j : Fin s.holes) :
    (∑ i : Fin s.holes,
      towerHoleCoefficients R s i * independentHoleBasis s i j) =
        (waveIIAmplitude R (s.channel j) : ℚ) := by
  exact independentHoleBasis_reconstruct s _ j

/-- A rational-linear native signed mass nonnegative on all signed
rational cycles is zero. Geometric current mass must be nonlinear. -/
theorem nonnegative_linear_native_mass_must_vanish
    {N : Type*} [AddCommGroup N] [Module ℚ N]
    (mass : N →ₗ[ℚ] ℚ)
    (hnonnegative : ∀ z : N, 0 ≤ mass z)
    (z : N) : mass z = 0 := by
  have hp := hnonnegative z
  have hn := hnonnegative (-z)
  rw [map_neg] at hn
  exact le_antisymm (neg_nonneg.mp hn) hp

/-- Any nonzero signed linear mass becomes negative under one of the
two orientations, unlike nonnegative geometric mass. -/
theorem nonzero_linear_mass_has_negative_orientation
    {N : Type*} [AddCommGroup N] [Module ℚ N]
    (mass : N →ₗ[ℚ] ℚ)
    (z : N) (hne : mass z ≠ 0) :
    mass z < 0 ∨ mass (-z) < 0 := by
  rcases lt_trichotomy (mass z) 0 with hneg | hz | hpos
  · exact Or.inl hneg
  · exact False.elim (hne hz)
  · right
    rw [map_neg]
    exact neg_lt_zero.mpr hpos

#check independentHoleBasis_reconstruct
#check independentHoleBasis_coefficients_unique
#check former_basis_is_constant_in_basis_index
#check towerHoleCoefficients_reconstructed
#check nonnegative_linear_native_mass_must_vanish
#check nonzero_linear_mass_has_negative_orientation

#print axioms independentHoleBasis_reconstruct
#print axioms independentHoleBasis_coefficients_unique
#print axioms nonnegative_linear_native_mass_must_vanish


/-! ## GST N-COHOMOLOGY DOUBLE CAUSAL FOLD: INDEPENDENT SOURCE BIRTH

The full N-hole coordinates are not compressed to a one-cell cosmic Hodge
diagonal. Two independently born causal graph-loop channels have a genuine
ordered-pair index, hence a product (not a sum) of their independent ranks.
A geometric nodal realization carries these classes in cohomological
degree two with mixed-Hodge weight zero. An arbitrary Tate extension
moves both degree and weight by 2j while retaining their separation.

The entire geometric Hodge interpretation follows from the causal incidence
and realized normalization computations, not from an arbitrary assignment
of a class on original X to a vector in the N-hole space.
-/

/-- The full rational multiplicity fiber of TWO independent N-hole families.
Both N-cohomology channel indices are retained. -/
abbrev DoubleCausalHoleCoordinates (s t : NShape) :=
  (Fin s.holes × Fin t.holes) → ℚ

/-- Independent tensor basis of the double-fold cohomology, with one
coordinate for every ordered pair of genuine N-hole channels. -/
def doubleCausalHoleBasis (s t : NShape)
    (a : Fin s.holes × Fin t.holes) :
    DoubleCausalHoleCoordinates s t :=
  fun b => if a = b then 1 else 0

/-- The product causal-fold coordinates have exact reconstruction, unlike
a rank-one collapsed cosmic-diagonal readout. -/
theorem doubleCausalHoleBasis_reconstruct
    (s t : NShape) (coeff : DoubleCausalHoleCoordinates s t)
    (j : Fin s.holes × Fin t.holes) :
    (∑ i : Fin s.holes × Fin t.holes,
      coeff i * doubleCausalHoleBasis s t i j) = coeff j := by
  classical
  simp [doubleCausalHoleBasis]

/-- Pairwise independent causal graph holes retain UNIQUE coefficients. -/
theorem doubleCausalHoleBasis_coefficients_unique
    (s t : NShape) (coeff : DoubleCausalHoleCoordinates s t)
    (hzero : ∀ j : Fin s.holes × Fin t.holes,
      (∑ i : Fin s.holes × Fin t.holes,
        coeff i * doubleCausalHoleBasis s t i j) = 0) :
    ∀ i : Fin s.holes × Fin t.holes, coeff i = 0 := by
  intro i
  rw [← doubleCausalHoleBasis_reconstruct s t coeff i]
  exact hzero i

/-- This is a genuine MULTIPLICATIVE birth count for independent
finite causal-hole indices: neither axis is collapsed. -/
theorem doubleCausalHoleBasis_channelCount
    (s t : NShape) :
    Fintype.card (Fin s.holes × Fin t.holes) =
      s.holes * t.holes := by
  simp

/-- Independent N-cohomological amplitudes form one genuine double-fold
tensor, rather than an unsupported external Hodge-to-Chow selector. -/
def doubleCausalHoleTensor (s t : NShape)
    (a : HoleCoordinates s) (b : HoleCoordinates t) :
    DoubleCausalHoleCoordinates s t :=
  fun ij => a ij.1 * b ij.2

/-- Tensor-product causal folding reproduces the independently measured
amplitude in each of its two coordinates. -/
theorem doubleCausalHoleTensor_apply
    (s t : NShape)
    (a : HoleCoordinates s) (b : HoleCoordinates t)
    (i : Fin s.holes) (j : Fin t.holes) :
    doubleCausalHoleTensor s t a b (i,j) = a i * b j := rfl


/-! ## GST MULTI-WORLD N-COHOMOLOGY: NO FINITE CAUSAL ARITY BOUND

The double graph-loop system is an m=2 realization of an arbitrary
finite family of typed N-hole sectors. The actual full multiplicity
fiber is a DEPENDENT product of the hole indices of each world.
Keeping all indices is essential: collapsing them to one cosmic
diagonal would destroy the product-rank emergence law.
-/

/-- Independent index of every genuine N-hole coordinate in every
causally participating world, with arbitrary finite arity m. -/
abbrev ManyCausalHoleIndex (m : ℕ) (s : Fin m → NShape) :=
  ∀ i : Fin m, Fin ((s i).holes)

/-- Every independent multi-causal hole coordinate survives as its
own rational amplitude; no source index or dimension is discarded. -/
abbrev ManyCausalHoleCoordinates (m : ℕ) (s : Fin m → NShape) :=
  ManyCausalHoleIndex m s → ℚ

/-- One delta channel per complete causal world-address tuple. -/
def manyCausalHoleBasis (m : ℕ) (s : Fin m → NShape)
    (a : ManyCausalHoleIndex m s) :
    ManyCausalHoleCoordinates m s :=
  fun b => if a = b then 1 else 0

/-- Exact ALL-ARITY source reconstruction of the emerged N-cohomology
space: causal multiplication retains the entire Hodge multiplicity fiber. -/
theorem manyCausalHoleBasis_reconstruct
    (m : ℕ) (s : Fin m → NShape)
    (coeff : ManyCausalHoleCoordinates m s)
    (j : ManyCausalHoleIndex m s) :
    (∑ i : ManyCausalHoleIndex m s,
      coeff i * manyCausalHoleBasis m s i j) = coeff j := by
  classical
  simp [manyCausalHoleBasis]

/-- Distinct multi-world causal channels remain linearly independent. -/
theorem manyCausalHoleBasis_coefficients_unique
    (m : ℕ) (s : Fin m → NShape)
    (coeff : ManyCausalHoleCoordinates m s)
    (hzero : ∀ j : ManyCausalHoleIndex m s,
      (∑ i : ManyCausalHoleIndex m s,
        coeff i * manyCausalHoleBasis m s i j) = 0) :
    ∀ j : ManyCausalHoleIndex m s, coeff j = 0 := by
  intro j
  rw [← manyCausalHoleBasis_reconstruct m s coeff j]
  exact hzero j

/-- Exact MULTIPLICATIVE causal rank across arbitrarily many independent
emergent N-hole dimensions, including the empty-world vacuum m=0. -/
theorem manyCausalHoleBasis_channelCount (m : ℕ) (s : Fin m → NShape) :
    Fintype.card (ManyCausalHoleIndex m s) =
      ∏ i : Fin m, (s i).holes := by
  classical
  simp [ManyCausalHoleIndex, Fintype.card_pi]

/-- The born product amplitude uses ACTUAL input amplitudes from each
individual N-hole world, not a freely chosen Hodge coordinate. -/
def manyCausalHoleTensor (m : ℕ) (s : Fin m → NShape)
    (a : ∀ i : Fin m, HoleCoordinates (s i)) :
    ManyCausalHoleCoordinates m s :=
  fun index => ∏ i : Fin m, a i (index i)

/-- The full tensor source readout is an explicit finite causal product. -/
theorem manyCausalHoleTensor_apply
    (m : ℕ) (s : Fin m → NShape)
    (a : ∀ i : Fin m, HoleCoordinates (s i))
    (index : ManyCausalHoleIndex m s) :
    manyCausalHoleTensor m s a index =
      ∏ i : Fin m, a i (index i) := rfl

#check manyCausalHoleBasis_reconstruct
#check manyCausalHoleBasis_channelCount
#check manyCausalHoleBasis_coefficients_unique
#check manyCausalHoleTensor_apply
#print axioms manyCausalHoleBasis_channelCount

#check doubleCausalHoleBasis_reconstruct
#check doubleCausalHoleBasis_coefficients_unique
#check doubleCausalHoleBasis_channelCount
#check doubleCausalHoleTensor_apply
#print axioms doubleCausalHoleBasis_reconstruct
#print axioms doubleCausalHoleBasis_channelCount


/-! ## Extension-sensitive folds retain tensor rank

The full product-coordinate space has product dimension, but ONE tensor of
independent input amplitudes lies on the rank-one locus. This is a precise
extra check required before interpreting causal products as arbitrary fiber
coverage. Pairing-graph linear combinations in the companion fold derivation
retain these multiplicities. No coordinate identity constructs Chow classes.
-/

def doubleCausalMinor (s t : NShape) (z : DoubleCausalHoleCoordinates s t)
    (i k : Fin s.holes) (j l : Fin t.holes) : ℚ :=
  z (i,j)*z (k,l)-z (i,l)*z (k,j)

theorem doubleCausalHoleTensor_minor_zero (s t : NShape)
    (a : HoleCoordinates s) (b : HoleCoordinates t)
    (i k : Fin s.holes) (j l : Fin t.holes) :
    doubleCausalMinor s t (doubleCausalHoleTensor s t a b) i k j l=0 := by
  simp only [doubleCausalMinor,doubleCausalHoleTensor]
  ring

/-- Explicit finite SUM of separated amplitudes, with all indices retained. -/
theorem separated_channel_sum_reconstruct (s t : NShape)
    (z : DoubleCausalHoleCoordinates s t) (k : Fin s.holes) (l : Fin t.holes) :
    (∑ i : Fin s.holes, ∑ j : Fin t.holes,
      z (i,j)*independentHoleBasis s i k*independentHoleBasis t j l)=z (k,l) := by
  classical
  simp [independentHoleBasis,mul_ite]

def twoChannelDiagonal : (Fin 2 × Fin 2) → ℚ :=
  fun ij => if ij.1=ij.2 then 1 else 0

theorem twoChannelDiagonal_minor :
    twoChannelDiagonal (0,0)*twoChannelDiagonal (1,1)-
      twoChannelDiagonal (0,1)*twoChannelDiagonal (1,0)=1 := by
  norm_num [twoChannelDiagonal]

theorem twoChannelDiagonal_not_one_tensor :
    ¬ ∃ a b : Fin 2 → ℚ, ∀ i j,twoChannelDiagonal (i,j)=a i*b j := by
  rintro ⟨a,b,h⟩
  have hc := twoChannelDiagonal_minor
  rw [h 0 0,h 1 1,h 0 1,h 1 0] at hc
  have hz : a 0*b 0*(a 1*b 1)-a 0*b 1*(a 1*b 0)=0 := by ring
  linarith

#print axioms doubleCausalHoleTensor_minor_zero
#print axioms separated_channel_sum_reconstruct
#print axioms twoChannelDiagonal_not_one_tensor
/-! ## The central causal fold has a full vector boundary

The degree-one boundary of the realized space is minus this curvature
transpose. Its kernel is identical. Every source and target channel is kept.
-/
def causalCurvatureBoundary (s t : NShape)
    (K : Fin s.holes → Fin t.holes → ℚ) (c : HoleCoordinates s) :
    HoleCoordinates t := fun j => ∑ i, K i j*c i

theorem causalCurvatureBoundary_add (s t : NShape)
    (K : Fin s.holes → Fin t.holes → ℚ) (c d : HoleCoordinates s) :
    causalCurvatureBoundary s t K (c+d)=
      causalCurvatureBoundary s t K c+causalCurvatureBoundary s t K d := by
  funext j
  simp [causalCurvatureBoundary,mul_add,Finset.sum_add_distrib]

theorem causalCurvatureBoundary_basis (s t : NShape)
    (K : Fin s.holes → Fin t.holes → ℚ) (i : Fin s.holes) (j : Fin t.holes) :
    causalCurvatureBoundary s t K (independentHoleBasis s i) j=K i j := by
  classical
  simp [causalCurvatureBoundary,independentHoleBasis,mul_ite]

theorem all_channels_closed_iff_zero_curvature (s t : NShape)
    (K : Fin s.holes → Fin t.holes → ℚ) :
    (∀ c : HoleCoordinates s,causalCurvatureBoundary s t K c=0) ↔ K=0 := by
  constructor
  · intro h
    funext i j
    have hi := congrFun (h (independentHoleBasis s i)) j
    simpa [causalCurvatureBoundary_basis] using hi
  · intro hK c
    rw [hK]
    funext j
    show (∑ i, (0 : Fin s.holes → Fin t.holes → ℚ) i j * c i) =
      (0 : HoleCoordinates t) j
    simp

theorem nonzero_curvature_detects_a_basis_channel (s t : NShape)
    (K : Fin s.holes → Fin t.holes → ℚ) (i : Fin s.holes) (j : Fin t.holes)
    (h : K i j ≠ 0) :
    causalCurvatureBoundary s t K (independentHoleBasis s i) ≠ 0 := by
  intro hz
  apply h
  have hj := congrFun hz j
  simpa [causalCurvatureBoundary_basis] using hj

/-- A zero collapsed scalar misses the two nonzero opposite channels. -/
theorem zero_total_is_not_zero_vector :
    (1 : ℚ)+(-1)=0 ∧ (![1,-1] : Fin 2 → ℚ) ≠ 0 := by
  constructor
  · norm_num
  · intro h
    have hi := congrFun h 0
    norm_num at hi

#print axioms all_channels_closed_iff_zero_curvature

/-- The same actual rational curvature matrix, extended to complex channels. -/
def complexCurvatureLinear (s t : NShape)
    (K : Fin s.holes → Fin t.holes → ℚ) :
    (Fin s.holes → ℂ) →ₗ[ℂ] (Fin t.holes → ℂ) where
  toFun c := fun j => ∑ i, (K i j : ℂ)*c i
  map_add' := by
    intro c d
    funext j
    simp [mul_add,Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    funext j
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [RingHom.id_apply]
    ring

/-! ## Curvature valued in the original base, in any even degree

Unlike a fixed coordinate matrix, alpha i is an actual base-cohomology
vector. In degree 2p its transpose measures the first affected degree
2p-1 of the higher transgression model. These algebraic statements do not
assign a complex manifold or an algebraic cycle to that model.
-/
section BaseValuedCurvature
variable {W : Type*} [AddCommGroup W] [Module ℚ W]

def targetCurvatureLinear (s : NShape) (alpha : Fin s.holes → W) :
    HoleCoordinates s →ₗ[ℚ] W where
  toFun c := ∑ i, c i • alpha i
  map_add' c d := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum,smul_smul]

theorem targetCurvature_basis (s : NShape) (alpha : Fin s.holes → W)
    (i : Fin s.holes) :
    targetCurvatureLinear s alpha (independentHoleBasis s i)=alpha i := by
  classical
  simp [targetCurvatureLinear,independentHoleBasis,ite_smul]

theorem targetCurvature_zero_iff (s : NShape) (alpha : Fin s.holes → W) :
    targetCurvatureLinear s alpha=0 ↔ ∀ i,alpha i=0 := by
  constructor
  · intro h i
    have hi := congrArg (fun T : HoleCoordinates s →ₗ[ℚ] W =>
      T (independentHoleBasis s i)) h
    simpa [targetCurvature_basis] using hi
  · intro h
    ext c
    simp [targetCurvatureLinear,h]

theorem targetCurvature_fusion (s : NShape) (alpha beta : Fin s.holes → W) :
    targetCurvatureLinear s (alpha+beta)=
      targetCurvatureLinear s alpha+targetCurvatureLinear s beta := by
  ext c
  simp [targetCurvatureLinear,smul_add,Finset.sum_add_distrib]

theorem targetCurvature_inverse_fusion (s : NShape) (alpha : Fin s.holes → W) :
    targetCurvatureLinear s (alpha+(-alpha))=0 := by
  apply (targetCurvature_zero_iff s (alpha+(-alpha))).mpr
  intro i
  simp

theorem targetCurvature_detects_prescribed_input (s : NShape)
    (alpha : Fin s.holes → W) (i : Fin s.holes) (hi : alpha i ≠ 0) :
    targetCurvatureLinear s alpha ≠ 0 := by
  intro h
  exact hi ((targetCurvature_zero_iff s alpha).mp h i)

#print axioms targetCurvature_zero_iff
end BaseValuedCurvature

end GSTNCohomologyV3
