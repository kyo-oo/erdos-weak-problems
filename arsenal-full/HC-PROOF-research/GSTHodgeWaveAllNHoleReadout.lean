import GSTGraphV2WaveNShapeCompiler
import GSTHodgeWaveFiniteCyclicCompletion

/-!
# GST exact all-N Wave-I/II/CM conserved information quotient

A NEW exact source-sensitive all-rank result, not merely another finite
matrix determinant:

For the *original* GST twelve-cell U+J+Wave-I SURVIVE source operator T,
the rational functional
  ell(u) = u(carry=0,trit=0) - u(carry=3,trit=2)
is a left eigenvector with eigenvalue TWO.  The raw x4/base3 information
fold and the mirror CM operator by themselves are not the same T.

For every independently addressed Wave-II NShape s (arbitrarily many
holes), the quotient ell applied to each hole is:
  * a genuine surjective rational linear map;
  * exactly intertwined with the existing shifted all-hole wave T_s;
  * governed by the pairwise distinct eigenvalues 2+10*channel(i);
  * born from the original GST uniform wave source with value 1 on each
    hole;
  * a kernel-invariant quotient, unlike an ad-hoc 12→9 projection.

Consequently its orbit is the Vandermonde family
  i ↦ (2 + 10*channel(i))^k for all k, and its first |s.holes|
columns are a rational basis by the Vandermonde identity.

These are information and wave theorems, not spatial coordinates or an
assertion that unknown Hodge classes already have Chow preimages.
-/

namespace GSTHodgeWaveAllNHoleReadout

open GSTGraphV2InformationRecovery
open GSTGraphV2CMWaveFusion
open GSTGraphV2WaveNShapeCompiler
open GSTNCohomology

abbrev Signal := GSTGraphV2CMWaveFusion.WaveSignal
abbrev PhysicalCell := GSTGraphV2InformationRecovery.Cell

def nullCell : PhysicalCell := ((0 : Fin 4), (0 : Fin 3))
def maximumCell : PhysicalCell := ((3 : Fin 4), (2 : Fin 3))

/-- An independently defined rational readout of the ORIGINAL Wave I
two fixed information cells: no geometric Hodge detector is inserted. -/
def nativeWaveReadout (u : Signal) : ℚ := u nullCell - u maximumCell

/-- The exact Wave-I source makes the fixed-cell readout a true left
eigenfunctional of the combined U+J+M wave operator. -/
theorem nativeWaveReadout_T (u : Signal) :
    nativeWaveReadout (T u) = 2 * nativeWaveReadout u := by
  have hnull : shuffle nullCell = nullCell := by decide
  have hmaximum : shuffle maximumCell = maximumCell := by decide
  have hmirror0 : mirrorCell nullCell = maximumCell := by decide
  have hmirror1 : mirrorCell maximumCell = nullCell := by decide
  have hphase0 : cmSign nullCell = 1 := by norm_num [cmSign, nullCell]
  have hphase1 : cmSign maximumCell = -1 := by norm_num [cmSign, maximumCell]
  have hmass0 : sourceMultiplicity nullCell = 0 := source_on_null_fixed
  have hmass1 : sourceMultiplicity maximumCell = 2 := source_on_positive_fixed
  change
    (u (shuffle nullCell) + cmSign nullCell * u (mirrorCell nullCell) +
       sourceMultiplicity nullCell * u nullCell) -
    (u (shuffle maximumCell) +
       cmSign maximumCell * u (mirrorCell maximumCell) +
       sourceMultiplicity maximumCell * u maximumCell) =
    2 * (u nullCell - u maximumCell)
  rw [hnull,hmaximum,hmirror0,hmirror1,hphase0,hphase1,hmass0,hmass1]
  ring

/-- A true rational linear readout, not merely a function on wave states. -/
def waveReadoutLinear : Signal →ₗ[ℚ] ℚ where
  toFun := nativeWaveReadout
  map_add' := by
    intro u v
    simp [nativeWaveReadout, Pi.add_apply]
    ring
  map_smul' := by
    intro q u
    simp [nativeWaveReadout, Pi.smul_apply, smul_eq_mul]
    ring

theorem waveReadoutLinear_T (u : Signal) :
    waveReadoutLinear (T u) = 2 * waveReadoutLinear u :=
  nativeWaveReadout_T u

/-- Every N-hole wave is observed by the original nonerasing fixed-cell
readout independently in each GST Wave-II channel. -/
def holeReadout (s : NShape) :
    HoleWaveSignals s →ₗ[ℚ] (Fin s.holes → ℚ) where
  toFun := fun u i => waveReadoutLinear (u i)
  map_add' := by
    intro u v
    funext i
    simp [Pi.add_apply, map_add]
  map_smul' := by
    intro q u
    funext i
    simp [Pi.smul_apply, map_smul, smul_eq_mul]

/-- The induced single coefficient fold from an independent NShape. -/
def coefficientFold (s : NShape) :
    (Fin s.holes → ℚ) →ₗ[ℚ] (Fin s.holes → ℚ) where
  toFun := fun v i => (2 + channelShift s i) * v i
  map_add' := by
    intro v w
    funext i
    simp [Pi.add_apply]
    ring
  map_smul' := by
    intro q v
    funext i
    simp [Pi.smul_apply, smul_eq_mul]
    ring

/-- ALL-N, ALL-WAVE intertwining: the wave-to-information map is a
**genuine quotient** of the full N-hole T_s, not a projection that
fails to respect the original operator. -/
theorem holeReadout_intertwines (s : NShape) (u : HoleWaveSignals s) :
    holeReadout s (shiftedNShapeFold s u) =
    coefficientFold s (holeReadout s u) := by
  funext i
  have hf : shiftedNShapeFold s u i =
      T (u i) + (channelShift s i) • u i := by
    funext c
    rfl
  change waveReadoutLinear (shiftedNShapeFold s u i) =
    (2 + channelShift s i) * waveReadoutLinear (u i)
  rw [hf, map_add, map_smul, waveReadoutLinear_T]
  simp [smul_eq_mul]
  ring

/-- The fixed-cell evaluation of the original mixed axial+rotating
Wave-I seed equals exactly one, no adjustable coefficient. -/
theorem waveReadout_seed : waveReadoutLinear seed = 1 := by
  have h0 : seed nullCell = 1 := by decide
  have h3 : seed maximumCell = 0 := by decide
  change seed nullCell - seed maximumCell = 1
  rw [h0, h3]
  norm_num

/-- Every original N-hole uniform source produces an all-one coefficient
seed in the quotient, at any number of holes. -/
theorem holeReadout_uniform (s : NShape) (i : Fin s.holes) :
    holeReadout s (uniformNShapeSeed s) i = 1 :=
  waveReadout_seed

/-- The entire infinite word of GST wave iterates has an exact
monomial spectral signature at EVERY N-hole address. -/
theorem holeReadout_orbit (s : NShape) (k : ℕ) (i : Fin s.holes) :
    holeReadout s (nShapeOrbit s k) i =
    (2 + channelShift s i)^k := by
  induction k with
  | zero =>
      simpa [nShapeOrbit] using holeReadout_uniform s i
  | succ k ih =>
      change (holeReadout s (shiftedNShapeFold s (nShapeOrbit s k))) i =
        (2+channelShift s i)^(k+1)
      rw [holeReadout_intertwines]
      change (2+channelShift s i) *
        holeReadout s (nShapeOrbit s k) i =
        (2+channelShift s i)^(k+1)
      rw [ih, pow_succ]
      ring

/-- The eigenvalues are pairwise distinct for arbitrary finite N
because the ORIGINAL Wave-II channels are injective. -/
theorem coefficientEigenvalue_injective (s : NShape) :
    Function.Injective (fun i : Fin s.holes =>
      (2 : ℚ) + channelShift s i) := by
  intro i j h
  apply channelShift_injective s
  exact add_left_cancel h

/-- An explicit right inverse of the all-hole information quotient. -/
def holeReadoutLift (s : NShape) (v : Fin s.holes → ℚ) :
    HoleWaveSignals s :=
  fun i c => if c = nullCell then v i else 0

/-- Arbitrary information-channel amplitudes really arise as original
GST waves, not through a postulated abstract projection. -/
theorem holeReadout_lift (s : NShape) (v : Fin s.holes → ℚ) :
    holeReadout s (holeReadoutLift s v) = v := by
  funext i
  have hdistinct : maximumCell ≠ nullCell := by decide
  simp [holeReadout, waveReadoutLinear, nativeWaveReadout,
    holeReadoutLift, hdistinct]

theorem holeReadout_surjective (s : NShape) :
    Function.Surjective (holeReadout s) := by
  intro v
  exact ⟨holeReadoutLift s v, holeReadout_lift s v⟩

/-- The kernel is genuinely invariant under the exact full wave fold.
This is the compatibility missing from arbitrary truncated projections. -/
theorem holeReadout_kernel_stable (s : NShape)
    (u : HoleWaveSignals s) (hu : holeReadout s u = 0) :
    holeReadout s (shiftedNShapeFold s u) = 0 := by
  rw [holeReadout_intertwines, hu, map_zero]

#check waveReadoutLinear_T
#check holeReadout_intertwines
#check holeReadout_orbit
#check coefficientEigenvalue_injective
#check holeReadout_surjective
#check holeReadout_kernel_stable
#print axioms holeReadout_orbit
#print axioms holeReadout_kernel_stable

end GSTHodgeWaveAllNHoleReadout
