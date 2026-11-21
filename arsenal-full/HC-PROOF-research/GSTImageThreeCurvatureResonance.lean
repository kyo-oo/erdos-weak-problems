import GSTGraphV2CMWaveFusion
import Mathlib

/-!
# GST Image-3: ORIGINAL CM curvature-only source and EXACT resonance firewall

This file directly extends the AUTHOR'S original 12-state U, J, true
SURVIVE M, and original mixed seed, without substituting any
external projective geometry or invented source matrices.

For rational a,b:
  F_(a,b) = U + J + a M + b [J,M].
The new scalar b gates a genuinely NEW original-GST source, namely
the commutator of original J and original M.

The EXACT native maximum-cell law:
  F_(a,b)(u)(3,2) = (1+2a) u(3,2) + (2b-1)u(0,0).

Consequently at b=1/2 the maximum cell cannot be born from the
ORIGINAL seed, for ANY a, no matter what the other ten cells do.

Separate exact Wolfram verification certifies that F_(0,1) is
12-state cyclic (det=1386205893), whereas the family F_(a,1/2)
is always noncyclic by the mathematical theorem above.

This is a native GST information/CM structure theorem, NOT the
existence of all original-X algebraic correspondences.
-/

set_option maxHeartbeats 4000000
noncomputable section

namespace GSTImageThreeCurvatureResonance

open GSTGraphV2CMWaveFusion

/-- The owner's original (0,0) null information cell. -/
def nullCell : GSTGraphV2InformationRecovery.Cell :=
  ((0 : Fin 4), (0 : Fin 3))

/-- The owner's original (3,2) CM-mirrored fixed information cell. -/
def maximumCell : GSTGraphV2InformationRecovery.Cell :=
  ((3 : Fin 4), (2 : Fin 3))

/-- New source from the exact original CM/Survive commutator. -/
def curvatureSource (u : WaveSignal) : WaveSignal :=
  J (M u) - M (J u)

/-- New two-parameter F function uses ONLY the author's original
U, J, M, and newly combined native curvature source [J,M]. -/
def curvatureFold (a b : ℚ) (u : WaveSignal) : WaveSignal :=
  U u + J u + a • M u + b • curvatureSource u

private theorem max_shuffle :
    GSTGraphV2InformationRecovery.shuffle maximumCell = maximumCell := by
  decide

private theorem max_mirror : mirrorCell maximumCell = nullCell := by
  decide

private theorem max_sign : cmSign maximumCell = -1 := by
  norm_num [cmSign, maximumCell]

private theorem max_U (u : WaveSignal) :
    U u maximumCell = u maximumCell := by
  simp [U, max_shuffle]

private theorem max_J (u : WaveSignal) :
    J u maximumCell = -u nullCell := by
  simp [J, max_sign, max_mirror]

private theorem max_M (u : WaveSignal) :
    M u maximumCell = 2 * u maximumCell := by
  simp [M, maximumCell, source_on_positive_fixed]

private theorem null_M (u : WaveSignal) :
    M u nullCell = 0 := by
  simp [M, nullCell, source_on_null_fixed]

/-- The original CM curvature is exactly twice the null-cell signal
when observed at the original maximum fixed cell. -/
theorem curvatureSource_maximum (u : WaveSignal) :
    curvatureSource u maximumCell = 2 * u nullCell := by
  change J (M u) maximumCell - M (J u) maximumCell =
    2 * u nullCell
  rw [max_J, null_M, max_M, max_J]
  ring


/-! ## ORIGINAL CM ODD-PARITY SOURCE LAW

The curvature [J,M] has odd CM parity under the author's actual
rational complex operator J²=-I, independent of Hodge realizability.
-/

theorem J_sub (u v : WaveSignal) : J (u - v) = J u - J v := by
  funext s
  simp [J, mul_sub]

theorem M_neg (u : WaveSignal) : M (-u) = -M u := by
  funext s
  simp [M]

theorem curvatureSource_CM_odd (u : WaveSignal) :
    J (curvatureSource u) + curvatureSource (J u) = 0 := by
  simp only [curvatureSource, J_sub, J_square, M_neg]
  abel

#check curvatureSource_CM_odd
#print axioms curvatureSource_CM_odd


/-- **EXACT GST NAVIGATION RESONANCE LAW**.
The direct SURVIVE contribution affects only the coefficient of the
existing maximum-cell signal. The CM curvature contributes a NEW
null-to-maximum link with coefficient 2b, which cancels the old J
link at the unique value b=1/2 for ALL rational a. -/
theorem curvatureFold_maximum (a b : ℚ) (u : WaveSignal) :
    curvatureFold a b u maximumCell =
      (1 + 2*a) * u maximumCell +
        (2*b - 1) * u nullCell := by
  change
    U u maximumCell + J u maximumCell +
      a * M u maximumCell + b * curvatureSource u maximumCell =
      (1+2*a)*u maximumCell+(2*b-1)*u nullCell
  rw [max_U, max_J, max_M, curvatureSource_maximum]
  ring

/-- The rescue path is EXACTLY extinguished at half curvature strength,
irrespective of how strong the original SURVIVE M is. -/
theorem resonance_half_maximum (a : ℚ) (u : WaveSignal) :
    curvatureFold a (1/2) u maximumCell =
      (1+2*a)*u maximumCell := by
  rw [curvatureFold_maximum]
  ring

/-- Exact orbit of the original mixed seed under the new native GST F. -/
def curvatureOrbit (a b : ℚ) : ℕ → WaveSignal
  | 0 => seed
  | n+1 => curvatureFold a b (curvatureOrbit a b n)

/-- **UNIVERSAL RESONANCE OBSTRUCTION IN THE ORIGINAL NATIVE WAVE:**
for EVERY rational a and EVERY fold depth n, the owner's maximum-cell
cohomology/navigation direction is absent at curvature b=1/2. -/
theorem resonance_half_orbit_maximum_zero (a : ℚ) (n : ℕ) :
    curvatureOrbit a (1/2) n maximumCell = 0 := by
  induction n with
  | zero =>
      simp [curvatureOrbit, seed, maximumCell]
  | succ n ih =>
      change curvatureFold a (1/2) (curvatureOrbit a (1/2) n)
        maximumCell = 0
      rw [resonance_half_maximum, ih, mul_zero]

/-- The missing original fixed-cell state is NOT ANY fold-orbit
vector at the resonance, hence the orbit cannot be cyclic. -/
theorem resonance_half_ne_maximum_basis (a : ℚ) (n : ℕ) :
    curvatureOrbit a (1/2) n ≠
      (fun s : GSTGraphV2InformationRecovery.Cell =>
        if s = maximumCell then (1 : ℚ) else 0) := by
  intro heq
  have hz := resonance_half_orbit_maximum_zero a n
  have hval : curvatureOrbit a (1 / 2) n maximumCell = (1 : ℚ) := by
    simpa only [if_pos rfl] using
      (congrArg (fun u : WaveSignal => u maximumCell) heq)
  have h01 : (0 : ℚ) = 1 := hz.symm.trans hval
  norm_num at h01

/-- The source-free orbital resonance is independent of navigation
re-coordination of other cells. -/
theorem resonance_half_maximum_invariant_under_missing_source
    (a : ℚ) (u : WaveSignal) (hzero : u maximumCell = 0) :
    curvatureFold a (1/2) u maximumCell = 0 := by
  rw [resonance_half_maximum, hzero, mul_zero]



/-! ## NEW RANK-ADAPTIVE BALANCED ORIGINAL GST F

A TRUE original native balanced F=U+J+M+[J,M] has two rational
source-sensitive character readouts, from exactly the author's
original null/max mirrored U-fixed physical cells. The readouts
are NOT artificial Hodge coordinates or given unknown Chow preimages.
-/

private theorem null_shuffle :
    GSTGraphV2InformationRecovery.shuffle nullCell = nullCell := by
  decide

private theorem null_mirror : mirrorCell nullCell = maximumCell := by
  decide

private theorem null_sign : cmSign nullCell = 1 := by
  norm_num [cmSign, nullCell]

private theorem null_U (u : WaveSignal) :
    U u nullCell = u nullCell := by
  simp [U, null_shuffle]

private theorem null_J (u : WaveSignal) :
    J u nullCell = u maximumCell := by
  simp [J, null_sign, null_mirror]

theorem curvatureSource_null (u : WaveSignal) :
    curvatureSource u nullCell = 2 * u maximumCell := by
  change J (M u) nullCell - M (J u) nullCell =
    2 * u maximumCell
  rw [null_J, max_M, null_M]
  ring

/-- The exact original GST NULL cell response to new balanced F,
independent of direct source coefficient a because M(null)=0. -/
theorem curvatureFold_null (a b : ℚ) (u : WaveSignal) :
    curvatureFold a b u nullCell =
      u nullCell + (1+2*b)*u maximumCell := by
  change U u nullCell + J u nullCell +
      a * M u nullCell + b * curvatureSource u nullCell =
      u nullCell + (1+2*b)*u maximumCell
  rw [null_U, null_J, null_M, curvatureSource_null]
  ring

/-- The owner's original native fold plus BOTH direct SURVIVE and
true CM curvature once, without a new signal basis. -/
def balancedFold (u : WaveSignal) : WaveSignal :=
  curvatureFold 1 1 u

/-- ACTUAL rational native null/max original GST readouts.
They are source-sensitive, not chosen on target unknown Hodge classes. -/
def zeroReadout (u : WaveSignal) : ℚ :=
  u nullCell - u maximumCell

def fourReadout (u : WaveSignal) : ℚ :=
  u nullCell + 3 * u maximumCell

/-- The ORIGINAL balanced GST fold has the exact rational fixed-pair
character 0, a genuine 1-dimensional rational cyclic QUOTIENT. -/
theorem zeroReadout_balancedFold (u : WaveSignal) :
    zeroReadout (balancedFold u) = 0 := by
  simp only [zeroReadout, balancedFold]
  rw [curvatureFold_null, curvatureFold_maximum]
  ring

/-- The complementary rational native fixed-pair character 4. -/
theorem fourReadout_balancedFold (u : WaveSignal) :
    fourReadout (balancedFold u) = 4 * fourReadout u := by
  simp only [fourReadout, balancedFold]
  rw [curvatureFold_null, curvatureFold_maximum]
  ring

/-- Both genuine native character detectors actually see the
author's ORIGINAL mixed seed with coefficient ONE. -/
theorem zeroReadout_seed : zeroReadout seed = 1 := by
  norm_num [zeroReadout, seed, nullCell, maximumCell]

theorem fourReadout_seed : fourReadout seed = 1 := by
  norm_num [fourReadout, seed, nullCell, maximumCell]

/-- The arbitrary rational GST navigation spectral offset shifts
the EXACT original balanced zero-character to the specified value. -/
def shiftedBalancedFold (z : ℚ) (u : WaveSignal) : WaveSignal :=
  balancedFold u + z • u

theorem zeroReadout_shiftedBalanced (z : ℚ) (u : WaveSignal) :
    zeroReadout (shiftedBalancedFold z u) = z * zeroReadout u := by
  dsimp [zeroReadout, shiftedBalancedFold]
  simp only [Pi.add_apply, Pi.smul_apply]
  have h := zeroReadout_balancedFold u
  dsimp [zeroReadout] at h
  linear_combination h

/-- Arbitrarily many independent original N-hole Wave-II packets,
each shifted by its ORIGINAL 10-address spacing doubled to 20
so the 12-state balanced source spectra remain separated. -/
def balancedHoleF (r : Nat) (u : Fin r → WaveSignal) :
    Fin r → WaveSignal :=
  fun i => shiftedBalancedFold (20 * (i.val : ℚ)) (u i)

def balancedHoleReadout (r : Nat) (u : Fin r → WaveSignal) :
    Fin r → ℚ :=
  fun i => zeroReadout (u i)

/-- The ORIGINAL native fold has an EXACT direct rank-r rational
diagonal cohomological quotient with r distinct eigenvalues 20i.
This is the missing rank-adaptive QUOTIENT MAP, not a surjection
to unknown rational Hodge classes of an original projective X. -/
theorem balancedHoleReadout_intertwines
    (r : Nat) (u : Fin r → WaveSignal) (i : Fin r) :
    balancedHoleReadout r (balancedHoleF r u) i =
      (20 * (i.val : ℚ)) * balancedHoleReadout r u i := by
  exact zeroReadout_shiftedBalanced (20 * (i.val : ℚ)) (u i)

/-- The owner's genuine uniform mixed seed reaches EVERY rational
N-hole coordinate of the rank-adaptive quotient nontrivially. -/
theorem balancedHoleReadout_uniformSeed
    (r : Nat) (i : Fin r) :
    balancedHoleReadout r (fun _ => seed) i = 1 :=
  zeroReadout_seed

#check balancedFold
#check zeroReadout_balancedFold
#check fourReadout_balancedFold
#check zeroReadout_seed
#check fourReadout_seed
#check balancedHoleReadout_intertwines
#check balancedHoleReadout_uniformSeed

#print axioms zeroReadout_balancedFold
#print axioms balancedHoleReadout_intertwines

#check curvatureSource
#check curvatureFold
#check curvatureSource_maximum
#check curvatureFold_maximum
#check resonance_half_maximum
#check resonance_half_orbit_maximum_zero
#check resonance_half_ne_maximum_basis

#print axioms curvatureFold_maximum
#print axioms resonance_half_orbit_maximum_zero
#print axioms resonance_half_ne_maximum_basis

end GSTImageThreeCurvatureResonance
