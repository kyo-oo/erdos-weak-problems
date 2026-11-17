import GSTClassicalHodgePointNormalForm
import GSTCompactNativeCyclePresentation

/-!
# GST CLASSICAL HODGE — EXACT CLAY-STYLE TARGET

This file pins the exact rational Hodge theorem and provides the
acceptance specification for the GST geometric construction program.

For a smooth projective complex variety X and codimension p, a rational Hodge
class is a class in H^(2p)(X,Q) whose complexification belongs to H^(p,p).
The conjecture says that every such class is the class of a rational algebraic
codimension-p cycle.

Because `codimensionCycles X p` is already the Q-vector space of native
Mathlib algebraic cycles supported in codimension p, the phrase

  "a rational linear combination of algebraic cycles"

is represented literally by an element of `codimensionCycles X p`.

The last theorem expands the same statement further into a finite rational sum
of genuine codimension-p irreducible point cycles, using projective compactness.
-/

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

noncomputable section

open AlgebraicGeometry

namespace GSTClassicalHodgeExactClayStatement

open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G
open GSTNativeCodimensionCyclePresentation
open GSTCompactNativeCyclePresentation
open GSTClassicalHodgePointNormalForm

variable {V : SmoothProjectiveComplexScheme}
variable (H : HodgeBigradedBettiData V)

/-- Literal elementwise rational Hodge conjecture.
Every rational `(p,p)` class is the cycle class of one rational algebraic
codimension-p cycle. -/
def EveryHodgeClassIsRationalAlgebraic : Prop :=
  ∀ p : Nat,
  ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
    alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ∃ Z : codimensionCycles V.X p,
        H.cycleClass p Z = alpha

/-- Fully expanded wording: every rational Hodge class is a FINITE rational
linear combination of classes of genuine codimension-p irreducible algebraic
subvarieties (represented by their generic points). -/
def EveryHodgeClassIsFiniteRationalCombination : Prop :=
  ∀ p : Nat,
  ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
    alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ∃ phi : FiniteCodimensionPresentation V.X p,
        phi.sum (fun x q =>
          q • H.cycleClass p (codimensionPointCycle V.X p x)) = alpha

/-- The repo's Stage-2G target is EXACTLY the ordinary elementwise rational
Hodge conjecture. -/
theorem everyHodgeClassIsRationalAlgebraic_iff_stage2G :
    EveryHodgeClassIsRationalAlgebraic H ↔
      BigradedBettiHodgeStatement V H := by
  constructor
  · intro h p alpha halpha
    exact h p alpha halpha
  · intro h p alpha halpha
    exact h p halpha

/-- On a projective carrier, the one-cycle wording and the literal finite
rational-combination wording are equivalent. -/
theorem rationalAlgebraic_iff_finiteRationalCombination :
    EveryHodgeClassIsRationalAlgebraic H ↔
      EveryHodgeClassIsFiniteRationalCombination H := by
  constructor
  · intro h p alpha halpha
    rcases h p alpha halpha with ⟨Z, hZ⟩
    letI : CompactSpace V.X := smoothProjectiveCompactSpace V
    let phi := presentationOfNativeCycle V.X p Z
    refine ⟨phi, ?_⟩
    have hmap :=
      linearMap_realizeFiniteCodimensionPresentation
        V.X p (H.cycleClass p) phi
    have hreal : realizeFiniteCodimensionPresentation V.X p phi = Z := by
      exact realize_presentationOfNativeCycle V.X p Z
    rw [hreal] at hmap
    exact hmap.symm.trans hZ
  · intro h p alpha halpha
    rcases h p alpha halpha with ⟨phi, hphi⟩
    refine ⟨realizeFiniteCodimensionPresentation V.X p phi, ?_⟩
    calc
      H.cycleClass p (realizeFiniteCodimensionPresentation V.X p phi)
          = phi.sum (fun x q =>
              q • H.cycleClass p (codimensionPointCycle V.X p x)) :=
            linearMap_realizeFiniteCodimensionPresentation
              V.X p (H.cycleClass p) phi
      _ = alpha := hphi

/-- **EXACT CLAY-STYLE NORMAL FORM.**
All three formulations coincide:
1. the Stage-2G range inclusion;
2. every rational Hodge class has an algebraic-cycle representative;
3. every rational Hodge class is a finite rational linear combination of
   irreducible codimension-p algebraic cycle classes. -/
theorem exact_rational_hodge_conjecture_normal_form :
    BigradedBettiHodgeStatement V H ↔
      EveryHodgeClassIsRationalAlgebraic H := by
  exact everyHodgeClassIsRationalAlgebraic_iff_stage2G H |>.symm

/-- Same target in the most literal finite-sum wording. -/
theorem exact_rational_hodge_conjecture_finite_sum :
    BigradedBettiHodgeStatement V H ↔
      EveryHodgeClassIsFiniteRationalCombination H := by
  exact
    (exact_rational_hodge_conjecture_normal_form H).trans
      (rationalAlgebraic_iff_finiteRationalCombination H)

#check EveryHodgeClassIsRationalAlgebraic
#check EveryHodgeClassIsFiniteRationalCombination
#check everyHodgeClassIsRationalAlgebraic_iff_stage2G
#check rationalAlgebraic_iff_finiteRationalCombination
#check exact_rational_hodge_conjecture_normal_form
#check exact_rational_hodge_conjecture_finite_sum

#print axioms exact_rational_hodge_conjecture_normal_form
#print axioms exact_rational_hodge_conjecture_finite_sum


/-! ## GST RATIONAL CYCLE IMAGE ⇔ WHOLE-HODGE SPECTRAL KERNEL

The actual rational Hodge class is a rational cohomology vector whose
COMPLEXIFICATION lies in the full (p,p) Hodge summand. A supplied complex
Hodge-charge generator G_p is required to satisfy the exact spectral kernel
identity: ker G_p = H^(p,p). This condition is ONLY a condition on the
Hodge-bigrading and does not assert any algebraic-cycle preimage.

We prove the genuinely typed conversion of the user's two boxed formulas.
The rational Chow-image equality is exactly the additional range condition,
not a consequence of complex spectral kernel identification by itself.
-/

/-- Complexification of ACTUAL Stage2G rational Betti cohomology in degree 2p. -/
abbrev SpectralComplexCohomology (p : Nat) :=
  Complexification
    (RationalSingularCohomology H.analytification (2 * p))

/-- A chosen complex-linear Hodge-charge generator on one realized fiber.
The geometric spectral identity is a separate input to the comparison. -/
abbrev SpectralGenerator (p : Nat) :=
  SpectralComplexCohomology H p →ₗ[ℂ]
    SpectralComplexCohomology H p

/-- Rational zero-charge locus: the PREIMAGE of the complex spectral kernel
along the canonical rational-to-complex class embedding. No cycles assumed. -/
noncomputable def rationalSpectralKernel
    (p : Nat) (G : SpectralGenerator H p) :
    Submodule ℚ (RationalSingularCohomology H.analytification (2 * p)) :=
  ((LinearMap.ker G).restrictScalars ℚ).comap
    (complexificationMapQ
      (RationalSingularCohomology H.analytification (2 * p)))

/-- Identifying the COMPLEX spectral kernel with the WHOLE complex (p,p)
component automatically identifies its rational restriction with the
existing actual Stage2G rational Hodge fiber. Not a Chow-surjectivity input. -/
theorem rationalSpectralKernel_eq_rationalHodge
    (p : Nat) (G : SpectralGenerator H p)
    (hG : LinearMap.ker G = (H.hodgeBigrading p).ppComponent) :
    rationalSpectralKernel H p G =
      rationalHodgeSubspace (H.hodgeBigrading p) := by
  unfold rationalSpectralKernel rationalHodgeSubspace
  rw [hG]

/-- The EXACT reduction of rational algebraicity to a cycle-class RANGE
covering the rational spectral kernel. No surjectivity is built into G. -/
theorem exactHodge_iff_spectralKernel_in_nativeRange
    (G : ∀ p : Nat, SpectralGenerator H p)
    (hG : ∀ p : Nat,
       LinearMap.ker (G p) = (H.hodgeBigrading p).ppComponent) :
    EveryHodgeClassIsRationalAlgebraic H ↔
      ∀ p : Nat, rationalSpectralKernel H p (G p) ≤
        LinearMap.range (H.cycleClass p) := by
  constructor
  · intro h p alpha halpha
    have hpp : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) := by
      rw [← rationalSpectralKernel_eq_rationalHodge H p (G p) (hG p)]
      exact halpha
    obtain ⟨Z, hZ⟩ := h p alpha hpp
    exact ⟨Z, hZ⟩
  · intro h p alpha halpha
    have hspectral : alpha ∈ rationalSpectralKernel H p (G p) := by
      rw [rationalSpectralKernel_eq_rationalHodge H p (G p) (hG p)]
      exact halpha
    exact h p hspectral

/-- The true canonical cycle class sends ACTUAL algebraic cycles to
(p,p); Stage2G stores a linear class map without claiming this geometric
property, so it is retained as an explicit SOURCE-SEMANTICS hypothesis. -/
def CycleClassHodgeCompatible : Prop :=
  ∀ p : Nat,
    LinearMap.range (H.cycleClass p) ≤
      rationalHodgeSubspace (H.hodgeBigrading p)

/-- Under the actual Hodge-type property of the canonical algebraic cycle
class, rational Hodge algebraicity is equivalent to literal image=kernel.
The geometric spectral identity alone supplies NO source surjectivity. -/
theorem exactHodge_iff_nativeRange_eq_spectralKernel
    (G : ∀ p : Nat, SpectralGenerator H p)
    (hG : ∀ p : Nat,
       LinearMap.ker (G p) = (H.hodgeBigrading p).ppComponent)
    (hcycle : CycleClassHodgeCompatible H) :
    EveryHodgeClassIsRationalAlgebraic H ↔
      ∀ p : Nat, LinearMap.range (H.cycleClass p) =
        rationalSpectralKernel H p (G p) := by
  constructor
  · intro h p
    apply le_antisymm
    · rw [rationalSpectralKernel_eq_rationalHodge H p (G p) (hG p)]
      exact hcycle p
    · exact (exactHodge_iff_spectralKernel_in_nativeRange H G hG).mp h p
  · intro heq
    apply (exactHodge_iff_spectralKernel_in_nativeRange H G hG).mpr
    intro p
    rw [← heq p]

#check SpectralComplexCohomology
#check SpectralGenerator
#check rationalSpectralKernel
#check rationalSpectralKernel_eq_rationalHodge
#check exactHodge_iff_spectralKernel_in_nativeRange
#check CycleClassHodgeCompatible
#check exactHodge_iff_nativeRange_eq_spectralKernel

#print axioms rationalSpectralKernel_eq_rationalHodge
#print axioms exactHodge_iff_spectralKernel_in_nativeRange
#print axioms exactHodge_iff_nativeRange_eq_spectralKernel

end GSTClassicalHodgeExactClayStatement
