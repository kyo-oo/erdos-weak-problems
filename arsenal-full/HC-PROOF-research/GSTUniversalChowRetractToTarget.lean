import GSTGeometricRealizationStage2G

/-!
# GST exact descent to an ARBITRARY TARGET VARIETY X

Target:
For every smooth projective complex X, p, and rational (p,p)
Hodge alpha, produce a genuine rational algebraic cycle Z on X.

This module constructs Z on X, not just a primitive on X x X.
It uses an independently geometric Chow correspondence from a source Y,
where the needed Hodge class has actually been represented.

For Y=X x X, a cohomological section is
  alpha |-> pr1^*(alpha) cup pr2^*(h^d)/deg(h^d)
and projection pr1_* is a left inverse.
Native proper pushforward and Betti Gysin must commute with cycleClass.
The source Hodge representatives need independent geometric proofs.
The known universal alternating product primitive alone does not supply them.

No arbitrary target-cycle selector is assumed, and no universal
Hodge theorem is claimed without the concrete geometric source theorem.
-/

set_option maxHeartbeats 5000000
noncomputable section

open AlgebraicGeometry
open GSTProjectiveOverC
open GSTGeometricRealizationStage2D
open GSTGeometricRealizationStage2F
open GSTGeometricRealizationStage2G

namespace GSTUniversalChowRetractToTarget

/-- Actual native Chow and rational Betti correspondence for a
source Y and a target X. Every field is geometric input, and
NONE asserts a target Hodge class is algebraic. -/
structure NativeHodgeRetract
    (Y X : SmoothProjectiveComplexScheme)
    (D : HodgeBigradedBettiData Y)
    (H : HodgeBigradedBettiData X)
    (q p : Nat) where
  native :
    codimensionCycles Y.X q →ₗ[ℚ] codimensionCycles X.X p
  betti :
    RationalSingularCohomology D.analytification (2 * q) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  hodgeSection :
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology D.analytification (2 * q)
  section_is_hodge :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        hodgeSection alpha ∈ rationalHodgeSubspace (D.hodgeBigrading q)
  betti_retract :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      betti (hodgeSection alpha) = alpha
  cycleClass_natural :
    ∀ Z : codimensionCycles Y.X q,
      H.cycleClass p (native Z) = betti (D.cycleClass q Z)

variable {Y X : SmoothProjectiveComplexScheme}
variable {D : HodgeBigradedBettiData Y}
variable {H : HodgeBigradedBettiData X}
variable {q p : Nat}

/-- Given a SOURCE native cycle for the cohomological section,
construct the actual TARGET rational algebraic cycle, through the
geometrically natural native correspondence. -/
theorem construct_target_cycle_from_source_hodge_lift
    (R : NativeHodgeRetract Y X D H q p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hsource :
      ∃ Z : codimensionCycles Y.X q,
        D.cycleClass q Z = R.hodgeSection alpha) :
    ∃ Z : codimensionCycles X.X p,
      H.cycleClass p Z = alpha := by
  obtain ⟨Z, hZ⟩ := hsource
  refine ⟨R.native Z, ?_⟩
  calc
    H.cycleClass p (R.native Z) =
        R.betti (D.cycleClass q Z) := R.cycleClass_natural Z
    _ = R.betti (R.hodgeSection alpha) := by rw [hZ]
    _ = alpha := R.betti_retract alpha

/-- Full Hodge on X is DERIVED if X is a true Chow motivic
retract of a source Y with previously established Hodge
algebraicity. There is no target algebraicity assumption. -/
theorem every_target_hodge_class_from_solved_source
    (R : NativeHodgeRetract Y X D H q p)
    (hY : ∀ beta : RationalSingularCohomology D.analytification (2 * q),
      beta ∈ rationalHodgeSubspace (D.hodgeBigrading q) →
        ∃ Z : codimensionCycles Y.X q,
          D.cycleClass q Z = beta) :
    ∀ alpha : RationalSingularCohomology H.analytification (2 * p),
      alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
        ∃ Z : codimensionCycles X.X p,
          H.cycleClass p Z = alpha := by
  intro alpha hAlpha
  exact construct_target_cycle_from_source_hodge_lift R alpha
    (hY (R.hodgeSection alpha) (R.section_is_hodge alpha hAlpha))

/-- Direct compatibility with the original omniversal GST ghost
separator: the actual target Hodge fiber lies in the native-cycle
range when the geometric retract source has been solved. -/
theorem target_hodge_subset_native_cycleClass_range
    (R : NativeHodgeRetract Y X D H q p)
    (hY : ∀ beta : RationalSingularCohomology D.analytification (2 * q),
      beta ∈ rationalHodgeSubspace (D.hodgeBigrading q) →
        ∃ Z : codimensionCycles Y.X q,
          D.cycleClass q Z = beta) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha hAlpha
  obtain ⟨Z, hZ⟩ :=
    every_target_hodge_class_from_solved_source R hY alpha hAlpha
  exact ⟨Z, hZ⟩

/-- Necessary source limitation:
the genuine target of an algebraic source cycle is again algebraic.
It cannot equal a hypothetical target class absent from the native
cycle-class range. A correspondence alone does not manufacture
unrepresented Hodge classes. -/
theorem no_unrepresented_target_from_algebraic_source
    (R : NativeHodgeRetract Y X D H q p)
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hmissing : alpha ∉ LinearMap.range (H.cycleClass p))
    (Z : codimensionCycles Y.X q) :
    R.betti (D.cycleClass q Z) ≠ alpha := by
  intro heq
  apply hmissing
  refine ⟨R.native Z, ?_⟩
  rw [R.cycleClass_natural]
  exact heq


/-! ## Scheme-typed, arbitrary-codimension GST geometric world birth

This upgrades the former abstract GST world-birth calculus into the actual
native codimension-cycle types of Mathlib smooth projective complex schemes.

For a chosen codimension p on a genuine target scheme, each finite source
index carries its OWN genuine smooth projective source scheme and codimension
q_i. The native assembly maps LAND IN codimensionCycles target.X p and the
Betti assembly maps LAND IN genuine rational singular cohomology of that target.
The required geometric Hodge expansion is a statement about the target's
actual Hodge bigrading, NOT an arbitrary vector-space presentation.

Projective bundles and blowups instantiate these fields through hyperplane/
exceptional-divisor intersection and Gysin operations. Their concrete scheme
constructions must be provided separately: do not mistake a packet containing
their comparison laws for an unconditional construction of all such maps.
-/

open scoped BigOperators

/-- Finite geometric birth with genuinely different source SCHEMES and
codimensions, and direct compatibility with the original cycleClass maps.
In particular the target cycle map is not chosen to make surjectivity true. -/
structure GeometricMultiSourceChowBirth
    (X : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData X)
    (p : ℕ)
    (ι : Type*) [Fintype ι] where
  source : ι → SmoothProjectiveComplexScheme
  data : (i : ι) → HodgeBigradedBettiData (source i)
  codim : ι → ℕ
  native : (i : ι) →
    codimensionCycles (source i).X (codim i) →ₗ[ℚ]
      codimensionCycles X.X p
  betti : (i : ι) →
    RationalSingularCohomology (data i).analytification (2 * codim i) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  naturality : ∀ i (Z : codimensionCycles (source i).X (codim i)),
    H.cycleClass p (native i Z) =
      betti i ((data i).cycleClass (codim i) Z)
  hodgeSpan : ∀ alpha : RationalSingularCohomology
      H.analytification (2 * p),
    alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      ∃ beta : (i : ι) →
        RationalSingularCohomology (data i).analytification (2 * codim i),
        (∀ i, beta i ∈ rationalHodgeSubspace
          ((data i).hodgeBigrading (codim i))) ∧
        (∑ i : ι, betti i (beta i)) = alpha

variable {ι : Type*} [Fintype ι]

/-- An EXPLICIT rational algebraic cycle on the actual target scheme:
assemble the native source cycles using the genuine Chow maps and
certify that its rational Betti class is precisely the target class. -/
theorem actual_target_cycle_of_geometric_multi_source_birth
    (P : GeometricMultiSourceChowBirth X H p ι)
    (hSource : ∀ i : ι,
      BigradedBettiHodgeStatement (P.source i) (P.data i))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hAlpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles X.X p, H.cycleClass p Z = alpha := by
  classical
  obtain ⟨beta, hHodge, hReconstruct⟩ := P.hodgeSpan alpha hAlpha
  have hWitness : ∀ i : ι,
      ∃ Z : codimensionCycles (P.source i).X (P.codim i),
        (P.data i).cycleClass (P.codim i) Z = beta i := by
    intro i
    exact hSource i (P.codim i) (hHodge i)
  let native : (i : ι) → codimensionCycles (P.source i).X (P.codim i) :=
    fun i => Classical.choose (hWitness i)
  refine ⟨∑ i : ι, P.native i (native i), ?_⟩
  calc
    H.cycleClass p (∑ i : ι, P.native i (native i)) =
        ∑ i : ι, H.cycleClass p (P.native i (native i)) := by
          rw [map_sum]
    _ = ∑ i : ι,
        P.betti i ((P.data i).cycleClass (P.codim i) (native i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact P.naturality i (native i)
    _ = ∑ i : ι, P.betti i (beta i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Classical.choose_spec (hWitness i)]
    _ = alpha := hReconstruct

/-- Scheme-typed (p,p) rational-Hodge surjectivity under a genuinely
geometric projective-bundle/blowup source splitting, with no fixed rank
or dimension assumption. This is directly a theorem about the ORIGINAL
target cycleClass map, not an abstract GST surrogate. -/
theorem actual_hodge_range_of_geometric_multi_source_birth
    (P : GeometricMultiSourceChowBirth X H p ι)
    (hSource : ∀ i : ι,
      BigradedBettiHodgeStatement (P.source i) (P.data i)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) := by
  intro alpha hAlpha
  obtain ⟨Z, hZ⟩ :=
    actual_target_cycle_of_geometric_multi_source_birth
      P hSource alpha hAlpha
  exact ⟨Z, hZ⟩


/-! ## Full coordinate-readout interface for genuine bundle and blowup formulas

The previous multivariate birth required a Hodge spanning equation.
A TRUE geometric blowup or projective bundle instead supplies explicit
cohomological extraction/readout operators (pullback, exceptional
Gysin inverse and fiber integration) and an exact reconstruction.

This law assembles a scheme-typed birth from those READOUT operations
and their Hodge preservation, deriving the Hodge spanning equation.
The underlying geometric Gysin and bundle maps are separate
scheme-level instances to be proved; the Lean record does not
silently instantiate them for an arbitrary X.
-/

/-- A certified actual Chow/Gysin splitting with explicit independent
cohomological readout from target to ALL source schemes.
Unlike a freely chosen Hodge class-to-cycle map, each readout stays in
COHOMOLOGY and its rational Hodge type is verified. -/
structure GeometricSplitGysinPacket
    (X : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData X)
    (p : ℕ) (ι : Type*) [Fintype ι] where
  source : ι → SmoothProjectiveComplexScheme
  data : (i : ι) → HodgeBigradedBettiData (source i)
  codim : ι → ℕ
  native : (i : ι) →
    codimensionCycles (source i).X (codim i) →ₗ[ℚ]
      codimensionCycles X.X p
  betti : (i : ι) →
    RationalSingularCohomology (data i).analytification (2 * codim i) →ₗ[ℚ]
      RationalSingularCohomology H.analytification (2 * p)
  readout : (i : ι) →
    RationalSingularCohomology H.analytification (2 * p) →ₗ[ℚ]
      RationalSingularCohomology (data i).analytification (2 * codim i)
  naturality : ∀ i (Z : codimensionCycles (source i).X (codim i)),
    H.cycleClass p (native i Z) =
      betti i ((data i).cycleClass (codim i) Z)
  readout_hodge : ∀ i
      (alpha : RationalSingularCohomology H.analytification (2 * p)),
    alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p) →
      readout i alpha ∈
        rationalHodgeSubspace ((data i).hodgeBigrading (codim i))
  reconstruct : ∀ alpha : RationalSingularCohomology
      H.analytification (2 * p),
    (∑ i : ι, betti i (readout i alpha)) = alpha

/-- Convert the actual projective-bundle / exceptional-Gysin
readout data into the previously verified SCHEME-TYPED birth law.
Importantly the Hodge decomposition is now DEDUCED from actual
cohomology readouts and the reconstruction identity. -/
noncomputable def GeometricSplitGysinPacket.toChowBirth
    (P : GeometricSplitGysinPacket X H p ι) :
    GeometricMultiSourceChowBirth X H p ι where
  source := P.source
  data := P.data
  codim := P.codim
  native := P.native
  betti := P.betti
  naturality := P.naturality
  hodgeSpan := by
    intro alpha hAlpha
    refine ⟨fun i => P.readout i alpha, ?_, P.reconstruct alpha⟩
    intro i
    exact P.readout_hodge i alpha hAlpha

/-- Actual codimension-p Hodge surjectivity on a TARGET SCHEME,
deduced from fully specified Chow/Gysin readouts and actual
source-scheme Hodge surjectivity; no target-cycle witness field. -/
theorem actual_chow_cycle_of_geometric_gysin_split
    (P : GeometricSplitGysinPacket X H p ι)
    (hSource : ∀ i : ι,
      BigradedBettiHodgeStatement (P.source i) (P.data i))
    (alpha : RationalSingularCohomology H.analytification (2 * p))
    (hAlpha : alpha ∈ rationalHodgeSubspace (H.hodgeBigrading p)) :
    ∃ Z : codimensionCycles X.X p,
      H.cycleClass p Z = alpha := by
  exact actual_target_cycle_of_geometric_multi_source_birth
    P.toChowBirth hSource alpha hAlpha

/-- One weight of the genuine Hodge conjecture on X, extracted from
a verified geometrical decomposition of the same Betti and Chow
sources, for any finite number of exceptional/projective-bundle terms. -/
theorem actual_hodge_of_geometric_gysin_split
    (P : GeometricSplitGysinPacket X H p ι)
    (hSource : ∀ i : ι,
      BigradedBettiHodgeStatement (P.source i) (P.data i)) :
    rationalHodgeSubspace (H.hodgeBigrading p) ≤
      LinearMap.range (H.cycleClass p) :=
  actual_hodge_range_of_geometric_multi_source_birth
    P.toChowBirth hSource


/-! ## Exact projective-bundle Chow/Hodge formula, scheme-typed

For an actual rank-r projective bundle T=P(E) over a smooth projective
complex base B, its codimension-p Chow and rational Hodge decompositions
have source summands CH^(p-j)(B) and Hdg^(p-j)(B), indexed by j<r.
The Gysin native map is xi^j * pi^*, while the Hodge map is the same
operation on cohomology. The extractors are determined by the projective
bundle formula and satisfy SUM_j xi^j*pi^*(read_j(alpha))=alpha.

Here the FULL index and codimension shifts are realized by the actual
native codimension-cycle carrier of the base and total schemes.
No map from a chosen target Hodge alpha to an invented native preimage
occurs. An ACTUAL geometric projectivization must instantiate the
pullback, hyperplane-cup, and extraction maps below separately.
-/

/-- Fully degree-indexed geometric projective-bundle certificate.
Each forward native map has source CH^(p-j)(B), not an unrelated
cycle carrier, and target CH^p(T) on the actual total scheme. -/
structure SchemeProjectiveBundleGysin
    (B T : SmoothProjectiveComplexScheme)
    (HB : HodgeBigradedBettiData B)
    (HT : HodgeBigradedBettiData T)
    (r p : ℕ) where
  nativeXiPull : (j : Fin r) →
    codimensionCycles B.X (p-j.val) →ₗ[ℚ] codimensionCycles T.X p
  bettiXiPull : (j : Fin r) →
    RationalSingularCohomology HB.analytification (2*(p-j.val)) →ₗ[ℚ]
      RationalSingularCohomology HT.analytification (2*p)
  hodgeReadout : (j : Fin r) →
    RationalSingularCohomology HT.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HB.analytification (2*(p-j.val))
  cycleClass_natural : ∀ j (Z : codimensionCycles B.X (p-j.val)),
    HT.cycleClass p (nativeXiPull j Z) =
      bettiXiPull j (HB.cycleClass (p-j.val) Z)
  readout_hodge : ∀ j
    (alpha : RationalSingularCohomology HT.analytification (2*p)),
    alpha ∈ rationalHodgeSubspace (HT.hodgeBigrading p) →
    hodgeReadout j alpha ∈
      rationalHodgeSubspace (HB.hodgeBigrading (p-j.val))
  reconstruct : ∀ alpha :
      RationalSingularCohomology HT.analytification (2*p),
    (∑ j : Fin r, bettiXiPull j (hodgeReadout j alpha)) = alpha

/-- Convert TRUE projective-bundle codimension indexing to the
previous kernel-checked actual scheme Gysin splitting. -/
noncomputable def SchemeProjectiveBundleGysin.toSplit
    {B T : SmoothProjectiveComplexScheme}
    {HB : HodgeBigradedBettiData B}
    {HT : HodgeBigradedBettiData T}
    {r p : ℕ}
    (P : SchemeProjectiveBundleGysin B T HB HT r p) :
    GeometricSplitGysinPacket T HT p (Fin r) where
  source := fun _ => B
  data := fun _ => HB
  codim := fun j => p-j.val
  native := P.nativeXiPull
  betti := P.bettiXiPull
  readout := P.hodgeReadout
  naturality := P.cycleClass_natural
  readout_hodge := P.readout_hodge
  reconstruct := P.reconstruct

/-- Build the ACTUAL CH^p cycle for every rational Hodge (p,p)
class on a verified geometric projective bundle from the base's
genuine algebraic cycles, for any fiber rank and total dimension. -/
theorem hodge_cycles_on_geometric_projective_bundle
    {B T : SmoothProjectiveComplexScheme}
    {HB : HodgeBigradedBettiData B}
    {HT : HodgeBigradedBettiData T}
    {r p : ℕ}
    (P : SchemeProjectiveBundleGysin B T HB HT r p)
    (hBase : BigradedBettiHodgeStatement B HB) :
    rationalHodgeSubspace (HT.hodgeBigrading p) ≤
      LinearMap.range (HT.cycleClass p) := by
  apply actual_hodge_of_geometric_gysin_split P.toSplit
  intro j
  exact hBase


/-! ## Actual blowup source degrees and exceptional Gysin packet

For a blowup along a smooth projective center of codimension c, the
actual source index is Option (Fin (c-1)): the base source and exactly
c-1 exceptional center sources with Hodge degrees p-(j+1).
All native source/target types below are true scheme codimension-cycle
spaces. The cohomological maps and compatibility are external geometric
inputs; these declarations do NOT construct the blowup in Mathlib.
-/

def blowupHodgeSource
    (B C : SmoothProjectiveComplexScheme) (c : ℕ) :
    Option (Fin (c-1)) → SmoothProjectiveComplexScheme
  | none => B
  | some _ => C

def blowupHodgeData
    {B C : SmoothProjectiveComplexScheme}
    (HB : HodgeBigradedBettiData B)
    (HC : HodgeBigradedBettiData C)
    (c : ℕ) :
    (i : Option (Fin (c-1))) →
      HodgeBigradedBettiData (blowupHodgeSource B C c i)
  | none => HB
  | some _ => HC

def blowupSourceCodim (p c : ℕ) :
    Option (Fin (c-1)) → ℕ
  | none => p
  | some j => p-(j.val+1)

/-- Genuine Chow/Gysin blowup source indexing and class comparison.
Gysin maps and Hodge readouts must come from real pullback and
exceptional divisor operations on the given schemes. -/
structure SchemeBlowupGysin
    (B C T : SmoothProjectiveComplexScheme)
    (HB : HodgeBigradedBettiData B)
    (HC : HodgeBigradedBettiData C)
    (HT : HodgeBigradedBettiData T)
    (c p : ℕ) where
  native : (i : Option (Fin (c-1))) →
    codimensionCycles (blowupHodgeSource B C c i).X
      (blowupSourceCodim p c i) →ₗ[ℚ] codimensionCycles T.X p
  betti : (i : Option (Fin (c-1))) →
    RationalSingularCohomology
      (blowupHodgeData HB HC c i).analytification
      (2 * blowupSourceCodim p c i) →ₗ[ℚ]
      RationalSingularCohomology HT.analytification (2*p)
  readout : (i : Option (Fin (c-1))) →
    RationalSingularCohomology HT.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology
        (blowupHodgeData HB HC c i).analytification
        (2 * blowupSourceCodim p c i)
  cycleClass_natural : ∀ i (Z :
      codimensionCycles (blowupHodgeSource B C c i).X
        (blowupSourceCodim p c i)),
    HT.cycleClass p (native i Z) =
      betti i ((blowupHodgeData HB HC c i).cycleClass
        (blowupSourceCodim p c i) Z)
  readout_hodge : ∀ i (alpha :
      RationalSingularCohomology HT.analytification (2*p)),
    alpha ∈ rationalHodgeSubspace (HT.hodgeBigrading p) →
      readout i alpha ∈
        rationalHodgeSubspace ((blowupHodgeData HB HC c i).hodgeBigrading
          (blowupSourceCodim p c i))
  reconstruct : ∀ alpha :
      RationalSingularCohomology HT.analytification (2*p),
    (∑ i : Option (Fin (c-1)), betti i (readout i alpha)) = alpha

noncomputable def SchemeBlowupGysin.toSplit
    {B C T : SmoothProjectiveComplexScheme}
    {HB : HodgeBigradedBettiData B}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {c p : ℕ}
    (P : SchemeBlowupGysin B C T HB HC HT c p) :
    GeometricSplitGysinPacket T HT p (Option (Fin (c-1))) where
  source := blowupHodgeSource B C c
  data := blowupHodgeData HB HC c
  codim := blowupSourceCodim p c
  native := P.native
  betti := P.betti
  readout := P.readout
  naturality := P.cycleClass_natural
  readout_hodge := P.readout_hodge
  reconstruct := P.reconstruct

/-- Build actual target codimension-p cycles from the actual base
and center cycles via verified Gysin splitting, for arbitrary
blowup codimension and any ambient geometric dimension. -/
theorem hodge_cycles_on_geometric_blowup
    {B C T : SmoothProjectiveComplexScheme}
    {HB : HodgeBigradedBettiData B}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {c p : ℕ}
    (P : SchemeBlowupGysin B C T HB HC HT c p)
    (hBase : BigradedBettiHodgeStatement B HB)
    (hCenter : BigradedBettiHodgeStatement C HC) :
    rationalHodgeSubspace (HT.hodgeBigrading p) ≤
      LinearMap.range (HT.cycleClass p) := by
  apply actual_hodge_of_geometric_gysin_split P.toSplit
  intro i
  cases i with
  | none => exact hBase
  | some j => exact hCenter


/-! ## Unrestricted-center GST codimension-two birth

A major geometric gain is available WITHOUT solving Hodge for the
blowup center. In codimension two, the only exceptional cohomology
source weights are ZERO and ONE, irrespective of the dimension
or other Hodge directions of the center. Thus every actual smooth
blowup preserves rational (2,2) Hodge algebraicity using only
the classical Hodge-(0,0) unit and divisor (1,1) cycles of the
center, not its full unknown middle primitive Hodge geometry.

The following strengthens the earlier all-weights birth theorem
by replacing the unjustified requirement that the center is
FULLY Hodge-complete with ONLY the relevant center weights.

A projective rational starting world can then be blown up an
ARBITRARY finite number of times along smooth centers of ANY
dimension, obtaining actual native representatives in CH^2
at EVERY stage; no center's higher Hodge conjecture is assumed.
The true geometric blowup Gysin comparison maps remain a
separate instantiation obligation.
-/

/-- Algebraicity at a SPECIFIC rational Hodge weight of the given
actual smooth projective scheme, not at all weights. -/
def HodgeAtWeight
    (V : SmoothProjectiveComplexScheme)
    (H : HodgeBigradedBettiData V)
    (p : ℕ) : Prop :=
  rationalHodgeSubspace (H.hodgeBigrading p) ≤
    LinearMap.range (H.cycleClass p)

/-- Construct an actual native target cycle using ONLY algebraicity
of the exact source weights selected by the geometric splitting.
This strictly strengthens the old theorem requiring every source
to satisfy the WHOLE Hodge conjecture at all codimensions. -/
theorem hodge_at_fixed_weight_of_geometric_birth
    {X : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData X}
    {p : ℕ} {ι : Type*} [Fintype ι]
    (P : GeometricMultiSourceChowBirth X H p ι)
    (hSources : ∀ i : ι,
      HodgeAtWeight (P.source i) (P.data i) (P.codim i)) :
    HodgeAtWeight X H p := by
  classical
  intro alpha hAlpha
  obtain ⟨beta, hHodge, hReconstruct⟩ := P.hodgeSpan alpha hAlpha
  have hw : ∀ i : ι,
      ∃ Z : codimensionCycles (P.source i).X (P.codim i),
        (P.data i).cycleClass (P.codim i) Z = beta i := by
    intro i
    exact hSources i (hHodge i)
  let native : (i : ι) →
      codimensionCycles (P.source i).X (P.codim i) :=
    fun i => Classical.choose (hw i)
  refine ⟨∑ i : ι, P.native i (native i), ?_⟩
  calc
    H.cycleClass p (∑ i : ι, P.native i (native i)) =
        ∑ i : ι, H.cycleClass p (P.native i (native i)) := by
          rw [map_sum]
    _ = ∑ i : ι, P.betti i
        ((P.data i).cycleClass (P.codim i) (native i)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact P.naturality i (native i)
    _ = ∑ i : ι, P.betti i (beta i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Classical.choose_spec (hw i)]
    _ = alpha := hReconstruct

/-- True Gysin blowup transfer with no high-codimension algebraicity
assumption on the center: in target weight p>0 each relevant
exceptional source weight is strictly smaller than p. -/
theorem geometric_blowup_from_strictly_lower_center_weights
    {B C T : SmoothProjectiveComplexScheme}
    {HB : HodgeBigradedBettiData B}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {c p : ℕ}
    (P : SchemeBlowupGysin B C T HB HC HT c p)
    (hp : 0 < p)
    (hBase : HodgeAtWeight B HB p)
    (hCenter : ∀ q : ℕ, q < p → HodgeAtWeight C HC q) :
    HodgeAtWeight T HT p := by
  apply hodge_at_fixed_weight_of_geometric_birth P.toSplit.toChowBirth
  intro i
  cases i with
  | none => exact hBase
  | some j =>
      exact hCenter (p-(j.val+1)) (by omega)

/-- ALL-DIMENSION smooth-center codimension-two theorem.
No Hodge assumption of center codimensions 2,3,... is made:
only genuine (0,0) and (1,1) algebraic cycle classes suffice. -/
theorem geometric_blowup_codimension_two_from_center_divisors
    {B C T : SmoothProjectiveComplexScheme}
    {HB : HodgeBigradedBettiData B}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {c : ℕ}
    (P : SchemeBlowupGysin B C T HB HC HT c 2)
    (hBase : HodgeAtWeight B HB 2)
    (hCenterZero : HodgeAtWeight C HC 0)
    (hCenterDivisor : HodgeAtWeight C HC 1) :
    HodgeAtWeight T HT 2 := by
  apply geometric_blowup_from_strictly_lower_center_weights
    P (by omega) hBase
  intro q hq
  interval_cases q
  · exact hCenterZero
  · exact hCenterDivisor

/-- NEW unlimited GST construction in the FIRST nontrivial Hodge
codimension, permitting each geometric blowup center to have
arbitrarily complicated UNKNOWN higher primitive Hodge classes. -/
inductive SchemeTypedGSTCodimensionTwoBlowupTower :
    (V : SmoothProjectiveComplexScheme) →
    HodgeBigradedBettiData V → Prop where
  | seed {V : SmoothProjectiveComplexScheme}
      {H : HodgeBigradedBettiData V}
      (h : HodgeAtWeight V H 2) :
      SchemeTypedGSTCodimensionTwoBlowupTower V H
  | blowup
      {B C T : SmoothProjectiveComplexScheme}
      {HB : HodgeBigradedBettiData B}
      {HC : HodgeBigradedBettiData C}
      {HT : HodgeBigradedBettiData T}
      (c : ℕ)
      (hBase : SchemeTypedGSTCodimensionTwoBlowupTower B HB)
      (hCenterZero : HodgeAtWeight C HC 0)
      (hCenterDivisor : HodgeAtWeight C HC 1)
      (P : SchemeBlowupGysin B C T HB HC HT c 2) :
      SchemeTypedGSTCodimensionTwoBlowupTower T HT

/-- Every codimension-two rational Hodge class on every actual
scheme in this arbitrary-depth blowup tower has a genuine
native codimension-two rational algebraic cycle representative.
This holds regardless of center dimension, middle cohomology,
CM behavior or higher Hodge algebraicity. -/
theorem unrestricted_center_blowup_tower_hodge_two
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (h : SchemeTypedGSTCodimensionTwoBlowupTower V H) :
    HodgeAtWeight V H 2 := by
  induction h with
  | seed h0 =>
      exact h0
  | blowup c hb h0 h1 P ih =>
      exact geometric_blowup_codimension_two_from_center_divisors
        P ih h0 h1


/-! ## GST unconditional codimension-two domination route

Unlike mere blowup recoordination, generically finite domination
produces an ACTUAL algebraic-cycle representative on an arbitrary
target X from a SOLVED source Y.

If a resolved projective rational parametrization Y -> X has
degree d!=0, then the geometric push-pull formula
 f_*f^*(alpha) = d alpha
allows us to construct
 Z_X = (1/d) f_* Z_Y,
where Z_Y is a genuine native codimension-two source cycle
representing f^*(alpha). In contrast to an arbitrary chosen
target representative, the input is a rational morphism resolved
from actual projective geometry and its natural Chow/Betti maps.

The two rational cohomology maps and the Chow pushforward
must be the GENUINE maps of a generically finite morphism;
their definition and comparison are still scheme-level
certificates to be constructed. In particular, NOT every
smooth projective complex X admits a generically finite
rational parametrization. This directly establishes the
unirational subclass, not the original universal conjecture.
-/

/-- Exact true geometric finite-degree push-pull data at (2,2)
for a dominant generically finite morphism of smooth projective
complex SCHEMES. There is no Hodge-to-Chow target section. -/
structure SchemeFiniteDominantTwoTransfer
    (Y X : SmoothProjectiveComplexScheme)
    (HY : HodgeBigradedBettiData Y)
    (HX : HodgeBigradedBettiData X) where
  degree : ℚ
  degree_ne_zero : degree ≠ 0
  nativePush :
    codimensionCycles Y.X 2 →ₗ[ℚ] codimensionCycles X.X 2
  bettiPush :
    RationalSingularCohomology HY.analytification 4 →ₗ[ℚ]
      RationalSingularCohomology HX.analytification 4
  bettiPull :
    RationalSingularCohomology HX.analytification 4 →ₗ[ℚ]
      RationalSingularCohomology HY.analytification 4
  pull_preserves_hodge :
    ∀ alpha : RationalSingularCohomology HX.analytification 4,
      alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading 2) →
      bettiPull alpha ∈
        rationalHodgeSubspace (HY.hodgeBigrading 2)
  native_betti_natural :
    ∀ Z : codimensionCycles Y.X 2,
      HX.cycleClass 2 (nativePush Z) =
        bettiPush (HY.cycleClass 2 Z)
  push_pull_degree :
    ∀ alpha : RationalSingularCohomology HX.analytification 4,
      bettiPush (bettiPull alpha) = degree • alpha

/-- CONCRETE actual target algebraic cycle, rather than an abstract
nonzero cohomology word: pull the rational Hodge target alpha
to the solved scheme Y, choose its known native source cycle,
push it forward and divide by the genuine nonzero mapping degree.
All cycle types are true algebraic scheme codimension-two carriers. -/
noncomputable def SchemeFiniteDominantTwoTransfer.constructNative
    {Y X : SmoothProjectiveComplexScheme}
    {HY : HodgeBigradedBettiData Y}
    {HX : HodgeBigradedBettiData X}
    (F : SchemeFiniteDominantTwoTransfer Y X HY HX)
    (hY : HodgeAtWeight Y HY 2)
    (alpha : RationalSingularCohomology HX.analytification 4)
    (hAlpha : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading 2)) :
    codimensionCycles X.X 2 :=
  F.degree⁻¹ • F.nativePush
    (Classical.choose
      (hY (F.pull_preserves_hodge alpha hAlpha)))

/-- The above explicit native target construction has EXACTLY the
original rational Hodge class. This theorem has NO assumption that
alpha was previously algebraic on X. Its source is a resolved,
independently cycle-complete geometric dominating variety. -/
theorem SchemeFiniteDominantTwoTransfer.constructNative_correct
    {Y X : SmoothProjectiveComplexScheme}
    {HY : HodgeBigradedBettiData Y}
    {HX : HodgeBigradedBettiData X}
    (F : SchemeFiniteDominantTwoTransfer Y X HY HX)
    (hY : HodgeAtWeight Y HY 2)
    (alpha : RationalSingularCohomology HX.analytification 4)
    (hAlpha : alpha ∈ rationalHodgeSubspace (HX.hodgeBigrading 2)) :
    HX.cycleClass 2 (F.constructNative hY alpha hAlpha) = alpha := by
  let Z : codimensionCycles Y.X 2 :=
    Classical.choose (hY (F.pull_preserves_hodge alpha hAlpha))
  have hZ : HY.cycleClass 2 Z = F.bettiPull alpha :=
    Classical.choose_spec (hY (F.pull_preserves_hodge alpha hAlpha))
  calc
    HX.cycleClass 2 (F.constructNative hY alpha hAlpha) =
        F.degree⁻¹ • (HX.cycleClass 2 (F.nativePush Z)) := by
          simp only [SchemeFiniteDominantTwoTransfer.constructNative, map_smul, Z]
    _ = F.degree⁻¹ • F.bettiPush (HY.cycleClass 2 Z) := by
          rw [F.native_betti_natural Z]
    _ = F.degree⁻¹ • F.bettiPush (F.bettiPull alpha) := by rw [hZ]
    _ = F.degree⁻¹ • (F.degree • alpha) := by rw [F.push_pull_degree]
    _ = alpha := by simp [smul_smul, F.degree_ne_zero]

/-- Hodge (2,2) is algebraic on ANY target admitting a proper
generically finite morphism from a scheme obtained by
arbitrarily many certified smooth blowups of a solved projective
source. No Hodge assumptions on higher primitive cohomology
of ANY exceptional center are made. This covers the
UNIRATIONAL class once the geometric resolution and finite
morphism certificates are instantiated. -/
theorem hodge_two_of_resolved_projective_domination
    {Y X : SmoothProjectiveComplexScheme}
    {HY : HodgeBigradedBettiData Y}
    {HX : HodgeBigradedBettiData X}
    (tower : SchemeTypedGSTCodimensionTwoBlowupTower Y HY)
    (F : SchemeFiniteDominantTwoTransfer Y X HY HX) :
    HodgeAtWeight X HX 2 := by
  intro alpha hAlpha
  let hY := unrestricted_center_blowup_tower_hodge_two tower
  exact ⟨F.constructNative hY alpha hAlpha,
    F.constructNative_correct hY alpha hAlpha⟩

#check SchemeFiniteDominantTwoTransfer
#check SchemeFiniteDominantTwoTransfer.constructNative
#check SchemeFiniteDominantTwoTransfer.constructNative_correct
#check hodge_two_of_resolved_projective_domination
#print axioms hodge_two_of_resolved_projective_domination

#check HodgeAtWeight
#check hodge_at_fixed_weight_of_geometric_birth
#check geometric_blowup_from_strictly_lower_center_weights
#check geometric_blowup_codimension_two_from_center_divisors
#check SchemeTypedGSTCodimensionTwoBlowupTower
#check unrestricted_center_blowup_tower_hodge_two
#print axioms unrestricted_center_blowup_tower_hodge_two

/-! ## Unbounded ACTUAL SCHEME-CARRIER GST geometric towers

This law finally connects the original self-expanding GST cosmology
to REAL smooth-projective scheme and native Chow cycle types. Each
birth must be an explicitly Gysin-certified projective bundle or
smooth blowup. The tower has NO fixed number of worlds, ambient
dimension, fiber rank, blowup center, or target codimension.

The roots must be independently cycle-complete source schemes.
Every later world inherits actual Chow representatives constructed
recursively by the typed projective-bundle and blowup Gysin laws.
No final target cycle is a field of the tower constructor.
-/

/-- Worlds built from independently verified cycle-complete smooth
projective roots by actual scheme-typed projective bundle or
smooth blowup operations, each with explicit Hodge/Chow Gysin data. -/

inductive SchemeTypedGSTGeometricTower :
    (V : SmoothProjectiveComplexScheme) →
    HodgeBigradedBettiData V → Prop where
  | seed {V : SmoothProjectiveComplexScheme}
      {H : HodgeBigradedBettiData V}
      (h : BigradedBettiHodgeStatement V H) :
      SchemeTypedGSTGeometricTower V H
  | projectiveBundle
      {B T : SmoothProjectiveComplexScheme}
      {HB : HodgeBigradedBettiData B}
      {HT : HodgeBigradedBettiData T}
      (r : ℕ)
      (hB : SchemeTypedGSTGeometricTower B HB)
      (P : ∀ p : ℕ, SchemeProjectiveBundleGysin B T HB HT r p) :
      SchemeTypedGSTGeometricTower T HT
  | blowup
      {B C T : SmoothProjectiveComplexScheme}
      {HB : HodgeBigradedBettiData B}
      {HC : HodgeBigradedBettiData C}
      {HT : HodgeBigradedBettiData T}
      (c : ℕ)
      (hB : SchemeTypedGSTGeometricTower B HB)
      (hC : SchemeTypedGSTGeometricTower C HC)
      (P : ∀ p : ℕ, SchemeBlowupGysin B C T HB HC HT c p) :
      SchemeTypedGSTGeometricTower T HT

/-- FULL rational Hodge cycle existence on every GST-born actual
smooth projective scheme in an arbitrarily deep tower, proved by
structural induction on the true projective-bundle/blowup birth
certificates. Every source and target is the ORIGINAL scheme type. -/
theorem every_scheme_world_in_GST_tower_has_actual_hodge_cycles
    {V : SmoothProjectiveComplexScheme}
    {H : HodgeBigradedBettiData V}
    (h : SchemeTypedGSTGeometricTower V H) :
    BigradedBettiHodgeStatement V H := by
  induction h with
  | seed hBase =>
      exact hBase
  | projectiveBundle r hB P ihB =>
      intro p
      exact hodge_cycles_on_geometric_projective_bundle (P p) ihB
  | blowup c hB hC P ihB ihC =>
      intro p
      exact hodge_cycles_on_geometric_blowup (P p) ihB ihC


/-! ## All-varieties exceptional center: bidirectional native Hodge transfer

Every smooth projective X admits a closed embedding X -> P^N with
codimension >= 2; blowing up P^N along X gives a RATIONAL smooth
projective Y. The cohomological blowup formula embeds Hdg^p(X)
into the exceptional Hodge summand of Hdg^(p+1)(Y).

This is a NEW formal CENTER-RECOVERY law complementary to the existing
forward SchemeBlowupGysin birth. Native exceptional Gysin maps
transport cycles X -> Y; the Chow excess-intersection/projective-bundle
inverse transports cycles Y -> X. These ACTUAL scheme-typed maps
and their Betti counterparts are independent geometric obligations.

We show exactly (for EVERY class alpha):
  alpha is algebraic on X
    IFF exceptionalGysin(alpha) is algebraic on Y.
Thus a rational ambient blowup cannot *hide* any missing arbitrary-X
primitive Hodge direction. It is a faithful transport/reduction of
the classical conjecture, not an unconditional proof that Y is solved.
The existence of the blowup and these geometric Gysin maps is still
an external scheme-theoretic instantiation; no arbitrary native
Hodge-to-cycle selector is included in this structure.
-/

/-- Scheme-typed native Chow/Betti retract for one exceptional
center summand, in ALL degrees p with shift p -> p+1.
No target native preimage or cycle-class surjectivity is a field. -/
structure SchemeExceptionalCenterRetract
    (C T : SmoothProjectiveComplexScheme)
    (HC : HodgeBigradedBettiData C)
    (HT : HodgeBigradedBettiData T)
    (p : ℕ) where
  exceptionalNative :
    codimensionCycles C.X p →ₗ[ℚ] codimensionCycles T.X (p+1)
  exceptionalBetti :
    RationalSingularCohomology HC.analytification (2*p) →ₗ[ℚ]
      RationalSingularCohomology HT.analytification (2*(p+1))
  centerRecoverNative :
    codimensionCycles T.X (p+1) →ₗ[ℚ] codimensionCycles C.X p
  centerRecoverBetti :
    RationalSingularCohomology HT.analytification (2*(p+1)) →ₗ[ℚ]
      RationalSingularCohomology HC.analytification (2*p)
  exceptionalCycleClass :
    ∀ Z : codimensionCycles C.X p,
      HT.cycleClass (p+1) (exceptionalNative Z) =
        exceptionalBetti (HC.cycleClass p Z)
  recoveryCycleClass :
    ∀ Z : codimensionCycles T.X (p+1),
      HC.cycleClass p (centerRecoverNative Z) =
        centerRecoverBetti (HT.cycleClass (p+1) Z)
  centerLeftInverseBetti :
    ∀ alpha : RationalSingularCohomology HC.analytification (2*p),
      centerRecoverBetti (exceptionalBetti alpha) = alpha
  exceptionalPreservesHodge :
    ∀ alpha : RationalSingularCohomology HC.analytification (2*p),
      alpha ∈ rationalHodgeSubspace (HC.hodgeBigrading p) →
        exceptionalBetti alpha ∈
          rationalHodgeSubspace (HT.hodgeBigrading (p+1))

/-- Exact per-class ALL-VARIETIES algebraicity equivalence, using
REAL rational codimension-cycle carriers of the center and blowup.
Forward: exceptional Gysin of a native cycle.
Backward: recover the native exceptional component of an algebraic
cycle, then invoke the Betti left-inverse identity. -/
theorem algebraic_center_iff_exceptional_blowup_class
    {C T : SmoothProjectiveComplexScheme}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {p : ℕ}
    (R : SchemeExceptionalCenterRetract C T HC HT p)
    (alpha : RationalSingularCohomology HC.analytification (2*p)) :
    alpha ∈ LinearMap.range (HC.cycleClass p) ↔
      R.exceptionalBetti alpha ∈
        LinearMap.range (HT.cycleClass (p+1)) := by
  constructor
  · rintro ⟨Z, hZ⟩
    refine ⟨R.exceptionalNative Z, ?_⟩
    calc
      HT.cycleClass (p+1) (R.exceptionalNative Z) =
          R.exceptionalBetti (HC.cycleClass p Z) :=
            R.exceptionalCycleClass Z
      _ = R.exceptionalBetti alpha := by rw [hZ]
  · rintro ⟨Z, hZ⟩
    refine ⟨R.centerRecoverNative Z, ?_⟩
    calc
      HC.cycleClass p (R.centerRecoverNative Z) =
          R.centerRecoverBetti (HT.cycleClass (p+1) Z) :=
            R.recoveryCycleClass Z
      _ = R.centerRecoverBetti (R.exceptionalBetti alpha) := by
            rw [hZ]
      _ = alpha := R.centerLeftInverseBetti alpha

/-- Missing primitive/Hodge classes in ANY X remain unrepresented
in the exceptional sector of a rational blowup centered at X.
This establishes a precise barrier against confusing geometric
rationality of the born world with Hodge algebraicity. -/
theorem missing_center_direction_survives_exceptional_birth
    {C T : SmoothProjectiveComplexScheme}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {p : ℕ}
    (R : SchemeExceptionalCenterRetract C T HC HT p)
    (alpha : RationalSingularCohomology HC.analytification (2*p))
    (hMissing : alpha ∉ LinearMap.range (HC.cycleClass p)) :
    R.exceptionalBetti alpha ∉
      LinearMap.range (HT.cycleClass (p+1)) := by
  intro h
  exact hMissing
    ((algebraic_center_iff_exceptional_blowup_class R alpha).mpr h)

/-- Global fixed-weight descent for every Hodge direction of an
ARBITRARY smooth projective center from its rational blowup host.
No class of the center is assumed already algebraic. -/
theorem hodge_on_arbitrary_center_of_solved_blowup
    {C T : SmoothProjectiveComplexScheme}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {p : ℕ}
    (R : SchemeExceptionalCenterRetract C T HC HT p)
    (hHost :
      rationalHodgeSubspace (HT.hodgeBigrading (p+1)) ≤
        LinearMap.range (HT.cycleClass (p+1))) :
    rationalHodgeSubspace (HC.hodgeBigrading p) ≤
      LinearMap.range (HC.cycleClass p) := by
  intro alpha hAlpha
  apply (algebraic_center_iff_exceptional_blowup_class R alpha).mpr
  exact hHost (R.exceptionalPreservesHodge alpha hAlpha)


/-! ## Arbitrary-X rational MIDDLE-DIMENSION GST bridge

Given Y=Bl_X(P^N), an arbitrary p-Hodge class on X sits in the
first exceptional degree q=p+1 of Y. If N >= 2q, choose
r=N-2q, and stabilize via M=Y×P^r. Then

     dim M = N+r = 2(q+r),

so the degree 2(q+r) of the stabilized Hodge class is
EXACTLY THE MIDDLE COHOMOLOGICAL DEGREE of M. Moreover,
M is rational because Y is rational.

The cycle constructor Z -> pr_Y^*(Z)*h^r and its true Betti
map are algebraic and admit inverse pushforward along P^r.
Their scheme-level Chow/projective-bundle geometry is an
independent instantiation obligation. The following theorem
proves the exact two-step Chow/BettI recovery law, for every
X,p and every Hodge alpha, not just a chosen source family.

An Hodge theorem for *all middle classes on these rational M*
would imply the general Hodge conjecture. This is an EQUIVALENT
REDUCTION, not a proof that those middle classes are algebraic.
-/

/-- All-dimensional arithmetic: adding a projective-space factor
of dimension r=N-2q moves the qth Hodge class on Y into the
middle Hodge degree of Y×P^r. No bound on N or q. -/
theorem projective_stabilization_hits_middle_degree
    (N q : ℕ) (h : 2*q ≤ N) :
    N + (N-2*q) = 2*(q+(N-2*q)) := by
  omega

/-- Actual native Chow and rational Betti stabilization for
Y -> Y×P^r. Native forward is pullback times top hyperplane
power h^r; native backward is pushforward over P^r. The
cohomological and cycle compatibility equations are explicit,
rather than identifying source and target carriers by hand. -/
structure SchemeProjectiveMiddleStabilization
    (Y M : SmoothProjectiveComplexScheme)
    (HY : HodgeBigradedBettiData Y)
    (HM : HodgeBigradedBettiData M)
    (q r : ℕ) where
  nativeStabilize :
    codimensionCycles Y.X q →ₗ[ℚ]
      codimensionCycles M.X (q+r)
  bettiStabilize :
    RationalSingularCohomology HY.analytification (2*q) →ₗ[ℚ]
      RationalSingularCohomology HM.analytification (2*(q+r))
  nativeRecover :
    codimensionCycles M.X (q+r) →ₗ[ℚ]
      codimensionCycles Y.X q
  bettiRecover :
    RationalSingularCohomology HM.analytification (2*(q+r)) →ₗ[ℚ]
      RationalSingularCohomology HY.analytification (2*q)
  stabilizeNaturality :
    ∀ Z : codimensionCycles Y.X q,
      HM.cycleClass (q+r) (nativeStabilize Z) =
        bettiStabilize (HY.cycleClass q Z)
  recoverNaturality :
    ∀ Z : codimensionCycles M.X (q+r),
      HY.cycleClass q (nativeRecover Z) =
        bettiRecover (HM.cycleClass (q+r) Z)
  bettiLeftInverse :
    ∀ alpha : RationalSingularCohomology HY.analytification (2*q),
      bettiRecover (bettiStabilize alpha) = alpha
  preserveHodge :
    ∀ alpha : RationalSingularCohomology HY.analytification (2*q),
      alpha ∈ rationalHodgeSubspace (HY.hodgeBigrading q) →
      bettiStabilize alpha ∈
        rationalHodgeSubspace (HM.hodgeBigrading (q+r))

/-- Every rational Hodge direction is algebraic on Y EXACTLY
when its actual projectively stabilized class is algebraic on
M=Y×P^r. Both directions construct ACTUAL Chow cycles. -/
theorem algebraic_iff_projectively_stabilized_class
    {Y M : SmoothProjectiveComplexScheme}
    {HY : HodgeBigradedBettiData Y}
    {HM : HodgeBigradedBettiData M}
    {q r : ℕ}
    (S : SchemeProjectiveMiddleStabilization Y M HY HM q r)
    (alpha : RationalSingularCohomology HY.analytification (2*q)) :
    alpha ∈ LinearMap.range (HY.cycleClass q) ↔
      S.bettiStabilize alpha ∈
        LinearMap.range (HM.cycleClass (q+r)) := by
  constructor
  · rintro ⟨Z, hZ⟩
    refine ⟨S.nativeStabilize Z, ?_⟩
    calc
      HM.cycleClass (q+r) (S.nativeStabilize Z) =
          S.bettiStabilize (HY.cycleClass q Z) :=
            S.stabilizeNaturality Z
      _ = S.bettiStabilize alpha := by rw [hZ]
  · rintro ⟨Z, hZ⟩
    refine ⟨S.nativeRecover Z, ?_⟩
    calc
      HY.cycleClass q (S.nativeRecover Z) =
          S.bettiRecover (HM.cycleClass (q+r) Z) :=
            S.recoverNaturality Z
      _ = S.bettiRecover (S.bettiStabilize alpha) := by
            rw [hZ]
      _ = alpha := S.bettiLeftInverse alpha

/-- ALL-VARIETIES TO MIDDLE HODGE reduction in the genuine
codimension-cycle carriers: first embed X as an exceptional center
of Y, then stabilize Y to M. The complete two-step inverse
recovers an actual Chow cycle on X from any algebraic middle
representative on M. The two genuine geometric certificates
are independent of the desired class alpha. -/
theorem algebraic_iff_rational_blowup_middle_class
    {X Y M : SmoothProjectiveComplexScheme}
    {HX : HodgeBigradedBettiData X}
    {HY : HodgeBigradedBettiData Y}
    {HM : HodgeBigradedBettiData M}
    {p r : ℕ}
    (E : SchemeExceptionalCenterRetract X Y HX HY p)
    (S : SchemeProjectiveMiddleStabilization Y M HY HM (p+1) r)
    (alpha : RationalSingularCohomology HX.analytification (2*p)) :
    alpha ∈ LinearMap.range (HX.cycleClass p) ↔
      S.bettiStabilize (E.exceptionalBetti alpha) ∈
        LinearMap.range (HM.cycleClass (p+1+r)) := by
  exact
    (algebraic_center_iff_exceptional_blowup_class E alpha).trans
      (algebraic_iff_projectively_stabilized_class S
        (E.exceptionalBetti alpha))

/-- The genuine all-varieties Hodge target at p is implied by
algebraicity of the corresponding middle degree on rational M,
provided the geometric exceptional/projective stabilization
exists. No native algebraic preimage on X is a premise. -/
theorem arbitrary_variety_hodge_from_rational_middle_world
    {X Y M : SmoothProjectiveComplexScheme}
    {HX : HodgeBigradedBettiData X}
    {HY : HodgeBigradedBettiData Y}
    {HM : HodgeBigradedBettiData M}
    {p r : ℕ}
    (E : SchemeExceptionalCenterRetract X Y HX HY p)
    (S : SchemeProjectiveMiddleStabilization Y M HY HM (p+1) r)
    (hMiddle :
      rationalHodgeSubspace (HM.hodgeBigrading (p+1+r)) ≤
        LinearMap.range (HM.cycleClass (p+1+r))) :
    rationalHodgeSubspace (HX.hodgeBigrading p) ≤
      LinearMap.range (HX.cycleClass p) := by
  intro alpha hAlpha
  apply (algebraic_iff_rational_blowup_middle_class E S alpha).mpr
  exact hMiddle (S.preserveHodge _
    (E.exceptionalPreservesHodge alpha hAlpha))


/-! ## Explicit arbitrary-X native cycle from a rational middle class

This is not merely surjectivity: given a SPECIFIC independently
constructed algebraic middle-degree cycle on the stabilized rational
world M, the following actual Lean term recovers a rational
codimension-p cycle on the ORIGINAL arbitrary X by first integrating
over the projective factor and then extracting the exceptional center
component. The two strict Chow/Betti projection formulas certify
the target class without an arbitrary Hodge-to-Chow selector.
-/

/-- A concrete rational Chow-cycle CONSTRUCTOR on arbitrary X
from a concrete middle rational Chow cycle on the stabilized
rational blowup M, through two existing native geometric maps. -/
noncomputable def nativeCenterFromRationalMiddleCycle
    {X Y M : SmoothProjectiveComplexScheme}
    {HX : HodgeBigradedBettiData X}
    {HY : HodgeBigradedBettiData Y}
    {HM : HodgeBigradedBettiData M}
    {p r : ℕ}
    (E : SchemeExceptionalCenterRetract X Y HX HY p)
    (S : SchemeProjectiveMiddleStabilization Y M HY HM (p+1) r)
    (Z : codimensionCycles M.X (p+1+r)) :
    codimensionCycles X.X p :=
  E.centerRecoverNative (S.nativeRecover Z)

/-- Constructed X-cycle exactly represents the supplied Hodge
class whenever its independently verified stabilized middle
algebraic cycle has the corresponding Betti class. The output
is an ACTUAL native Chow element on X, NOT a cohomology vector. -/
theorem nativeCenterFromRationalMiddleCycle_correct
    {X Y M : SmoothProjectiveComplexScheme}
    {HX : HodgeBigradedBettiData X}
    {HY : HodgeBigradedBettiData Y}
    {HM : HodgeBigradedBettiData M}
    {p r : ℕ}
    (E : SchemeExceptionalCenterRetract X Y HX HY p)
    (S : SchemeProjectiveMiddleStabilization Y M HY HM (p+1) r)
    (alpha : RationalSingularCohomology HX.analytification (2*p))
    (Z : codimensionCycles M.X (p+1+r))
    (hZ : HM.cycleClass (p+1+r) Z =
      S.bettiStabilize (E.exceptionalBetti alpha)) :
    HX.cycleClass p (nativeCenterFromRationalMiddleCycle E S Z) =
      alpha := by
  calc
    HX.cycleClass p
        (nativeCenterFromRationalMiddleCycle E S Z) =
      E.centerRecoverBetti
        (HY.cycleClass (p+1) (S.nativeRecover Z)) :=
        E.recoveryCycleClass (S.nativeRecover Z)
    _ = E.centerRecoverBetti
          (S.bettiRecover (HM.cycleClass (p+1+r) Z)) := by
            rw [S.recoverNaturality Z]
    _ = E.centerRecoverBetti
          (S.bettiRecover
            (S.bettiStabilize (E.exceptionalBetti alpha))) := by
            rw [hZ]
    _ = E.centerRecoverBetti (E.exceptionalBetti alpha) := by
            rw [S.bettiLeftInverse]
    _ = alpha := E.centerLeftInverseBetti alpha

#check nativeCenterFromRationalMiddleCycle
#check nativeCenterFromRationalMiddleCycle_correct
#print axioms nativeCenterFromRationalMiddleCycle_correct

#check SchemeProjectiveMiddleStabilization
#check projective_stabilization_hits_middle_degree
#check algebraic_iff_projectively_stabilized_class
#check algebraic_iff_rational_blowup_middle_class
#check arbitrary_variety_hodge_from_rational_middle_world
#print axioms algebraic_iff_rational_blowup_middle_class
#print axioms arbitrary_variety_hodge_from_rational_middle_world


/-! ## Actual independent algebraic Hodge directions from every center

A rational blowup is more than a recoordination: its exceptional
native Chow Gysin map creates algebraic-cycle directions which
are linearly independent from the old projective ambient sector.
The recovery projection tests independence EXACTLY by killing
the old ambient summand while acting as identity on the
exceptional center summand.

No Hodge conjecture hypothesis on X is used to construct these
NEW algebraic directions: only an actual nonzero native cycle
already available on X (e.g. a projective hyperplane divisor).

The geometric ambient-recovery orthogonality is an independent
part of the blowup Chow/Hodge decomposition, rather than an
assumption that an arbitrary target Hodge class is algebraic.
-/

/-- The genuine exceptional Gysin map has no kernel on its
source rational Hodge cohomology once the actual geometric
center readout/recovery formula is certified. -/
theorem exceptional_hodge_embedding_injective
    {C T : SmoothProjectiveComplexScheme}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {p : ℕ}
    (R : SchemeExceptionalCenterRetract C T HC HT p) :
    Function.Injective R.exceptionalBetti := by
  intro a b hab
  calc
    a = R.centerRecoverBetti (R.exceptionalBetti a) :=
      (R.centerLeftInverseBetti a).symm
    _ = R.centerRecoverBetti (R.exceptionalBetti b) := by rw [hab]
    _ = b := R.centerLeftInverseBetti b

/-- An explicit new ACTUAL native codimension-(p+1) cycle on the
born rational world, provably outside the ENTIRE old ambient
Betti image. This works for any smooth center X of any dimension,
without assuming algebraicity of its unknown primitive classes. -/
theorem exceptional_native_cycle_new_beyond_ambient
    {C T : SmoothProjectiveComplexScheme}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {p : ℕ}
    {A : Type*} [AddCommGroup A] [Module ℚ A]
    (R : SchemeExceptionalCenterRetract C T HC HT p)
    (ambientBetti : A →ₗ[ℚ]
      RationalSingularCohomology HT.analytification (2*(p+1)))
    (ambient_recover_zero : ∀ a : A,
      R.centerRecoverBetti (ambientBetti a) = 0)
    (Z : codimensionCycles C.X p)
    (hNonzero : HC.cycleClass p Z ≠ 0) :
    ∃ W : codimensionCycles T.X (p+1),
      HT.cycleClass (p+1) W =
        R.exceptionalBetti (HC.cycleClass p Z) ∧
      R.exceptionalBetti (HC.cycleClass p Z) ∉
        LinearMap.range ambientBetti := by
  refine ⟨R.exceptionalNative Z, R.exceptionalCycleClass Z, ?_⟩
  rintro ⟨a, ha⟩
  apply hNonzero
  calc
    HC.cycleClass p Z =
        R.centerRecoverBetti (R.exceptionalBetti (HC.cycleClass p Z)) :=
          (R.centerLeftInverseBetti (HC.cycleClass p Z)).symm
    _ = R.centerRecoverBetti (ambientBetti a) := by rw [ha]
    _ = 0 := ambient_recover_zero a

#check exceptional_hodge_embedding_injective
#check exceptional_native_cycle_new_beyond_ambient
#print axioms exceptional_native_cycle_new_beyond_ambient


/-! ## Exact persistence of the FULL arbitrary-X Hodge defect rank

A missing Hodge class on X becomes a missing exceptional class on
the rational blowup. This stronger all-index theorem proves that
EVERY LINEARLY INDEPENDENT FAMILY of missing classes modulo the
actual Chow cycleClass image survives the exceptional blowup
and further middle-degree projective stabilization, with the
SAME rational coefficients.

Thus the GST all-X obstruction is not a one-dimensional accident:
a rational middle blowup host retains the entire independent
defect module of the original arbitrary variety. Mere rationality
and existing low-weight Picard exceptional classes cannot make
those missing high-weight directions algebraic.

There is no assumption that a missing class actually exists; the
result isolates precisely what a truly new geometric birth must
overcome without assuming the Hodge conjecture or its negation.
-/

/-- Strong independence modulo GENUINE native codimension-p Chow
cycle classes. Linear combinations which happen to become actual
algebraic classes must have all coefficients zero. -/
def NativeDefectIndependent
    {X : SmoothProjectiveComplexScheme}
    (H : HodgeBigradedBettiData X)
    (p : ℕ)
    {ι : Type*} [Fintype ι]
    (alpha : ι →
      RationalSingularCohomology H.analytification (2*p)) : Prop :=
  ∀ coeff : ι → ℚ,
    (∑ i : ι, coeff i • alpha i) ∈
      LinearMap.range (H.cycleClass p) →
    ∀ i : ι, coeff i = 0

/-- Every rational linear independent class-family defect on an
arbitrary smooth projective CENTER persists under its true
exceptional Chow/Betti blowup embedding. The map cannot collapse
or algebraize any nontrivial rational combination of missing
directions merely because the host is rational. -/
theorem exceptional_blowup_preserves_native_defect_independence
    {C T : SmoothProjectiveComplexScheme}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {p : ℕ} {ι : Type*} [Fintype ι]
    (E : SchemeExceptionalCenterRetract C T HC HT p)
    (alpha : ι →
      RationalSingularCohomology HC.analytification (2*p))
    (hIndependent : NativeDefectIndependent HC p alpha) :
    NativeDefectIndependent HT (p+1)
      (fun i => E.exceptionalBetti (alpha i)) := by
  classical
  intro coeff hCycle
  apply hIndependent coeff
  apply (algebraic_center_iff_exceptional_blowup_class E
    (∑ i : ι, coeff i • alpha i)).mpr
  simpa only [map_sum, map_smul] using hCycle

/-- Even a middle-degree smooth RATIONAL world formed by projective
stabilization preserves ALL mutually independent arbitrary-X
non-algebraic directions: the obstruction module is transported
faithfully through both genuine Chow/Gysin recovery stages. -/
theorem middle_rational_world_preserves_native_defect_independence
    {C T M : SmoothProjectiveComplexScheme}
    {HC : HodgeBigradedBettiData C}
    {HT : HodgeBigradedBettiData T}
    {HM : HodgeBigradedBettiData M}
    {p r : ℕ} {ι : Type*} [Fintype ι]
    (E : SchemeExceptionalCenterRetract C T HC HT p)
    (S : SchemeProjectiveMiddleStabilization T M HT HM (p+1) r)
    (alpha : ι →
      RationalSingularCohomology HC.analytification (2*p))
    (hIndependent : NativeDefectIndependent HC p alpha) :
    NativeDefectIndependent HM (p+1+r)
      (fun i => S.bettiStabilize (E.exceptionalBetti (alpha i))) := by
  classical
  intro coeff hCycle
  apply hIndependent coeff
  apply (algebraic_iff_rational_blowup_middle_class E S
    (∑ i : ι, coeff i • alpha i)).mpr
  simpa only [map_sum, map_smul] using hCycle

#check NativeDefectIndependent
#check exceptional_blowup_preserves_native_defect_independence
#check middle_rational_world_preserves_native_defect_independence
#print axioms middle_rational_world_preserves_native_defect_independence

#check SchemeExceptionalCenterRetract
#check algebraic_center_iff_exceptional_blowup_class
#check missing_center_direction_survives_exceptional_birth
#check hodge_on_arbitrary_center_of_solved_blowup
#print axioms algebraic_center_iff_exceptional_blowup_class
#print axioms missing_center_direction_survives_exceptional_birth
#print axioms hodge_on_arbitrary_center_of_solved_blowup

#check SchemeTypedGSTGeometricTower
#check every_scheme_world_in_GST_tower_has_actual_hodge_cycles
#print axioms every_scheme_world_in_GST_tower_has_actual_hodge_cycles

#check SchemeBlowupGysin
#check SchemeBlowupGysin.toSplit
#check hodge_cycles_on_geometric_blowup
#print axioms hodge_cycles_on_geometric_blowup

#check SchemeProjectiveBundleGysin
#check hodge_cycles_on_geometric_projective_bundle
#print axioms hodge_cycles_on_geometric_projective_bundle

#check GeometricSplitGysinPacket
#check GeometricSplitGysinPacket.toChowBirth
#check actual_chow_cycle_of_geometric_gysin_split
#check actual_hodge_of_geometric_gysin_split
#print axioms actual_hodge_of_geometric_gysin_split

#check GeometricMultiSourceChowBirth
#check actual_target_cycle_of_geometric_multi_source_birth
#check actual_hodge_range_of_geometric_multi_source_birth
#print axioms actual_target_cycle_of_geometric_multi_source_birth
#print axioms actual_hodge_range_of_geometric_multi_source_birth

#check construct_target_cycle_from_source_hodge_lift
#check every_target_hodge_class_from_solved_source
#check target_hodge_subset_native_cycleClass_range
#check no_unrepresented_target_from_algebraic_source
#print axioms every_target_hodge_class_from_solved_source
#print axioms no_unrepresented_target_from_algebraic_source

end GSTUniversalChowRetractToTarget
