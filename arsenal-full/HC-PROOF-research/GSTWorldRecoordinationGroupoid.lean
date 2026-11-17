import Mathlib
import GSTRadixWorldDynamics
import GSTGradedWorldAlgebra

/-!
# GST WORLD RECOORDINATION GROUPOID

The mixed-radix upgrade still keeps one rectangular world shape fixed.
This layer removes that restriction.

A GST world shape of total cardinality N is any rectangle A x B with
A * B = N.  Every such shape has a canonical code equivalence with Fin N.
Therefore every pair of equal-cardinality world shapes is canonically
recoordinated through Fin N.

The resulting transport has:
* exact code conservation;
* unique targets;
* identity, inverse and composition laws;
* functorial transport of coefficient fields;
* functorial transport of every code spectral sector;
* functorial polynomial functional calculus;
* the previous mixed-radix transpose as one swapped-chart specialization.

Thus rectangular world shape is coordinate data, not a mathematical
invariant of the underlying finite GST state universe.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTWorldRecoordinationGroupoid

open GSTRadixWorldDynamics
open GSTGradedWorldAlgebra

/-- A rectangular presentation of one N-state GST universe. -/
structure GSTWorldShape (N : Nat) where
  rows : Nat
  cols : Nat
  area_eq : rows * cols = N

/-- State type carried by one world shape. -/
abbrev ShapeState {N : Nat} (S : GSTWorldShape N) : Type :=
  Fin S.rows × Fin S.cols

/-- Canonical row-major coding of a shaped world into the underlying N states. -/
def shapeCodeEquiv {N : Nat} (S : GSTWorldShape N) :
    ShapeState S ≃ Fin N :=
  (finProdFinEquiv : Fin S.rows × Fin S.cols ≃ Fin (S.rows * S.cols)).trans
    (finCongr S.area_eq)

/-- Integer code of one state, independent of later recoordination. -/
def worldCode {N : Nat} (S : GSTWorldShape N) (x : ShapeState S) : Nat :=
  (shapeCodeEquiv S x).1

@[simp]
theorem worldCode_expanded
    {N : Nat} (S : GSTWorldShape N) (x : ShapeState S) :
    worldCode S x = x.2.1 + S.cols * x.1.1 := by
  rfl

theorem worldCode_lt
    {N : Nat} (S : GSTWorldShape N) (x : ShapeState S) :
    worldCode S x < N :=
  (shapeCodeEquiv S x).2

/-- Canonical recoordination between any two equal-cardinality GST worlds. -/
def worldRecoordinate
    {N : Nat} (S T : GSTWorldShape N) :
    ShapeState S ≃ ShapeState T :=
  (shapeCodeEquiv S).trans (shapeCodeEquiv T).symm

/-- Recoordination preserves the underlying state code exactly. -/
theorem worldRecoordinate_code
    {N : Nat} (S T : GSTWorldShape N) (x : ShapeState S) :
    worldCode T (worldRecoordinate S T x) = worldCode S x := by
  unfold worldCode worldRecoordinate
  simp

/-- A target with the same code is uniquely the canonical recoordination. -/
theorem worldRecoordinate_unique
    {N : Nat} (S T : GSTWorldShape N)
    (x : ShapeState S) (y : ShapeState T)
    (h : worldCode T y = worldCode S x) :
    worldRecoordinate S T x = y := by
  apply (shapeCodeEquiv T).injective
  apply Fin.ext
  change worldCode T (worldRecoordinate S T x) = worldCode T y
  exact (worldRecoordinate_code S T x).trans h.symm

/-- Every source state has a unique equal-code target in every other shape. -/
theorem existsUnique_worldRecoordinate
    {N : Nat} (S T : GSTWorldShape N) (x : ShapeState S) :
    ∃! y : ShapeState T, worldCode T y = worldCode S x := by
  refine ⟨worldRecoordinate S T x, worldRecoordinate_code S T x, ?_⟩
  intro y hy
  exact (worldRecoordinate_unique S T x y hy).symm

/-- Recoordination by the same chart is identity. -/
theorem worldRecoordinate_self
    {N : Nat} (S : GSTWorldShape N) (x : ShapeState S) :
    worldRecoordinate S S x = x := by
  apply (shapeCodeEquiv S).injective
  simp [worldRecoordinate]

/-- Recoordination is exactly reversible by reversing the chart pair. -/
theorem worldRecoordinate_inverse
    {N : Nat} (S T : GSTWorldShape N) (y : ShapeState T) :
    (worldRecoordinate S T).symm y = worldRecoordinate T S y := by
  apply (shapeCodeEquiv S).injective
  simp [worldRecoordinate]

/-- **WORLD GROUPOID COMPOSITION.**
Passing through an intermediate rectangular chart is exactly direct
recoordination. -/
theorem worldRecoordinate_comp
    {N : Nat} (S T U : GSTWorldShape N) (x : ShapeState S) :
    worldRecoordinate T U (worldRecoordinate S T x) =
      worldRecoordinate S U x := by
  apply (shapeCodeEquiv U).injective
  simp [worldRecoordinate]

/-- Coefficient field living on one shaped finite world. -/
abbrev ShapeCoef {N : Nat} (S : GSTWorldShape N) : Type :=
  ShapeState S → ℤ

/-- Push a coefficient field through a world recoordination. -/
def transportCoef
    {N : Nat} (S T : GSTWorldShape N)
    (f : ShapeCoef S) : ShapeCoef T :=
  fun y => f ((worldRecoordinate S T).symm y)

theorem transportCoef_self
    {N : Nat} (S : GSTWorldShape N) (f : ShapeCoef S) :
    transportCoef S S f = f := by
  funext x
  simp [transportCoef, worldRecoordinate]

/-- **FUNCTORIAL COEFFICIENT TRANSPORT.** -/
theorem transportCoef_comp
    {N : Nat} (S T U : GSTWorldShape N)
    (f : ShapeCoef S) :
    transportCoef T U (transportCoef S T f) =
      transportCoef S U f := by
  funext z
  simp [transportCoef, worldRecoordinate]

/-- Spectral projector onto one invariant state code. -/
def codeSectorProj
    {N : Nat} (S : GSTWorldShape N) (k : Nat)
    (f : ShapeCoef S) : ShapeCoef S :=
  fun x => if worldCode S x = k then f x else 0

theorem codeSectorProj_idempotent
    {N : Nat} (S : GSTWorldShape N) (k : Nat)
    (f : ShapeCoef S) :
    codeSectorProj S k (codeSectorProj S k f) =
      codeSectorProj S k f := by
  funext x
  change
    (if worldCode S x = k then
      (if worldCode S x = k then f x else 0)
    else 0)
      =
    (if worldCode S x = k then f x else 0)
  by_cases h : worldCode S x = k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem codeSectorProj_orthogonal
    {N : Nat} (S : GSTWorldShape N)
    (j k : Nat) (hjk : j ≠ k) (f : ShapeCoef S) :
    codeSectorProj S j (codeSectorProj S k f) = fun _ => 0 := by
  funext x
  change
    (if worldCode S x = j then
      (if worldCode S x = k then f x else 0)
    else 0) = 0
  by_cases hj : worldCode S x = j
  · have hk : worldCode S x ≠ k := by
      intro hk
      apply hjk
      exact hj.symm.trans hk
    rw [if_pos hj, if_neg hk]
  · rw [if_neg hj]

/-- All N code sectors sum exactly to the coefficient field. -/
theorem codeSectorProj_sum
    {N : Nat} (S : GSTWorldShape N) (f : ShapeCoef S) :
    (fun x => ∑ k ∈ Finset.range N, codeSectorProj S k f x) = f := by
  funext x
  classical
  have hmem : worldCode S x ∈ Finset.range N :=
    Finset.mem_range.mpr (worldCode_lt S x)
  rw [Finset.sum_eq_single (worldCode S x)]
  · change (if worldCode S x = worldCode S x then f x else 0) = f x
    rw [if_pos rfl]
  · intro b hb hne
    change (if worldCode S x = b then f x else 0) = 0
    have hne' : worldCode S x ≠ b := hne.symm
    rw [if_neg hne']
  · intro hnot
    exact (hnot hmem).elim

/-- **SPECTRAL NATURALITY.**
World recoordination commutes with every exact code projector. -/
theorem transportCoef_codeSectorProj
    {N : Nat} (S T : GSTWorldShape N)
    (k : Nat) (f : ShapeCoef S) :
    transportCoef S T (codeSectorProj S k f) =
      codeSectorProj T k (transportCoef S T f) := by
  funext y
  have hcode :
      worldCode S ((worldRecoordinate S T).symm y) =
        worldCode T y := by
    rw [worldRecoordinate_inverse S T y]
    exact worldRecoordinate_code T S y
  unfold transportCoef
  change
    (if worldCode S ((worldRecoordinate S T).symm y) = k then
      f ((worldRecoordinate S T).symm y) else 0)
      =
    (if worldCode T y = k then
      f ((worldRecoordinate S T).symm y) else 0)
  rw [hcode]

/-!
## Spectral reconstruction rigidity of the world recoordination groupoid

The old laws proved naturality of coordinate codes and spectral projections.
A stronger question is whether a second rational/integral linear transport
could satisfy the very same laws but move coefficients differently.

It cannot: each code sector is a rank-one free integer line, selected by
an exact idempotent projector. A linear transport intertwining all code
sectors and preserving the canonical constant-one field is forced to be
the unique canonical chart recoordination. This establishes rigidity of
the entire native observable action, not only naturality of its generators.
-/

/-- A single code projector has exactly one source coordinate. Its value
on any field is that coordinate's amplitude times the same projector
applied to the all-one field. -/
theorem codeSectorProj_rankOne
    {N : Nat} (S : GSTWorldShape N)
    (k : Nat) (f : ShapeCoef S)
    (x : ShapeState S) (hx : worldCode S x = k) :
    codeSectorProj S k f =
      f x • codeSectorProj S k (fun _ => (1 : ℤ)) := by
  funext z
  change
    (if worldCode S z = k then f z else (0 : ℤ)) =
      f x * (if worldCode S z = k then (1 : ℤ) else 0)
  by_cases hz : worldCode S z = k
  · have hzx : z = x := by
      apply (shapeCodeEquiv S).injective
      apply Fin.ext
      exact hz.trans hx.symm
    subst z
    rw [if_pos hx, if_pos hx, mul_one]
  · rw [if_neg hz, if_neg hz, mul_zero]

/-- **COMPLETE CLASSIFICATION OF CODE-SPECTRAL INTERTWINERS.**
No normalization is assumed: any integer-linear map intertwining the
rank-one code projectors is *pointwise multiplication* of canonical chart
transport by the image of the constant-one field.  In particular such maps
cannot mix invariant codes or generate a new off-code coefficient. -/
theorem transportCoef_classification_of_spectral_intertwining
    {N : Nat} (S T : GSTWorldShape N)
    (M : ShapeCoef S →ₗ[ℤ] ShapeCoef T)
    (hproject : ∀ k f,
      M (codeSectorProj S k f) = codeSectorProj T k (M f))
    (f : ShapeCoef S) :
    M f = fun y =>
      transportCoef S T f y * (M (fun _ => (1 : ℤ))) y := by
  funext y
  let x : ShapeState S := (worldRecoordinate S T).symm y
  let k : Nat := worldCode T y
  have hkS : worldCode S x = k := by
    dsimp [x, k]
    rw [worldRecoordinate_inverse S T y]
    exact worldRecoordinate_code T S y
  have hkT : worldCode T y = k := rfl
  have hlocal := codeSectorProj_rankOne S k f x hkS
  have hscaled :
      M (codeSectorProj S k f) =
        f x • M (codeSectorProj S k (fun _ => (1 : ℤ))) := by
    rw [hlocal, map_smul]
  change (M f) y = f x * (M (fun _ => (1 : ℤ))) y
  calc
    (M f) y = (codeSectorProj T k (M f)) y := by
      change (M f) y =
        (if worldCode T y = k then (M f) y else (0 : ℤ))
      rw [if_pos hkT]
    _ = (M (codeSectorProj S k f)) y := by
      exact congrFun (hproject k f).symm y
    _ = f x * (M (codeSectorProj S k (fun _ => (1 : ℤ)))) y := by
      rw [hscaled]
      rfl
    _ = f x * (codeSectorProj T k (M (fun _ => (1 : ℤ)))) y := by
      rw [hproject k (fun _ => (1 : ℤ))]
    _ = f x * (M (fun _ => (1 : ℤ))) y := by
      change
        f x * (if worldCode T y = k then
          (M (fun _ => (1 : ℤ))) y else (0 : ℤ)) =
          f x * (M (fun _ => (1 : ℤ))) y
      rw [if_pos hkT]

/-- **NORMALIZED SPECTRAL RIGIDITY**, now derived from the complete
unnormalized intertwiner classification rather than separately assumed
coordinatewise uniqueness. -/
theorem transportCoef_unique_of_spectral_intertwining
    {N : Nat} (S T : GSTWorldShape N)
    (M : ShapeCoef S →ₗ[ℤ] ShapeCoef T)
    (hproject : ∀ k f,
      M (codeSectorProj S k f) = codeSectorProj T k (M f))
    (hone : M (fun _ => (1 : ℤ)) = (fun _ => (1 : ℤ)))
    (f : ShapeCoef S) :
    M f = transportCoef S T f := by
  simpa only [hone, mul_one] using
    (transportCoef_classification_of_spectral_intertwining
      S T M hproject f)

/-- Code-preserving state equivalences are themselves unique. There are
no hidden chart twists invisible to every native state address. -/
theorem worldRecoordinate_is_unique_codePreserving
    {N : Nat} (S T : GSTWorldShape N)
    (e : ShapeState S ≃ ShapeState T) :
    (∀ x, worldCode T (e x) = worldCode S x) ↔
      e = worldRecoordinate S T := by
  constructor
  · intro h
    apply Equiv.ext
    intro x
    exact (worldRecoordinate_unique S T x (e x) (h x)).symm
  · intro he x
    rw [he]
    exact worldRecoordinate_code S T x

/-- The full spectral rigidity crown identifies all available coordinates:
there is a unique code-preserving state map, and every normalized
code-projector-intertwining linear map is canonical coefficient transport. -/
theorem worldRecoordination_full_spectral_rigidity
    {N : Nat} (S T : GSTWorldShape N) :
    (∀ e : ShapeState S ≃ ShapeState T,
      (∀ x, worldCode T (e x) = worldCode S x) →
      e = worldRecoordinate S T)
    ∧ (∀ M : ShapeCoef S →ₗ[ℤ] ShapeCoef T,
      (∀ k f, M (codeSectorProj S k f) =
        codeSectorProj T k (M f)) →
      M (fun _ => (1 : ℤ)) = (fun _ => (1 : ℤ)) →
      ∀ f, M f = transportCoef S T f) := by
  constructor
  · intro e h
    exact (worldRecoordinate_is_unique_codePreserving S T e).mp h
  · intro M hproject hone f
    exact transportCoef_unique_of_spectral_intertwining S T M
      hproject hone f

/-- Polynomial functional calculus of the invariant code observable. -/
def codePolyOp
    {N : Nat} (S : GSTWorldShape N)
    (p : Polynomial ℤ) (f : ShapeCoef S) : ShapeCoef S :=
  fun x => p.eval (worldCode S x : ℤ) * f x

/-- Polynomial observables are exactly natural under world recoordination. -/
theorem transportCoef_codePolyOp
    {N : Nat} (S T : GSTWorldShape N)
    (p : Polynomial ℤ) (f : ShapeCoef S) :
    transportCoef S T (codePolyOp S p f) =
      codePolyOp T p (transportCoef S T f) := by
  funext y
  have hcode :
      worldCode S ((worldRecoordinate S T).symm y) =
        worldCode T y := by
    rw [worldRecoordinate_inverse S T y]
    exact worldRecoordinate_code T S y
  unfold transportCoef codePolyOp
  rw [hcode]

/-- Every code projector is an explicit integer spectral polynomial,
up to a nonzero integer scalar, on every shaped N-state world. -/
theorem codeSector_projector_polynomial
    {N : Nat} (S : GSTWorldShape N)
    (k : Nat) (hk : k < N) :
    ∃ (p : Polynomial ℤ) (c : ℤ), c ≠ 0 ∧
      ∀ (f : ShapeCoef S) (x : ShapeState S),
        codePolyOp S p f x = c * codeSectorProj S k f x := by
  refine ⟨worldKunnethPoly N k,
    (worldKunnethPoly N k).eval (k : ℤ),
    worldKunnethPoly_eval_self_ne_zero N k hk, ?_⟩
  intro f x
  change
    (worldKunnethPoly N k).eval (worldCode S x : ℤ) * f x =
      (worldKunnethPoly N k).eval (k : ℤ) *
        (if worldCode S x = k then f x else 0)
  by_cases h : worldCode S x = k
  · rw [if_pos h, h]
  · have hlt := worldCode_lt S x
    have hz :=
      worldKunnethPoly_eval_zero N k (worldCode S x) hlt h
    rw [if_neg h, hz, zero_mul, mul_zero]

/-- Standard output-oriented rectangular shape. -/
def outputShape (s b : Nat) : GSTWorldShape (s*b) where
  rows := s
  cols := b
  area_eq := rfl

/-- Input-oriented shape of the same s*b state universe. -/
def inputShape (s b : Nat) : GSTWorldShape (s*b) where
  rows := b
  cols := s
  area_eq := Nat.mul_comm b s

/-- Swap the old mixed-radix input coordinates into the input-shaped world. -/
def inputShapeState
    {s b : Nat} (x : RadixState s b) :
    ShapeState (inputShape s b) :=
  (x.2, x.1)

/-- **ABSORPTION OF MIXED-RADIX TRANSPOSE.**
The earlier transpose is exactly: swap into the input chart, then apply the
canonical equal-cardinality world recoordination. -/
theorem mixedRadixTranspose_is_worldRecoordinate
    {s b : Nat} (x : RadixState s b) :
    mixedRadixTranspose s b x =
      worldRecoordinate (inputShape s b) (outputShape s b)
        (inputShapeState x) := by
  apply mixedRadixTranspose_unique
  have h :=
    worldRecoordinate_code
      (inputShape s b) (outputShape s b)
      (inputShapeState x)
  simpa [worldCode_expanded, inputShape, outputShape,
    inputShapeState, inputCode, outputCode] using h

/-- Capstone: equal-cardinality world shapes form an exact finite
recoordination groupoid, and all code-spectral mathematics is natural
under that groupoid. -/
theorem world_recoordination_groupoid_crown :
    (∀ N (S T : GSTWorldShape N) (x : ShapeState S),
      worldCode T (worldRecoordinate S T x) = worldCode S x)
    ∧ (∀ N (S T U : GSTWorldShape N) (x : ShapeState S),
      worldRecoordinate T U (worldRecoordinate S T x) =
        worldRecoordinate S U x)
    ∧ (∀ N (S T : GSTWorldShape N) (f : ShapeCoef S) k,
      transportCoef S T (codeSectorProj S k f) =
        codeSectorProj T k (transportCoef S T f))
    ∧ (∀ N (S T : GSTWorldShape N)
        (p : Polynomial ℤ) (f : ShapeCoef S),
      transportCoef S T (codePolyOp S p f) =
        codePolyOp T p (transportCoef S T f)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N S T x
    exact worldRecoordinate_code S T x
  · intro N S T U x
    exact worldRecoordinate_comp S T U x
  · intro N S T f k
    exact transportCoef_codeSectorProj S T k f
  · intro N S T p f
    exact transportCoef_codePolyOp S T p f

#check GSTWorldShape
#check worldRecoordinate
#check worldRecoordinate_code
#check worldRecoordinate_unique
#check existsUnique_worldRecoordinate
#check worldRecoordinate_comp
#check transportCoef_comp
#check codeSectorProj_sum
#check transportCoef_codeSectorProj
#check transportCoef_codePolyOp
#check codeSector_projector_polynomial
#check mixedRadixTranspose_is_worldRecoordinate
#check codeSectorProj_rankOne
#check transportCoef_classification_of_spectral_intertwining
#check transportCoef_unique_of_spectral_intertwining
#check worldRecoordinate_is_unique_codePreserving
#check worldRecoordination_full_spectral_rigidity
#check world_recoordination_groupoid_crown

#print axioms worldRecoordinate_code
#print axioms worldRecoordinate_unique
#print axioms worldRecoordinate_comp
#print axioms transportCoef_comp
#print axioms transportCoef_codeSectorProj
#print axioms codeSector_projector_polynomial
#print axioms mixedRadixTranspose_is_worldRecoordinate
#print axioms transportCoef_classification_of_spectral_intertwining
#print axioms world_recoordination_groupoid_crown


/-! ## Global chart calculus: reindexing without a finite shape ceiling -/
open GSTWorldCosmology

def cosmicRechart (e : CosmicCell ≃ CosmicCell) :
    CompletedCosmos ≃ₗ[ℤ] CompletedCosmos where
  toFun := fun f c => f (e.symm c)
  invFun := fun f c => f (e c)
  left_inv := by intro f; funext c; simp
  right_inv := by intro f; funext c; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem cosmicRechart_trans (e d : CosmicCell ≃ CosmicCell)
    (f : CompletedCosmos) :
    cosmicRechart d (cosmicRechart e f) = cosmicRechart (e.trans d) f := rfl

/-- Any global chart change is faithfully detected by all finite windows. -/
theorem cosmicRechart_observation_ext (e : CosmicCell ≃ CosmicCell)
    {f g : CompletedCosmos}
    (h : ∀ A B, observe A B (cosmicRechart e f) =
      observe A B (cosmicRechart e g)) : f = g :=
  (cosmicRechart e).injective (observations_separate h)

/-- Finite support is transported by an actual coordinate equivalence. -/
noncomputable def compactRechart (e : CosmicCell ≃ CosmicCell) :
    CompactCosmos ≃+ CompactCosmos := Finsupp.domCongr e

end GSTWorldRecoordinationGroupoid
