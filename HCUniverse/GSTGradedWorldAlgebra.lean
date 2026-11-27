import Mathlib
import HCUniverse.GSTWorldCosmology

/-!
# GST GRADED WORLD ALGEBRA

The six Kunneth sectors of the original 4 x 3 chart are one specialization
of a grading carried by every rectangular GST world.

For a cell (C,d), degree is C+d.  The resulting degree projectors are
idempotent, pairwise orthogonal and complete.  Arbitrary digit/carry shifts
raise degree by exactly their shift depth.

The fixed six-degree Kunneth polynomial is likewise one instance of an
arbitrary finite-world spectral projector polynomial.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTGradedWorldAlgebra

open GSTWorldCosmology

/-- Native total degree on an arbitrary rectangular GST world. -/
def worldDegree {A B : Nat} (c : WorldCell A B) : Nat :=
  c.1.1 + c.2.1

/-- Project an amplitude onto one total-degree sector. -/
def worldSectorProj {A B : Nat} (k : Nat)
    (g : WorldCoef A B) : WorldCoef A B :=
  fun c => if worldDegree c = k then g c else 0

/-- Sector projectors are idempotent in every rectangular world. -/
theorem worldSectorProj_idempotent
    {A B : Nat} (k : Nat) (g : WorldCoef A B) :
    worldSectorProj k (worldSectorProj k g) = worldSectorProj k g := by
  funext c
  by_cases h : worldDegree c = k <;>
    simp [worldSectorProj, h]

/-- Distinct sectors are exactly orthogonal. -/
theorem worldSectorProj_orthogonal
    {A B : Nat} (k j : Nat) (hkj : k ≠ j)
    (g : WorldCoef A B) :
    worldSectorProj k (worldSectorProj j g) = fun _ => 0 := by
  funext c
  by_cases hj : worldDegree c = j
  · have hjk : j ≠ k := by
      intro h
      exact hkj h.symm
    simp [worldSectorProj, hj, hjk]
  · simp [worldSectorProj, hj]

/-- Every live cell has degree strictly below A+B. -/
theorem worldDegree_lt
    {A B : Nat} (c : WorldCell A B) :
    worldDegree c < A + B := by
  unfold worldDegree
  omega

/-- **DIMENSION-FREE KUNNETH DECOMPOSITION.**
All degree projectors below A+B sum to the identity. -/
theorem worldSectorProj_sum
    {A B : Nat} (g : WorldCoef A B) :
    (fun c => ∑ k ∈ Finset.range (A+B), worldSectorProj k g c) = g := by
  funext c
  classical
  have hmem : worldDegree c ∈ Finset.range (A+B) :=
    Finset.mem_range.mpr (worldDegree_lt c)
  rw [Finset.sum_eq_single (worldDegree c)]
  · simp [worldSectorProj]
  · intro b hb hne
    have hne' : worldDegree c ≠ b := hne.symm
    simp [worldSectorProj, hne']
  · intro hnot
    exact (hnot hmem).elim

/-- Projection distributes over addition. -/
theorem worldSectorProj_add
    {A B : Nat} (k : Nat) (f g : WorldCoef A B) :
    worldSectorProj k (fun c => f c + g c) =
      (fun c => worldSectorProj k f c + worldSectorProj k g c) := by
  funext c
  by_cases h : worldDegree c = k <;>
    simp [worldSectorProj, h]

/-- Arbitrary digit transport raises total degree by exactly n. -/
theorem digitShiftN_respects_degree
    {A B : Nat} (n k : Nat) (g : WorldCoef A B) :
    digitShiftN n (worldSectorProj k g) =
      worldSectorProj (k+n) (digitShiftN n g) := by
  funext c
  by_cases hn : n ≤ c.2.1
  · have hiff :
        (c.1.1 + (c.2.1 - n) = k) ↔
          (c.1.1 + c.2.1 = k+n) := by
      omega
    simp [digitShiftN, worldSectorProj, worldDegree, hn, hiff]
  · simp [digitShiftN, worldSectorProj, worldDegree, hn]

/-- Arbitrary carry transport raises total degree by exactly n. -/
theorem carryShiftN_respects_degree
    {A B : Nat} (n k : Nat) (g : WorldCoef A B) :
    carryShiftN n (worldSectorProj k g) =
      worldSectorProj (k+n) (carryShiftN n g) := by
  funext c
  by_cases hn : n ≤ c.1.1
  · have hiff :
        ((c.1.1 - n) + c.2.1 = k) ↔
          (c.1.1 + c.2.1 = k+n) := by
      omega
    simp [carryShiftN, worldSectorProj, worldDegree, hn, hiff]
  · simp [carryShiftN, worldSectorProj, worldDegree, hn]

/-- Native degree correspondence on arbitrary worlds. -/
def worldDegreeOp {A B : Nat}
    (g : WorldCoef A B) : WorldCoef A B :=
  fun c => ((worldDegree c : Nat) : Int) * g c

/-- Polynomial functional calculus of the native degree correspondence. -/
def worldPolyOp {A B : Nat}
    (p : Polynomial Int) (g : WorldCoef A B) : WorldCoef A B :=
  fun c => p.eval ((worldDegree c : Nat) : Int) * g c

/-- Universal finite-degree spectral polynomial. -/
noncomputable def worldKunnethPoly
    (bound k : Nat) : Polynomial Int :=
  ((List.range bound).filter (fun j => j ≠ k)).foldr
    (fun (j : Nat) (p : Polynomial Int) =>
      (Polynomial.X - Polynomial.C (j : Int)) * p)
    (1 : Polynomial Int)

private theorem eval_worldKunneth_foldr
    (js : List Nat) (x : Int) :
    ((js.foldr
      (fun (j : Nat) (p : Polynomial Int) =>
        (Polynomial.X - Polynomial.C (j : Int)) * p)
      (1 : Polynomial Int)).eval x)
      =
    js.foldr (fun (j : Nat) (v : Int) => (x - (j : Int)) * v) 1 := by
  induction js with
  | nil => simp
  | cons j js ih =>
      simp only [List.foldr]
      rw [Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, ih]

private theorem worldKunneth_foldr_zero
    (js : List Nat) (x : Nat) (hx : x ∈ js) :
    js.foldr (fun (j : Nat) (v : Int) => ((x : Int) - (j : Int)) * v) 1 = 0 := by
  induction js with
  | nil => exact absurd hx (by simp)
  | cons j js ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst j
        simp
      · simp [ih h]

private theorem worldKunneth_foldr_ne_zero
    (js : List Nat) (k : Nat)
    (hk : ∀ j ∈ js, j ≠ k) :
    js.foldr (fun (j : Nat) (v : Int) => ((k : Int) - (j : Int)) * v) 1 ≠ 0 := by
  induction js with
  | nil => simp
  | cons j js ih =>
      have hjk : j ≠ k := hk j (by simp)
      exact mul_ne_zero (by omega)
        (ih (fun j' hj' => hk j' (by
          exact List.mem_cons_of_mem j hj')))

/-- The universal Kunneth polynomial vanishes on every other degree below
the chosen finite bound. -/
theorem worldKunnethPoly_eval_zero
    (bound k x : Nat) (hx : x < bound) (hxk : x ≠ k) :
    (worldKunnethPoly bound k).eval (x : Int) = 0 := by
  unfold worldKunnethPoly
  rw [eval_worldKunneth_foldr]
  exact worldKunneth_foldr_zero
    ((List.range bound).filter (fun j => j ≠ k)) x
    (List.mem_filter.mpr
      ⟨List.mem_range.mpr hx, decide_eq_true hxk⟩)

/-- At its own degree the universal spectral polynomial is nonzero. -/
theorem worldKunnethPoly_eval_self_ne_zero
    (bound k : Nat) (hk : k < bound) :
    (worldKunnethPoly bound k).eval (k : Int) ≠ 0 := by
  unfold worldKunnethPoly
  rw [eval_worldKunneth_foldr]
  exact worldKunneth_foldr_ne_zero
    ((List.range bound).filter (fun j => j ≠ k)) k
    (fun j hj => of_decide_eq_true (List.mem_filter.mp hj).2)

/-- **DIMENSION-FREE KUNNETH POLYNOMIAL THEOREM.**

Every degree-k projector in every A x B GST world is an explicit integer
polynomial in the degree correspondence, up to a nonzero integer scalar. -/
theorem worldKunneth_projector_polynomial
    {A B : Nat} (k : Nat) (hk : k < A+B) :
    ∃ (p : Polynomial Int) (c : Int), c ≠ 0 ∧
      ∀ (g : WorldCoef A B) (x : WorldCell A B),
        worldPolyOp p g x = c * worldSectorProj k g x := by
  refine ⟨worldKunnethPoly (A+B) k,
    (worldKunnethPoly (A+B) k).eval (k : Int),
    worldKunnethPoly_eval_self_ne_zero (A+B) k hk, ?_⟩
  intro g x
  unfold worldPolyOp worldSectorProj
  by_cases hdeg : worldDegree x = k
  · simp [hdeg]
  · have hlt : worldDegree x < A+B := worldDegree_lt x
    have hz :=
      worldKunnethPoly_eval_zero (A+B) k (worldDegree x) hlt hdeg
    simp [hdeg, hz]

/-- One capstone for the dimension-free graded world algebra. -/
theorem graded_world_crown :
    (∀ A B k (g : WorldCoef A B),
      worldSectorProj k (worldSectorProj k g) = worldSectorProj k g)
    ∧ (∀ A B k j, k ≠ j → ∀ (g : WorldCoef A B),
      worldSectorProj k (worldSectorProj j g) = fun _ => 0)
    ∧ (∀ A B (g : WorldCoef A B),
      (fun c => ∑ k ∈ Finset.range (A+B), worldSectorProj k g c) = g)
    ∧ (∀ A B n k (g : WorldCoef A B),
      digitShiftN n (worldSectorProj k g) =
        worldSectorProj (k+n) (digitShiftN n g))
    ∧ (∀ A B n k (g : WorldCoef A B),
      carryShiftN n (worldSectorProj k g) =
        worldSectorProj (k+n) (carryShiftN n g)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A B k g
    exact worldSectorProj_idempotent k g
  · intro A B k j hkj g
    exact worldSectorProj_orthogonal k j hkj g
  · intro A B g
    exact worldSectorProj_sum g
  · intro A B n k g
    exact digitShiftN_respects_degree n k g
  · intro A B n k g
    exact carryShiftN_respects_degree n k g

#check worldSectorProj_idempotent
#check worldSectorProj_orthogonal
#check worldSectorProj_sum
#check digitShiftN_respects_degree
#check carryShiftN_respects_degree
#check worldKunneth_projector_polynomial
#check graded_world_crown

#print axioms worldSectorProj_sum
#print axioms digitShiftN_respects_degree
#print axioms carryShiftN_respects_degree
#print axioms worldKunneth_projector_polynomial
#print axioms graded_world_crown


/-! ## Unbounded grading, independent of a window -/
def cosmicDegree (c : CosmicCell) : ℕ := c.1+c.2

def cosmicCharge (c : CosmicCell) : ℤ := (c.1 : ℤ)-c.2

/-- Degree and signed charge jointly determine the two native coordinates. -/
theorem cosmic_degree_charge_injective :
    Function.Injective (fun c : CosmicCell => (cosmicDegree c, cosmicCharge c)) := by
  intro c d h
  have ht := congrArg Prod.fst h
  have hc := congrArg Prod.snd h
  simp only [cosmicDegree, cosmicCharge] at ht hc
  apply Prod.ext <;> omega

def cosmicSector (k : ℕ) (f : CompletedCosmos) : CompletedCosmos :=
  fun c => if cosmicDegree c=k then f c else 0

@[simp] theorem observe_cosmicSector (A B k : ℕ) (f : CompletedCosmos) :
    observe A B (cosmicSector k f) = worldSectorProj k (observe A B f) := rfl

theorem cosmicSector_idempotent (k : ℕ) (f : CompletedCosmos) :
    cosmicSector k (cosmicSector k f) = cosmicSector k f := by
  funext c
  change (if cosmicDegree c = k then
      (if cosmicDegree c = k then f c else 0) else 0) =
    (if cosmicDegree c = k then f c else 0)
  by_cases hk : cosmicDegree c = k
  · simp only [if_pos hk]
  · simp only [if_neg hk]

theorem cosmicSector_orthogonal (k j : ℕ) (h : k ≠ j) (f : CompletedCosmos) :
    cosmicSector k (cosmicSector j f) = 0 := by
  funext c
  change (if cosmicDegree c = k then
      (if cosmicDegree c = j then f c else 0) else 0) = 0
  by_cases hk : cosmicDegree c = k
  · have hj : cosmicDegree c ≠ j := by
      intro hcj
      apply h
      exact hk.symm.trans hcj
    simp only [if_pos hk, if_neg hj]
  · simp only [if_neg hk]

theorem cosmic_digit_grading (n k : ℕ) (f : CompletedCosmos) :
    cosmicDigitShift n (cosmicSector k f) =
      cosmicSector (k+n) (cosmicDigitShift n f) := by
  apply observations_separate
  intro A B
  simpa using digitShiftN_respects_degree (A:=A) (B:=B) n k (observe A B f)

theorem cosmic_carry_grading (n k : ℕ) (f : CompletedCosmos) :
    cosmicCarryShift n (cosmicSector k f) =
      cosmicSector (k+n) (cosmicCarryShift n f) := by
  apply observations_separate
  intro A B
  simpa using carryShiftN_respects_degree (A:=A) (B:=B) n k (observe A B f)

end GSTGradedWorldAlgebra
