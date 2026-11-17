import Mathlib
import GSTHodgePoincareStrands
import GSTUniversalLefschetzDynamics
import GSTDimensionFreeHodgeDiagonal

/-!
# GST HODGE BIGRADED COSMOLOGY

A rectangular GST cell carries two simultaneous invariants:

    k = C + d       (Lefschetz degree)
    q = C - d       (signed Hodge charge).

Together (k,q) determine the cell uniquely. Hence every rectangular world
admits a multiplicity-free Hodge/Lefschetz bidegree decomposition.

The two native axis transports act by

    digit n : (k,q) |-> (k+n, q-n)
    carry n : (k,q) |-> (k+n, q+n),

while Poincare duality acts by

    (k,q) |-> (A+B-2-k, (A-B)-q).

The historical diagonal Hodge sector is exactly q=0 and k=2p.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTHodgeBigradedCosmology

open GSTWorldCosmology
open GSTGradedWorldAlgebra
open GSTWorldPoincareDuality
open GSTHodgePoincareStrands
open GSTWorldRecoordinationGroupoid
open GSTUniversalLefschetzDynamics
open GSTDimensionFreeHodgeDiagonal

/-- Joint Lefschetz-degree / Hodge-charge label. -/
def worldHodgeBidegree {A B : Nat} (c : WorldCell A B) : Nat × Int :=
  (worldDegree c, worldHodgeCharge c)

/-- **MULTIPLICITY-FREE BIGRADING.** Degree and charge together determine a world cell uniquely. -/
theorem worldHodgeBidegree_injective {A B : Nat} :
    Function.Injective (@worldHodgeBidegree A B) := by
  intro c d h
  rcases c with ⟨⟨C,hC⟩,⟨a,ha⟩⟩
  rcases d with ⟨⟨D,hD⟩,⟨b,hb⟩⟩
  have hk := congrArg Prod.fst h
  have hq := congrArg Prod.snd h
  unfold worldHodgeBidegree worldDegree worldHodgeCharge at hk hq
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

/-- Cells of one exact bidegree. -/
abbrev HodgeBidegreeCell (A B k : Nat) (q : Int) : Type :=
  {c : WorldCell A B // worldHodgeBidegree c = (k,q)}

/-- Every bidegree fiber has at most one cell. -/
theorem hodgeBidegreeCell_subsingleton (A B k : Nat) (q : Int) :
    Subsingleton (HodgeBidegreeCell A B k q) := by
  constructor
  intro x y
  apply Subtype.ext
  apply worldHodgeBidegree_injective
  rw [x.2, y.2]

/-- Project onto one exact (degree,charge) sector. -/
def worldHodgeBidegreeProj {A B : Nat} (k : Nat) (q : Int)
    (f : WorldCoef A B) : WorldCoef A B :=
  worldSectorProj k (worldHodgeStrandProj q f)

/-- Degree and charge projectors commute exactly. -/
theorem degree_charge_projectors_commute {A B : Nat} (k : Nat) (q : Int)
    (f : WorldCoef A B) :
    worldSectorProj k (worldHodgeStrandProj q f) =
      worldHodgeStrandProj q (worldSectorProj k f) := by
  funext c
  by_cases hk : worldDegree c = k <;>
    by_cases hq : worldHodgeCharge c = q <;>
      simp [worldSectorProj, worldHodgeStrandProj, hk, hq]

/-- Exact pointwise criterion for the joint projector. -/
theorem worldHodgeBidegreeProj_apply {A B : Nat} (k : Nat) (q : Int)
    (f : WorldCoef A B) (c : WorldCell A B) :
    worldHodgeBidegreeProj k q f c =
      if worldHodgeBidegree c = (k,q) then f c else 0 := by
  unfold worldHodgeBidegreeProj worldHodgeBidegree
  by_cases hk : worldDegree c = k
  · by_cases hq : worldHodgeCharge c = q
    · simp [worldSectorProj, worldHodgeStrandProj, hk, hq]
    · have hpair : (worldDegree c, worldHodgeCharge c) ≠ (k,q) := by
        intro h
        exact hq (congrArg Prod.snd h)
      simp [worldSectorProj, worldHodgeStrandProj, hk, hq, hpair]
  · have hpair : (worldDegree c, worldHodgeCharge c) ≠ (k,q) := by
      intro h
      exact hk (congrArg Prod.fst h)
    simp [worldSectorProj, worldHodgeStrandProj, hk, hpair]

/-- Joint projectors are idempotent. -/
theorem worldHodgeBidegreeProj_idempotent {A B : Nat} (k : Nat) (q : Int)
    (f : WorldCoef A B) :
    worldHodgeBidegreeProj k q (worldHodgeBidegreeProj k q f) =
      worldHodgeBidegreeProj k q f := by
  funext c
  rw [worldHodgeBidegreeProj_apply, worldHodgeBidegreeProj_apply]
  by_cases h : worldHodgeBidegree c = (k,q) <;> simp [h]

/-- Distinct joint bidegrees are orthogonal. -/
theorem worldHodgeBidegreeProj_orthogonal {A B : Nat}
    (k j : Nat) (q r : Int)
    (hneq : (k,q) ≠ (j,r))
    (f : WorldCoef A B) :
    worldHodgeBidegreeProj k q (worldHodgeBidegreeProj j r f) = fun _ => 0 := by
  funext c
  rw [worldHodgeBidegreeProj_apply, worldHodgeBidegreeProj_apply]
  by_cases h1 : worldHodgeBidegree c = (k,q)
  · rw [if_pos h1]
    by_cases h2 : worldHodgeBidegree c = (j,r)
    · exact absurd (h1.symm.trans h2) hneq
    · rw [if_neg h2]
  · rw [if_neg h1]

/-- Digit-axis transport moves bidegree by (n,-n). -/
theorem digitShiftN_respects_bidegree {A B : Nat} (n k : Nat) (q : Int)
    (f : WorldCoef A B) :
    digitShiftN n (worldHodgeBidegreeProj k q f) =
      worldHodgeBidegreeProj (k+n) (q-(n:Int)) (digitShiftN n f) := by
  unfold worldHodgeBidegreeProj
  rw [degree_charge_projectors_commute]
  rw [digitShiftN_respects_hodgeCharge]
  rw [digitShiftN_respects_degree]
  rw [degree_charge_projectors_commute]

/-- Carry-axis transport moves bidegree by (n,+n). -/
theorem carryShiftN_respects_bidegree {A B : Nat} (n k : Nat) (q : Int)
    (f : WorldCoef A B) :
    carryShiftN n (worldHodgeBidegreeProj k q f) =
      worldHodgeBidegreeProj (k+n) (q+(n:Int)) (carryShiftN n f) := by
  unfold worldHodgeBidegreeProj
  rw [degree_charge_projectors_commute]
  rw [carryShiftN_respects_hodgeCharge]
  rw [carryShiftN_respects_degree]
  rw [degree_charge_projectors_commute]

/-- Poincare complement transforms the complete bidegree exactly. -/
theorem worldHodgeBidegree_dual {A B : Nat} (c : WorldCell A B) :
    worldHodgeBidegree (worldDual c) =
      (A+B-2-worldDegree c, worldChargeCenter A B-worldHodgeCharge c) := by
  apply Prod.ext
  · exact worldDegree_dual c
  · exact worldHodgeCharge_dual c

/-- Poincare gives an equivalence between exact complementary bidegrees. -/
def hodgeBidegreeDualEquiv {A B : Nat} (k : Nat) (q : Int)
    (hk : k ≤ A+B-2) :
    HodgeBidegreeCell A B k q ≃
      HodgeBidegreeCell A B (A+B-2-k) (worldChargeCenter A B-q) where
  toFun c :=
    ⟨worldDual c.1, by
      rw [worldHodgeBidegree_dual]
      have hk' : worldDegree ↑c.1 = k := congrArg Prod.fst c.2
      have hq' : worldHodgeCharge ↑c.1 = q := congrArg Prod.snd c.2
      rw [hk', hq']⟩
  invFun c :=
    ⟨worldDual c.1, by
      rw [worldHodgeBidegree_dual]
      have hk' : worldDegree ↑c.1 = A+B-2-k := congrArg Prod.fst c.2
      have hq' : worldHodgeCharge ↑c.1 = worldChargeCenter A B - q :=
        congrArg Prod.snd c.2
      rw [hk', hq']
      apply Prod.ext
      · omega
      · ring⟩
  left_inv c := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- Diagonal weight p has exact bidegree (2p,0). -/
theorem diagonalState_bidegree {A B p : Nat} (hpA : p < A) (hpB : p < B) :
    worldHodgeBidegree (diagonalState hpA hpB) = (2*p,0) := by
  unfold worldHodgeBidegree worldDegree worldHodgeCharge diagonalState
  simp
  omega

/-- A live weight-p Hodge class is exactly a fixed vector of the single bidegree projector (2p,0). -/
theorem worldHodgeClass_iff_bidegree_fixed {A B p : Nat} (hpA : p < A) (hpB : p < B)
    (f : WorldCoef A B) :
    isWorldHodgeClass p f ↔ worldHodgeBidegreeProj (2*p) 0 f = f := by
  constructor
  · intro hf
    funext c
    by_cases hdiag : c.1.1 = p ∧ c.2.1 = p
    · rcases hdiag with ⟨hC,hd⟩
      have hb : worldHodgeBidegree c = (2*p,0) := by
        unfold worldHodgeBidegree worldDegree worldHodgeCharge
        apply Prod.ext
        · simp only
          omega
        · simp only
          omega
      rw [worldHodgeBidegreeProj_apply]
      simp [hb]
    · have hoff : c.1.1 ≠ p ∨ c.2.1 ≠ p := by tauto
      have hf0 := hf c hoff
      rw [worldHodgeBidegreeProj_apply]
      by_cases hb : worldHodgeBidegree c = (2*p,0)
      · have hq := congrArg Prod.snd hb
        have hk := congrArg Prod.fst hb
        unfold worldHodgeBidegree worldDegree worldHodgeCharge at hk hq
        have : c.1.1 = p ∧ c.2.1 = p := by omega
        exact (hdiag this).elim
      · simp [hb, hf0]
  · intro hfix c hoff
    have hb : worldHodgeBidegree c ≠ (2*p,0) := by
      intro hbc
      have hq := congrArg Prod.snd hbc
      have hk := congrArg Prod.fst hbc
      unfold worldHodgeBidegree worldDegree worldHodgeCharge at hk hq
      rcases hoff with hC | hd
      · exact hC (by omega)
      · exact hd (by omega)
    have hc0 : worldHodgeBidegreeProj (2*p) 0 f c = 0 :=
      (worldHodgeBidegreeProj_apply (2*p) 0 f c).trans (if_neg hb)
    rw [← hfix]
    exact hc0

/-- Capstone: multiplicity-free bidegrees, exact axis motion, Poincare reflection and identification of the Hodge diagonal all coexist. -/
theorem hodge_bigraded_cosmology_crown :
    (∀ A B : Nat, Function.Injective (@worldHodgeBidegree A B))
    ∧ (∀ A B n k (q : Int) (f : WorldCoef A B),
      digitShiftN n (worldHodgeBidegreeProj k q f) =
        worldHodgeBidegreeProj (k+n) (q-(n:Int)) (digitShiftN n f))
    ∧ (∀ A B n k (q : Int) (f : WorldCoef A B),
      carryShiftN n (worldHodgeBidegreeProj k q f) =
        worldHodgeBidegreeProj (k+n) (q+(n:Int)) (carryShiftN n f))
    ∧ (∀ A B (c : WorldCell A B),
      worldHodgeBidegree (worldDual c) =
        (A+B-2-worldDegree c,
          worldChargeCenter A B-worldHodgeCharge c)) := by
  refine ⟨?_, fun A B => digitShiftN_respects_bidegree,
    fun A B => carryShiftN_respects_bidegree,
    fun A B c => worldHodgeBidegree_dual c⟩
  intro A B
  exact worldHodgeBidegree_injective

#check worldHodgeBidegree
#check worldHodgeBidegree_injective
#check hodgeBidegreeCell_subsingleton
#check worldHodgeBidegreeProj
#check digitShiftN_respects_bidegree
#check carryShiftN_respects_bidegree
#check worldHodgeBidegree_dual
#check hodgeBidegreeDualEquiv
#check diagonalState_bidegree
#check worldHodgeClass_iff_bidegree_fixed
#check hodge_bigraded_cosmology_crown

#print axioms worldHodgeBidegree_injective
#print axioms digitShiftN_respects_bidegree
#print axioms worldHodgeBidegree_dual
#print axioms worldHodgeClass_iff_bidegree_fixed
#print axioms hodge_bigraded_cosmology_crown

end GSTHodgeBigradedCosmology
