import Mathlib
import GSTUniversalLefschetzPathFormula

/-!
# GST UNIVERSAL LEFSCHETZ TRANSITION KERNEL

The universal path formula expands every Lefschetz power into all mixed
digit/carry paths.  This file closes the next layer: it evaluates that whole
path sum on the canonical world basis.

For arbitrary rectangular worlds, arbitrary source and target cells, and
arbitrary time n, a matrix coefficient of L^n is completely determined by
three pieces of native GST data:

* the target must lie in the source's forward digit/carry cone;
* n must equal the exact Manhattan depth between source and target;
* when both conditions hold, the coefficient is the corresponding binomial
  path multiplicity.

Thus every Lefschetz power has a closed transition kernel in every finite GST
world.  No fixed Fin 12 carrier, fixed exponent, or hand-written matrix occurs.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTUniversalLefschetzKernel

open GSTWorldCosmology
open GSTWorldPoincareDuality
open GSTTruncatedWorldCohomologyRing
open GSTUniversalLefschetzPathFormula

/-- A target is causally forward of a source when neither native axis
moves backwards. -/
def worldForward
    {A B : Nat} (s t : WorldCell A B) : Prop :=
  s.1.1 ≤ t.1.1 ∧ s.2.1 ≤ t.2.1

/-- Native carry-axis distance from source to target. -/
def carryDistance
    {A B : Nat} (s t : WorldCell A B) : Nat :=
  t.1.1 - s.1.1

/-- Native digit-axis distance from source to target. -/
def digitDistance
    {A B : Nat} (s t : WorldCell A B) : Nat :=
  t.2.1 - s.2.1

/-- Total causal depth between two world cells. -/
def worldCausalDistance
    {A B : Nat} (s t : WorldCell A B) : Nat :=
  carryDistance s t + digitDistance s t

/-- Forwardness of world cells is decidable: it is a conjunction of
natural order comparisons. -/
instance worldForward_decidable {A B : Nat} (s t : WorldCell A B) :
    Decidable (worldForward s t) := by
  unfold worldForward
  infer_instance

/-- **UNIVERSAL LEFSCHETZ TRANSITION KERNEL.**

Every matrix coefficient of every power of the universal Lefschetz class is
closed form.  A coefficient is zero outside the forward cone or at the wrong
time.  At the unique causal time it is the exact binomial number of mixed
digit/carry paths. -/
theorem worldAct_L_pow_basis_kernel
    (A B n : Nat) (s t : WorldCell A B) :
    worldAct A B ((L A B)^n) (worldBasis s) t =
      if hfuture : worldForward s t then
        if htime : n = worldCausalDistance s t then
          (n.choose (digitDistance s t) : ℤ)
        else 0
      else 0 := by
  rcases s with ⟨⟨Cs,hCs⟩,⟨ds,hds⟩⟩
  rcases t with ⟨⟨Ct,hCt⟩,⟨dt,hdt⟩⟩
  unfold worldForward worldCausalDistance carryDistance digitDistance
  dsimp only
  rw [worldAct_L_pow_coordinate_formula]
  by_cases hfuture : Cs ≤ Ct ∧ ds ≤ dt
  · rw [show dite (Cs ≤ Ct ∧ ds ≤ dt)
        (fun hfuture => if htime : n = Ct - Cs + (dt - ds) then (n.choose (dt - ds) : ℤ) else 0)
        (fun _ => 0) = (if htime : n = Ct - Cs + (dt - ds) then (n.choose (dt - ds) : ℤ) else 0) from
      dif_pos hfuture]
    by_cases htime : n = (Ct-Cs) + (dt-ds)
    · rw [show dite (n = Ct - Cs + (dt - ds))
        (fun htime => (n.choose (dt - ds) : ℤ)) (fun _ => 0)
        = (n.choose (dt - ds) : ℤ) from dif_pos htime]
      rw [Finset.sum_eq_single (dt-ds)]
      · have hpath :
            dt-ds ≤ dt ∧ n-(dt-ds) ≤ Ct := by
          constructor
          · exact Nat.sub_le _ _
          · omega
        rw [dif_pos hpath]
        have hpred :
            ((⟨Ct-(n-(dt-ds)), by omega⟩,
              ⟨dt-(dt-ds), by omega⟩) : WorldCell A B) =
              (⟨Cs,hCs⟩,⟨ds,hds⟩) := by
          apply Prod.ext
          · apply Fin.ext
            show Ct-(n-(dt-ds)) = Cs
            have hsd : ds ≤ dt := hfuture.2
            have hss : Cs ≤ Ct := hfuture.1
            have htm : n = (Ct-Cs) + (dt-ds) := htime
            omega
          · apply Fin.ext
            show dt-(dt-ds) = ds
            have hsd : ds ≤ dt := hfuture.2
            have htm : n = (Ct-Cs) + (dt-ds) := htime
            omega
        rw [hpred]
        simp [worldBasis]
      · intro m hm hne
        by_cases hpath : m ≤ dt ∧ n-m ≤ Ct
        · rw [dif_pos hpath]
          have hdne : dt - m ≠ ds := by
            intro heq
            have hmd : m ≤ dt := hpath.1
            have hsd : ds ≤ dt := hfuture.2
            exact hne (by omega)
          have hpred_ne :
              ((⟨Ct-(n-m), by omega⟩,
                ⟨dt-m, by omega⟩) : WorldCell A B) ≠
                (⟨Cs,hCs⟩,⟨ds,hds⟩) := by
            intro heq
            have h := congrArg (fun x : WorldCell A B => x.2.1) heq
            simp only at h
            exact hdne h
          simp [worldBasis, hpred_ne]
        · rw [dif_neg hpath]
      · intro hnot
        have hmem : dt-ds ∈ Finset.range (n+1) := by
          apply Finset.mem_range.mpr
          omega
        exact (hnot hmem).elim
    · rw [show dite (n = Ct - Cs + (dt - ds))
        (fun htime => (n.choose (dt - ds) : ℤ)) (fun _ => 0)
        = 0 from dif_neg htime]
      apply Finset.sum_eq_zero
      intro m hm
      by_cases hpath : m ≤ dt ∧ n-m ≤ Ct
      · rw [dif_pos hpath]
        have hpred_ne :
            ((⟨Ct-(n-m), by omega⟩,
              ⟨dt-m, by omega⟩) : WorldCell A B) ≠
                (⟨Cs,hCs⟩,⟨ds,hds⟩) := by
          intro heq
          have hC := congrArg (fun x : WorldCell A B => x.1.1) heq
          have hd := congrArg (fun x : WorldCell A B => x.2.1) heq
          simp only at hC hd
          have hmd : m ≤ dt := hpath.1
          have hnm : n - m ≤ Ct := hpath.2
          have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
          exact htime (by omega)
        simp [worldBasis, hpred_ne]
      · rw [dif_neg hpath]
  · rw [show dite (Cs ≤ Ct ∧ ds ≤ dt)
        (fun hfuture => if htime : n = Ct - Cs + (dt - ds) then (n.choose (dt - ds) : ℤ) else 0)
        (fun _ => 0) = 0 from dif_neg hfuture]
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hpath : m ≤ dt ∧ n-m ≤ Ct
    · rw [dif_pos hpath]
      have hpred_ne :
          ((⟨Ct-(n-m), by omega⟩,
            ⟨dt-m, by omega⟩) : WorldCell A B) ≠
              (⟨Cs,hCs⟩,⟨ds,hds⟩) := by
        intro heq
        have hC := congrArg (fun x : WorldCell A B => x.1.1) heq
        have hd := congrArg (fun x : WorldCell A B => x.2.1) heq
        simp only at hC hd
        push_neg at hfuture
        by_cases hCC : Cs ≤ Ct
        · have hdout : dt < ds := hfuture hCC
          omega
        · have hCout : Cs > Ct := by omega
          omega
      simp [worldBasis, hpred_ne]
    · rw [dif_neg hpath]

/-- Exact coefficient at the unique causal time. -/
theorem worldAct_L_pow_basis_exact
    {A B n : Nat} (s t : WorldCell A B)
    (hfuture : worldForward s t)
    (htime : n = worldCausalDistance s t) :
    worldAct A B ((L A B)^n) (worldBasis s) t =
      (n.choose (digitDistance s t) : ℤ) := by
  rw [worldAct_L_pow_basis_kernel]
  simp [hfuture, htime]

/-- Every wrong-time matrix coefficient vanishes even inside the forward
causal cone. -/
theorem worldAct_L_pow_basis_wrong_time_zero
    {A B n : Nat} (s t : WorldCell A B)
    (hfuture : worldForward s t)
    (htime : n ≠ worldCausalDistance s t) :
    worldAct A B ((L A B)^n) (worldBasis s) t = 0 := by
  rw [worldAct_L_pow_basis_kernel]
  simp [hfuture, htime]

/-- No Lefschetz path propagates backwards along either native world axis. -/
theorem worldAct_L_pow_basis_outside_future_zero
    {A B n : Nat} (s t : WorldCell A B)
    (hfuture : ¬ worldForward s t) :
    worldAct A B ((L A B)^n) (worldBasis s) t = 0 := by
  rw [worldAct_L_pow_basis_kernel]
  simp [hfuture]

/-- A nonzero matrix coefficient forces both causal reachability and the
unique exact propagation time. -/
theorem nonzero_lefschetz_transition_forces_causality
    {A B n : Nat} (s t : WorldCell A B)
    (hne :
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0) :
    worldForward s t ∧ n = worldCausalDistance s t := by
  constructor
  · by_contra hfuture
    have hz :=
      worldAct_L_pow_basis_outside_future_zero
        (A:=A) (B:=B) (n:=n) s t hfuture
    exact hne hz
  · have hfuture : worldForward s t := by
      by_contra hfuture
      have hz :=
        worldAct_L_pow_basis_outside_future_zero
          (A:=A) (B:=B) (n:=n) s t hfuture
      exact hne hz
    by_contra htime
    have hz :=
      worldAct_L_pow_basis_wrong_time_zero
        (A:=A) (B:=B) (n:=n) s t hfuture htime
    exact hne hz

/-!
## Exact causal support, not merely a necessary forward-cone law

A native coefficient is nonzero if and only if the target is in the true
forward causal cone AND the observation time is its exact Manhattan depth.
The reverse direction is substantive: binomial path multiplicities never
vanish over the integral GST world.
-/

/-!
## The exact graded causal cone, length cocycle and positive spectral support

The universal Lefschetz law does more than detect an admissible coordinate:
its integral matrix kernel is strictly positive at every legitimate causal
time.  Its support forms a graded transitive causal relation, with an
exactly additive path length.  Thus finite GST worlds carry a graded
enriched-causality law without any fixed cell count or chart dimension.
-/

/-- Genuine forward causal motion composes without losing either GST axis. -/
theorem worldForward_trans
    {A B : Nat} {s t u : WorldCell A B}
    (hst : worldForward s t) (htu : worldForward t u) :
    worldForward s u :=
  ⟨le_trans hst.1 htu.1, le_trans hst.2 htu.2⟩

/-- The exact causal length is a 1-cocycle on forward-composable world
transitions, not merely a nonnegative coordinate heuristic. -/
theorem worldCausalDistance_add_of_forward
    {A B : Nat} {s t u : WorldCell A B}
    (hst : worldForward s t) (htu : worldForward t u) :
    worldCausalDistance s u =
      worldCausalDistance s t + worldCausalDistance t u := by
  rcases s with ⟨⟨Cs, hCs⟩, ⟨ds, hds⟩⟩
  rcases t with ⟨⟨Ct, hCt⟩, ⟨dt, hdt⟩⟩
  rcases u with ⟨⟨Cu, hCu⟩, ⟨du, hdu⟩⟩
  dsimp [worldForward, worldCausalDistance, carryDistance,
    digitDistance] at *
  omega

/-- **STRICTLY POSITIVE KERNEL CLASSIFIER.**
The integer coefficient of a genuine causal transition cannot cancel.
It is strictly positive precisely at its unique geometric propagation time. -/
theorem lefschetz_transition_positive_iff
    {A B n : Nat} (s t : WorldCell A B) :
    0 < worldAct A B ((L A B)^n) (worldBasis s) t ↔
      worldForward s t ∧ n = worldCausalDistance s t := by
  constructor
  · intro hpositive
    exact nonzero_lefschetz_transition_forces_causality s t
      (ne_of_gt hpositive)
  · rintro ⟨hfuture, htime⟩
    rw [worldAct_L_pow_basis_exact s t hfuture htime]
    have hle : digitDistance s t ≤ n := by
      unfold worldCausalDistance at htime
      omega
    exact_mod_cast Nat.choose_pos hle

/-- **FULL CAUSAL NONZERO CLASSIFIER, BOTH DIRECTIONS.** -/
theorem lefschetz_transition_nonzero_iff
    {A B n : Nat} (s t : WorldCell A B) :
    worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0 ↔
      worldForward s t ∧ n = worldCausalDistance s t := by
  constructor
  · exact nonzero_lefschetz_transition_forces_causality s t
  · intro hcausal
    exact ne_of_gt ((lefschetz_transition_positive_iff s t).2 hcausal)

/-- **CAUSAL SEMIGROUP LAW FOR ALL LEFSCHETZ POWERS.**
Two live transitions whose causal endpoints match always compose to a live
transition, and their exact unique propagation times add.  This is a native
higher-order semigroup law derived from the FULL integral kernel. -/
theorem nonzero_lefschetz_transition_comp
    {A B n m : Nat} {s t u : WorldCell A B}
    (hst :
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0)
    (htu :
      worldAct A B ((L A B)^m) (worldBasis t) u ≠ 0) :
    worldAct A B ((L A B)^(n+m)) (worldBasis s) u ≠ 0 := by
  obtain ⟨hforward₁, htime₁⟩ :=
    (lefschetz_transition_nonzero_iff s t).mp hst
  obtain ⟨hforward₂, htime₂⟩ :=
    (lefschetz_transition_nonzero_iff t u).mp htu
  apply (lefschetz_transition_nonzero_iff s u).2
  refine ⟨worldForward_trans hforward₁ hforward₂, ?_⟩
  calc
    n + m = worldCausalDistance s t + worldCausalDistance t u := by
      rw [htime₁, htime₂]
    _ = worldCausalDistance s u :=
      (worldCausalDistance_add_of_forward hforward₁ hforward₂).symm

/-- Higher-order positive transitions also compose without cancellation.
The depth-additivity theorem above is the strict causal time law. -/
theorem positive_lefschetz_transition_comp
    {A B n m : Nat} {s t u : WorldCell A B}
    (hst : 0 < worldAct A B ((L A B)^n) (worldBasis s) t)
    (htu : 0 < worldAct A B ((L A B)^m) (worldBasis t) u) :
    0 < worldAct A B ((L A B)^(n+m)) (worldBasis s) u := by
  have hs := (lefschetz_transition_positive_iff s t).mp hst
  have ht := (lefschetz_transition_positive_iff t u).mp htu
  apply (lefschetz_transition_positive_iff s u).2
  refine ⟨worldForward_trans hs.1 ht.1, ?_⟩
  calc
    n + m = worldCausalDistance s t + worldCausalDistance t u := by
      rw [hs.2, ht.2]
    _ = worldCausalDistance s u :=
      (worldCausalDistance_add_of_forward hs.1 ht.1).symm

/-- Origin-to-cell propagation is the universal binomial kernel.  The earlier
bottom-to-top coefficient is just the maximal-degree specialization. -/
theorem origin_to_cell_kernel
    (A B C d : Nat) (hC : C < A) (hd : d < B) :
    worldAct A B ((L A B)^(C+d))
      (worldBasis
        (⟨0, by omega⟩, ⟨0, by omega⟩))
      (⟨C,hC⟩,⟨d,hd⟩) =
        ((C+d).choose d : ℤ) := by
  apply worldAct_L_pow_basis_exact
  · constructor <;> simp [worldForward]
  · unfold worldCausalDistance carryDistance digitDistance
    simp

/-- The historical 4 x 3 top transition is one entry of the universal
transition kernel. -/
theorem hc_origin_to_top_kernel :
    worldAct 4 3 ((L 4 3)^5)
      (worldBasis
        (⟨0, by decide⟩, ⟨0, by decide⟩))
      (⟨3, by decide⟩, ⟨2, by decide⟩) = 10 := by
  have h := origin_to_cell_kernel 4 3 3 2 (by decide) (by decide)
  have hten : ((3+2 : ℕ).choose 2 : ℤ) = 10 := rfl
  rw [hten] at h
  simpa using h

/-!
## Exact nilpotency depth of every genuinely two-axis finite world

The previous theory gave an upper extinction bound.  The native binomial
kernel gives its sharp converse: for each time STRICTLY below the boundary
a concrete origin-to-cell coefficient is nonzero, and every later power
kills every finite-world coefficient field.  Thus the endomorphism has
exactly the asserted nilpotency index, with no dimension-specific table.
-/

/-- **EVERY SUBTERMINAL LEFSCHETZ TIME HAS A LIVE MATRIX COEFFICIENT.**
The live target is chosen canonically by carrying as far as possible and
assigning the remaining depth to the digit axis. -/
theorem finite_world_L_each_subterminal_power_nonzero
    (A B n : Nat)
    (hA : 0 < A) (hB : 0 < B)
    (hn : n < A + B - 1) :
    ∃ s t : WorldCell A B,
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0 := by
  let C := min n (A - 1)
  let d := n - C
  have hC : C < A := by
    dsimp [C]
    omega
  have hd : d < B := by
    dsimp [d, C]
    omega
  have hsum : C + d = n := by
    dsimp [d, C]
    omega
  let s : WorldCell A B :=
    (⟨0, by omega⟩, ⟨0, by omega⟩)
  let t : WorldCell A B := (⟨C, hC⟩, ⟨d, hd⟩)
  refine ⟨s, t, ?_⟩
  have hvalue := origin_to_cell_kernel A B C d hC hd
  have hcoefficient :
      worldAct A B ((L A B)^n) (worldBasis s) t =
        (n.choose d : ℤ) := by
    simpa only [hsum] using hvalue
  rw [hcoefficient]
  have hpos : 0 < n.choose d := Nat.choose_pos (by omega)
  exact_mod_cast (Nat.ne_of_gt hpos)

/-- Every finite-world power at or beyond the exact geometric horizon
annihilates ALL native fields, not merely the distinguished origin state. -/
theorem finite_world_L_extinct_at_and_after_boundary
    (A B n : Nat)
    (hn : A + B - 1 ≤ n)
    (g : WorldCoef A B) :
    worldAct A B ((L A B)^n) g = 0 := by
  have hsplit : n = (A + B - 1) + (n - (A + B - 1)) := by
    omega
  rw [hsplit, pow_add, worldAct_mul]
  exact worldAct_L_pow_boundary A B _

/-- **SHARP NILPOTENCY SPECTRUM OF EVERY FINITE GST WORLD.**
For A,B>0, the universal Lefschetz operator kills every coefficient field
at time n if and only if n has reached the exact rectangular boundary
A+B-1.  No weaker nilpotency exponent is possible. -/
theorem finite_world_L_power_zero_iff_boundary
    (A B n : Nat) (hA : 0 < A) (hB : 0 < B) :
    (∀ g : WorldCoef A B,
      worldAct A B ((L A B)^n) g = 0) ↔ A + B - 1 ≤ n := by
  constructor
  · intro hzero
    by_contra hnot
    have hlt : n < A + B - 1 := Nat.lt_of_not_ge hnot
    obtain ⟨s, t, hnonzero⟩ :=
      finite_world_L_each_subterminal_power_nonzero A B n hA hB hlt
    have hz := congrFun (hzero (worldBasis s)) t
    exact hnonzero hz
  · intro hn g
    exact finite_world_L_extinct_at_and_after_boundary A B n hn g

/-- One intrinsic spectral certificate contains both the exact causal
support law and the true nilpotency horizon for ALL positive rectangles. -/
theorem omniversal_L_sharp_spectrum :
    (∀ A B n (s t : WorldCell A B),
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0 ↔
        worldForward s t ∧ n = worldCausalDistance s t)
    ∧ (∀ A B n, 0 < A → 0 < B →
      ((∀ g : WorldCoef A B, worldAct A B ((L A B)^n) g = 0) ↔
        A + B - 1 ≤ n)) := by
  constructor
  · intro A B n s t
    exact lefschetz_transition_nonzero_iff s t
  · intro A B n hA hB
    exact finite_world_L_power_zero_iff_boundary A B n hA hB

/-- Capstone: every matrix entry is classified, every nonzero transition has
a unique causal time, and the historical coefficient 10 is absorbed as one
special case. -/
theorem universal_lefschetz_kernel_crown :
    (∀ A B n (s t : WorldCell A B),
      worldAct A B ((L A B)^n) (worldBasis s) t =
        if hfuture : worldForward s t then
          if htime : n = worldCausalDistance s t then
            (n.choose (digitDistance s t) : ℤ)
          else 0
        else 0)
    ∧ (∀ A B n (s t : WorldCell A B),
      worldAct A B ((L A B)^n) (worldBasis s) t ≠ 0 →
        worldForward s t ∧ n = worldCausalDistance s t)
    ∧ worldAct 4 3 ((L 4 3)^5)
        (worldBasis
          (⟨0, by decide⟩, ⟨0, by decide⟩))
        (⟨3, by decide⟩, ⟨2, by decide⟩) = 10 := by
  exact ⟨
    worldAct_L_pow_basis_kernel,
    fun A B n s t h =>
      (lefschetz_transition_nonzero_iff s t).mp h,
    hc_origin_to_top_kernel⟩

#check worldForward
#check carryDistance
#check digitDistance
#check worldCausalDistance
#check worldAct_L_pow_basis_kernel
#check worldAct_L_pow_basis_exact
#check worldAct_L_pow_basis_wrong_time_zero
#check worldAct_L_pow_basis_outside_future_zero
#check nonzero_lefschetz_transition_forces_causality
#check origin_to_cell_kernel
#check hc_origin_to_top_kernel
#check lefschetz_transition_nonzero_iff
#check finite_world_L_each_subterminal_power_nonzero
#check finite_world_L_power_zero_iff_boundary
#check omniversal_L_sharp_spectrum
#check universal_lefschetz_kernel_crown

#print axioms worldAct_L_pow_basis_kernel
#print axioms nonzero_lefschetz_transition_forces_causality
#print axioms origin_to_cell_kernel
#print axioms universal_lefschetz_kernel_crown


/-! ## The exact kernel on the unbounded grid -/
open GSTUniversalLefschetzCosmology

def cosmicBasis (s : CosmicCell) : CompletedCosmos := fun t => if t=s then 1 else 0

theorem cosmicLefschetz_kernel (n : ℕ) (s t : CosmicCell) :
    (cosmicLefschetz^n) (cosmicBasis s) t =
      if s.1 ≤ t.1 ∧ s.2 ≤ t.2 then
        if n = (t.1-s.1)+(t.2-s.2) then (n.choose (t.2-s.2) : ℤ) else 0
      else 0 := by
  let A := max s.1 t.1 + 1
  let B := max s.2 t.2 + 1
  let sf : WorldCell A B := (⟨s.1, by dsimp [A]; omega⟩,⟨s.2, by dsimp [B]; omega⟩)
  let tf : WorldCell A B := (⟨t.1, by dsimp [A]; omega⟩,⟨t.2, by dsimp [B]; omega⟩)
  have hb : observe A B (cosmicBasis s) = worldBasis sf := by
    funext c
    simp [observe, cosmicBasis, worldBasis, sf, Prod.ext_iff, Fin.ext_iff]
  have ho := congrFun (worldAct_is_cosmic_observation A B n (cosmicBasis s)) tf
  rw [hb, worldAct_L_pow_basis_kernel] at ho
  by_cases hcond : worldForward sf tf
  · have hcond' : s.1 ≤ t.1 ∧ s.2 ≤ t.2 := hcond
    rw [dif_pos hcond] at ho
    rw [if_pos hcond']
    by_cases htime : n = worldCausalDistance sf tf
    · have htime' : n = (t.1-s.1)+(t.2-s.2) := htime
      rw [dif_pos htime] at ho
      rw [if_pos htime']
      simpa [observe, worldForward, worldCausalDistance, carryDistance,
        digitDistance, sf, tf] using ho.symm
    · rw [dif_neg htime] at ho
      have hne : ¬ n = (t.1-s.1)+(t.2-s.2) := htime
      rw [if_neg hne]
      simpa [observe, worldForward, worldCausalDistance, carryDistance,
        digitDistance, sf, tf] using ho.symm
  · rw [dif_neg hcond] at ho
    have hne : ¬ (s.1 ≤ t.1 ∧ s.2 ≤ t.2) := hcond
    rw [if_neg hne]
    simpa [observe, worldForward, worldCausalDistance, carryDistance,
      digitDistance, sf, tf] using ho.symm

/-- A unit source propagates at every natural time: there is no global ceiling. -/
theorem cosmicLefschetz_never_extinguishes (n : ℕ) :
    (cosmicLefschetz^n) (cosmicBasis (0,0)) (0,n) = 1 := by
  simp [cosmicLefschetz_kernel]

theorem cosmicLefschetz_not_nilpotent : ¬ IsNilpotent cosmicLefschetz := by
  rintro ⟨n, hn⟩
  have h := cosmicLefschetz_never_extinguishes n
  rw [hn] at h
  norm_num at h

#print axioms cosmicLefschetz_kernel
#print axioms cosmicLefschetz_not_nilpotent

/-- A compact source also survives every depth. Finite support at each time
must never be confused with a fixed observation boundary for all time. -/
theorem compactEvolution_never_extinguishes (n : ℕ) :
    compactEvolution n (Finsupp.single (0,0) 1) (0,n) = 1 := by
  have hb : ((Finsupp.single (0,0) (1 : ℤ) :
      CompactCosmos) : CompletedCosmos) =
      cosmicBasis (0,0) := by
    funext c
    simp [cosmicBasis, Finsupp.single_apply, eq_comm]
  have h := congrFun (compactEvolution_completed n (Finsupp.single (0,0) 1)) (0,n)
  rw [hb, cosmicLefschetz_never_extinguishes] at h
  exact h

#print axioms compactEvolution_never_extinguishes

end GSTUniversalLefschetzKernel
