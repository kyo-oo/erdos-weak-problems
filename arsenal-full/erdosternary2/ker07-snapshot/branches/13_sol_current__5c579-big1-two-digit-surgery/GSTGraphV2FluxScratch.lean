/- ======================================================================
/- CHRONOLOGICAL LABEL -- #0533 / 1132
/-    Path         : branches/sol_5c579-big1-two-digit-surgery/GSTGraphV2FluxScratch.lean
/-    Ref          : origin/sol/5c579-big1-two-digit-surgery
/-    First-commit : 2026-08-16 02:16:16 +0530  (886c096)
/-    Last-commit  : 2026-08-16 02:20:10 +0530  (84a8784)
/-    Total commits: 2
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- [01/2] 2026-08-16 02:16:16 +0530  886c096  (ker07-dev)
/-        Add GST Graph V2 event mass sectors
/- [02/2] 2026-08-16 02:20:10 +0530  84a8784  (ker07-dev)
/-        Add mod-11 BIG2 species invariant
/- ====================================================================== -/

import GSTGraphV2Scratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
GST Graph V2 local information flux.
Every legal multiply-by-four cell is compressed to the mass C + 4*d in
{0,...,11}.  The four event types occupy exact disjoint mass sectors.
-/

def gstCellMassV2S (C d : Nat) : Nat := C + 4*d

def gstCellOutputV2S (C d : Nat) : Nat := (C + 4*d) % 3

def gstCellNextCarryV2S (C d : Nat) : Nat := (C + 4*d) / 3

/-- Exact local conservation of one GST cell. -/
theorem gst_cell_mass_conservationV2S (C d : Nat) :
    gstCellMassV2S C d =
      gstCellOutputV2S C d + 3 * gstCellNextCarryV2S C d := by
  unfold gstCellMassV2S gstCellOutputV2S gstCellNextCarryV2S
  have h := Nat.mod_add_div (C + 4*d) 3
  omega

/-- SURVIVE occupies exactly masses 8 and 11. -/
theorem gst_cell_survive_iff_massV2S
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (d = 2 ∧ gstCellOutputV2S C d = 2) ↔
      (gstCellMassV2S C d = 8 ∨ gstCellMassV2S C d = 11) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;> decide

/-- CREATE occupies exactly masses 2 and 5. -/
theorem gst_cell_create_iff_massV2S
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (d ≠ 2 ∧ gstCellOutputV2S C d = 2) ↔
      (gstCellMassV2S C d = 2 ∨ gstCellMassV2S C d = 5) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;> decide

/-- DESTROY occupies exactly masses 9 and 10. -/
theorem gst_cell_destroy_iff_massV2S
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (d = 2 ∧ gstCellOutputV2S C d ≠ 2) ↔
      (gstCellMassV2S C d = 9 ∨ gstCellMassV2S C d = 10) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;> decide

/-- The parent cell mass is one residue of the shared carrier.  This unifies
all three rotating residue-12 cases into a single equation. -/
theorem gst_parent_cell_mass_from_sharedV2S
    (S D Z r : Nat)
    (hD : D < 4)
    (hr : r < 3)
    (hS : S = D + 4*Z) :
    gstCellMassV2S D ((Z+r)%3) = (S + 4*r) % 12 := by
  have hP : (Z+r)%3 < 3 := Nat.mod_lt _ (by decide)
  have hmass : D + 4*((Z+r)%3) < 12 := by omega
  have hmod : (D + 4*(Z+r)) % 12 = D + 4*((Z+r)%3) := by
    have hz : Z+r = 3*((Z+r)/3) + (Z+r)%3 :=
      (Nat.div_add_mod (Z+r) 3).symm
    rw [hz]
    have hshape :
        D + 4 * (3 * ((Z+r)/3) + (Z+r)%3) =
          (D + 4*((Z+r)%3)) + 12*((Z+r)/3) := by ring
    rw [hshape, Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hmass]
  unfold gstCellMassV2S
  rw [hS]
  have hshape : D + 4*Z + 4*r = D + 4*(Z+r) := by ring
  rw [hshape, hmod]

/-- Unified parent SURVIVE classifier in the shared carrier coordinates. -/
theorem gst_parent_survive_iff_shared_mass_sectorV2S
    (S D Z r : Nat)
    (hD : D < 4)
    (hr : r < 3)
    (hS : S = D + 4*Z) :
    (((Z+r)%3 = 2) ∧
      (gstCellOutputV2S D ((Z+r)%3) = 2)) ↔
      ((S + 4*r) % 12 = 8 ∨ (S + 4*r) % 12 = 11) := by
  have hp : (Z+r)%3 < 3 := Nat.mod_lt _ (by decide)
  rw [gst_cell_survive_iff_massV2S D ((Z+r)%3) hD hp]
  rw [gst_parent_cell_mass_from_sharedV2S S D Z r hD hr hS]

/-!
The local re-coordinate map acts on the mass by multiplication by four modulo
11.  Because 4 has order five modulo 11, the ten non-fixed legal masses split
into two exact five-cycles.  This is a local coordinate invariant only; no
global mirror principle is assumed.
-/

/-- One local GST re-coordinate rotates the mass by x |-> 4x modulo 11. -/
theorem gst_local_rotate_mass_mod11V2S
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    let y := gstLocalRotateS (C,d)
    gstCellMassV2S y.1 y.2 % 11 =
      (4 * gstCellMassV2S C d) % 11 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;> decide

/-- The nonzero BIG2 species is the second five-cycle together with the fixed
SURVIVE mass 11. -/
def GSTBig2MassSpeciesV2S (M : Nat) : Prop :=
  M = 2 ∨ M = 6 ∨ M = 7 ∨ M = 8 ∨ M = 10 ∨ M = 11

/-- A legal child Happy Gate always begins in the BIG2 mass species. -/
theorem gst_child_happy_has_big2_mass_speciesV2S
    (C : Nat) (hC : C = 0 ∨ C = 3) :
    GSTBig2MassSpeciesV2S (gstCellMassV2S C 2) := by
  rcases hC with h0 | h3 <;> subst C <;>
    simp [GSTBig2MassSpeciesV2S, gstCellMassV2S]

/-- The BIG2 five-cycle is closed under one local re-coordinate. -/
theorem gst_big2_species_rotate_closedV2S
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbig : GSTBig2MassSpeciesV2S (gstCellMassV2S C d)) :
    let y := gstLocalRotateS (C,d)
    GSTBig2MassSpeciesV2S (gstCellMassV2S y.1 y.2) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    simp [GSTBig2MassSpeciesV2S, gstCellMassV2S, gstLocalRotateS] at hbig ⊢

/-- Every legal BIG2-species cell reaches a SURVIVE mass (8 or 11) within at
most four local coordinate rotations. -/
theorem gst_big2_species_hits_survive_within_fourV2S
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbig : GSTBig2MassSpeciesV2S (gstCellMassV2S C d)) :
    let x0 := (C,d)
    let x1 := gstLocalRotateS x0
    let x2 := gstLocalRotateS x1
    let x3 := gstLocalRotateS x2
    let x4 := gstLocalRotateS x3
    (gstCellMassV2S x0.1 x0.2 = 8 ∨ gstCellMassV2S x0.1 x0.2 = 11) ∨
    (gstCellMassV2S x1.1 x1.2 = 8 ∨ gstCellMassV2S x1.1 x1.2 = 11) ∨
    (gstCellMassV2S x2.1 x2.2 = 8 ∨ gstCellMassV2S x2.1 x2.2 = 11) ∨
    (gstCellMassV2S x3.1 x3.2 = 8 ∨ gstCellMassV2S x3.1 x3.2 = 11) ∨
    (gstCellMassV2S x4.1 x4.2 = 8 ∨ gstCellMassV2S x4.1 x4.2 = 11) := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with h0 | h1 | h2 | h3 <;>
    rcases hdc with d0 | d1 | d2 <;>
    subst C <;> subst d <;>
    simp [GSTBig2MassSpeciesV2S, gstCellMassV2S, gstLocalRotateS] at hbig ⊢
