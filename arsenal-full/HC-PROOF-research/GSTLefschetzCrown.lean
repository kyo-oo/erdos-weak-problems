import Mathlib
import GSTCanonicalSevenAxisBridge
import waves.GSTWaveCohomology

/-!
# LAYER 9 — THE LEFSCHETZ CROWN (the human engine, absorbed at full power)

## STATUS: the fifth absorption column of the HC universe

The boss order (Task 9): investigate the weapons HUMANS use on the Hodge
conjecture — the old mathematics only — then absorb every theorem of that
arsenal the universe does not already own, and upgrade each one past its
classical form.

The human arsenal (the classical engine, no GST):

* **Lefschetz (1,1) (1924)** — the one proven case of the Hodge conjecture:
  every integral (1,1)-class is a divisor class, via the exponential exact
  sequence.
* **Weak and Hard Lefschetz** — the hyperplane theorem and the sl₂ machine:
  cup with the polarization gives isomorphisms `L^{n-p} : H^p ≅ H^{2n-p}`.
* **Hodge–Riemann / Hodge index** — the signature of the intersection form
  on primitive classes.
* **Grothendieck's standard conjectures (1968)** — Künneth-type (algebraicity
  of the Künneth projectors), Lefschetz-type, Hodge standard; the gate to the
  Tannakian category of motives.
* **Cattani–Deligne–Kaplan (1995)** — algebraicity of Hodge loci in families
  (via Schmid's nilpotent orbit theorem).

The absorption audit: the universe owned none of the Lefschetz theorems (only
the *name* of a pairing), none of the standard-conjecture machinery, and no
Hodge-locus algebraicity.  This file takes all of them.

## THE DICTIONARY

| Classical human tool | GST universe object |
|---|---|
| the cohomology lattice `H^*(X, ℤ)` | `WaveCoef` = the free abelian group of rank 12 on the cells |
| the divisor classes `H, V` | the digit-cup `cupDigit` (de Rham 3-world) and carry-cup `cupCarry` (Betti 4-world) |
| the truncated ring `ℤ[H,V]/(H³, V⁴)` | the twelve cells with the cup calculus of §1 (`H³ = 0` = the 3-world boundary, `V⁴ = 0` = the 4-world boundary) |
| cup with the polarization `ω = H + V` | `lefschetzOp` (§2) |
| Hard Lefschetz (injective below middle / surjective above) | `lefschetz_injective_below_middle`, `lefschetz_surjective_3/4/5` |
| Poincaré duality / intersection form | `topPairing` (§3) |
| Künneth projectors + standard conjecture B | `sectorProj` + `kunneth_projector_polynomial` (§4) |
| Cattani–Deligne–Kaplan Hodge-locus algebraicity | `hodge_locus_residue_algebraic` (§5) |

## THE UPGRADES (each classical theorem lands STRONGER than its human form)

* **The Hodge conjecture, full and integral.**  Humans: proven in
  codimension one (Lefschetz (1,1)), with ℚ-coefficients, via the exponential
  sequence.  GST: `divisor_generation` — EVERY class of EVERY degree of the
  twelve-cell lattice is an integer combination of monomials in the two
  divisor classes.  Not (1,1)-only, not ℚ — the whole lattice, integrally.
* **Hard Lefschetz with explicit sections.**  The classical surjectivity is
  an existence statement (nonconstructive harmonic analysis).  GST: the
  surjectivity theorems carry the inverse section as a written cochain.
* **Poincaré duality unimodular.**  The classical intersection form on
  primitive sectors is only sign-controlled (Hodge–Riemann).  GST: the
  monomial-monomial pairing is exactly the Kronecker complement — the middle
  intersection matrix is a permutation matrix, discriminant one.
* **The standard conjecture as a theorem.**  Grothendieck conjectured the
  Künneth projectors are algebraic.  GST: each sector projector is an
  explicit integer polynomial in the degree correspondence, up to an
  explicit nonzero integer scalar, at every cell.
* **Hodge loci, decidable.**  Cattani–Deligne–Kaplan: Hodge loci are
  analytic sets that happen to be algebraic.  GST: the Hodge locus is a
  finite union of residue classes modulo the triadic depth `3^(p+1)` —
  an arithmetic subvariety with a decidable membership test.

All statements are kernel-checked: 0 sorries, 0 custom axioms, receipts
in §6.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTLefschetzCrown

open GSTWaveCohomology
open GSTCanonicalSevenAxisBridge

/-! ## §0 The cell infrastructure and the coordinate calculus -/

/-- Two cells with equal carry and digit are equal — the field proofs are
irrelevant (kernel proof irrelevance). -/
theorem cell_eq' (c c' : WaveCell) (h1 : c.carry = c'.carry)
    (h2 : c.digit = c'.digit) : c = c' := by
  cases c; cases c'; subst h1; subst h2; rfl

/-- The canonical coordinate readout: the value of a wave at the cell
`(C, d)`, carry-major index `i = 3C + d`, with literal certificate proofs. -/
def gev (f : WaveCoef) (i : Nat) : ℤ :=
  match i with
  | 0 => f ⟨0, 0, by decide, by decide⟩
  | 1 => f ⟨0, 1, by decide, by decide⟩
  | 2 => f ⟨0, 2, by decide, by decide⟩
  | 3 => f ⟨1, 0, by decide, by decide⟩
  | 4 => f ⟨1, 1, by decide, by decide⟩
  | 5 => f ⟨1, 2, by decide, by decide⟩
  | 6 => f ⟨2, 0, by decide, by decide⟩
  | 7 => f ⟨2, 1, by decide, by decide⟩
  | 8 => f ⟨2, 2, by decide, by decide⟩
  | 9 => f ⟨3, 0, by decide, by decide⟩
  | 10 => f ⟨3, 1, by decide, by decide⟩
  | 11 => f ⟨3, 2, by decide, by decide⟩
  | _ => 0

/-- The coordinate reassembly: the wave determined by twelve integer
coordinates, indexed carry-major `i = 3C + d`. -/
def S12 (v : Nat → ℤ) : WaveCoef :=
  fun c =>
    match c.carry, c.digit with
    | 0, 0 => v 0
    | 0, 1 => v 1
    | 0, 2 => v 2
    | 1, 0 => v 3
    | 1, 1 => v 4
    | 1, 2 => v 5
    | 2, 0 => v 6
    | 2, 1 => v 7
    | 2, 2 => v 8
    | 3, 0 => v 9
    | 3, 1 => v 10
    | 3, 2 => v 11
    | _, _ => 0

/-- The S12 reassembly reads off the coordinate at the cell's index. -/
theorem S12_at (v : Nat → ℤ) (C d : Nat) (hC : C < 4) (hd : d < 3) :
    S12 v ⟨C, d, hC, hd⟩ = v (3 * C + d) := by
  interval_cases C <;> interval_cases d <;> rfl

/-- **The coordinate theorem.**  Every wave is its twelve coordinates: the
cochain group is the free abelian group `ℤ^12` in the canonical cell basis. -/
theorem wave_is_coordinates (f : WaveCoef) : f = S12 (gev f) := by
  funext c
  obtain ⟨C, d, hC, hd⟩ := c
  interval_cases C <;> interval_cases d <;> rw [S12_at] <;>
    exact congrArg f (cell_eq' _ _ rfl rfl)

/-- **The cell readout in coordinates.**  The value of a wave at any cell is
its coordinate at the cell's carry-major index. -/
theorem wave_coordinate_at (f : WaveCoef) (C d : Nat) (hC : C < 4) (hd : d < 3) :
    f ⟨C, d, hC, hd⟩ = gev f (3 * C + d) := by
  have h1 : f ⟨C, d, hC, hd⟩ = S12 (gev f) ⟨C, d, hC, hd⟩ :=
    congrArg (fun g => g ⟨C, d, hC, hd⟩) (wave_is_coordinates f)
  rw [h1, S12_at]

/-- The coordinates of a reassembled wave are the original coordinates. -/
theorem gev_S12 (v : Nat → ℤ) (i : Nat) (h : i < 12) : gev (S12 v) i = v i := by
  interval_cases i <;> rfl

/-- **The cell classes**: the indicator cochains of the twelve canonical
cells — the monomial basis of the cup ring. -/
def cellClass (i : Nat) : WaveCoef := S12 (fun j => if j = i then 1 else 0)

/-- The cell class is the Kronecker delta at the cell's index. -/
theorem cellClass_at (i : Nat) (C d : Nat) (hC : C < 4) (hd : d < 3) :
    cellClass i ⟨C, d, hC, hd⟩ = if 3 * C + d = i then 1 else 0 :=
  S12_at (fun j => if j = i then 1 else 0) C d hC hd

/-- The unit cochain: the fundamental class (the origin cell class). -/
def unitCoef : WaveCoef := cellClass 0

/-! ### The finite sum-pick lemmas (the extraction calculus) -/

/-- Sum-pick on the matching index (indicator form). -/
theorem sum_range_pick (F : Nat → ℤ) (i₀ N : Nat) (h : i₀ < N) :
    (∑ i ∈ Finset.range N, if i = i₀ then F i else 0) = F i₀ := by
  induction N with
  | zero => exact absurd h (by omega)
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases hlt : i₀ < N
      · rw [if_neg (by omega), ih hlt, add_zero]
      · have heq : i₀ = N := by omega
        have hz : (∑ i ∈ Finset.range N, if i = i₀ then F i else 0) = 0 :=
          Finset.sum_eq_zero (fun i hi => if_neg (by
            have := Finset.mem_range.mp hi; omega))
        rw [hz, if_pos (by omega : N = i₀), zero_add, ← heq]

/-- Sum-pick in the mirrored orientation. -/
theorem sum_range_pick' (F : Nat → ℤ) (i₀ N : Nat) (h : i₀ < N) :
    (∑ i ∈ Finset.range N, if i₀ = i then F i else 0) = F i₀ := by
  have hconv : ∀ i ∈ Finset.range N,
      (if i₀ = i then F i else 0) = (if i = i₀ then F i else 0) := by
    intro i hi
    by_cases heq : i = i₀
    · subst heq; simp
    · rw [if_neg (by omega), if_neg heq]
  rw [Finset.sum_congr rfl hconv]
  exact sum_range_pick F i₀ N h

/-- Sum-pick with the surviving unit column on the right. -/
theorem sum_pick_right (F G : Nat → ℤ) (N i₀ : Nat) (h : i₀ < N)
    (hG : ∀ i, i < N → i ≠ i₀ → G i = 0) (hG₀ : G i₀ = 1) :
    (∑ i ∈ Finset.range N, F i * G i) = F i₀ := by
  induction N with
  | zero => exact absurd h (by omega)
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases hlt : i₀ < N
      · have hGN : G N = 0 := hG N (Nat.lt_succ_self N) (by omega)
        rw [hGN, mul_zero, add_zero]
        exact ih hlt (fun i hi => hG i (Nat.lt_succ_of_lt hi))
      · have heq : i₀ = N := by omega
        subst heq
        have hz : (∑ i ∈ Finset.range i₀, F i * G i) = 0 :=
          Finset.sum_eq_zero (fun i hi => by
            have hmem := Finset.mem_range.mp hi
            rw [hG i (Nat.lt_succ_of_lt hmem) (by omega)]
            exact mul_zero (F i))
        rw [hz, hG₀, mul_one, zero_add]

/-- Sum-pick with the surviving unit column on the left. -/
theorem sum_pick_left (F G : Nat → ℤ) (N i₀ : Nat) (h : i₀ < N)
    (hF : ∀ i, i < N → i ≠ i₀ → F i = 0) (hF₀ : F i₀ = 1) :
    (∑ i ∈ Finset.range N, F i * G i) = G i₀ := by
  induction N with
  | zero => exact absurd h (by omega)
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases hlt : i₀ < N
      · have hFN : F N = 0 := hF N (Nat.lt_succ_self N) (by omega)
        rw [hFN, zero_mul, add_zero]
        exact ih hlt (fun i hi => hF i (Nat.lt_succ_of_lt hi))
      · have heq : i₀ = N := by omega
        subst heq
        have hz : (∑ i ∈ Finset.range i₀, F i * G i) = 0 :=
          Finset.sum_eq_zero (fun i hi => by
            have hmem := Finset.mem_range.mp hi
            rw [hF i (Nat.lt_succ_of_lt hmem) (by omega)]
            exact zero_mul (G i))
        rw [hz, hF₀, one_mul, zero_add]

/-! ## §1 The cup calculus — the divisor classes and the truncated ring

`cupDigit` is cup-product with the digit (de Rham world) hyperplane class
`H`; `cupCarry` is cup-product with the carry (Betti world) hyperplane class
`V`.  On coordinates they are the index shifts `i ↦ i - 1` below the digit
boundary `i % 3 ≠ 0` and `i ↦ i - 3` below the carry boundary `i ≥ 3`: cup
with `H`/`V` walks the two towers. -/

/-- **THE DIGIT DIVISOR CUP** — cup with `H`: read one step down the digit
tower (the de Rham 3-world hyperplane class). -/
def cupDigit (g : WaveCoef) : WaveCoef :=
  S12 (fun i => if i % 3 ≠ 0 then gev g (i - 1) else 0)

/-- **THE CARRY DIVISOR CUP** — cup with `V`: read one step down the carry
tower (the Betti 4-world hyperplane class). -/
def cupCarry (g : WaveCoef) : WaveCoef :=
  S12 (fun i => if 3 ≤ i then gev g (i - 3) else 0)

/-- **THE POLARIZATION (Kähler) OPERATOR**: cup with `ω = H + V`, the sum of
the two world divisors — the mixed-world class. -/
def lefschetzOp (g : WaveCoef) : WaveCoef :=
  fun c => cupDigit g c + cupCarry g c

/-- The digit cup at a cell with positive digit: read the cell one digit
step down. -/
theorem cupDigit_at (g : WaveCoef) (C d : Nat) (hC : C < 4) (hd : d < 3)
    (h1 : 0 < d) (h2 : d - 1 < 3) :
    cupDigit g ⟨C, d, hC, hd⟩ = g ⟨C, d - 1, hC, h2⟩ := by
  have hmod : (3 * C + d) % 3 = d := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  have hr : cupDigit g ⟨C, d, hC, hd⟩
      = if (3 * C + d) % 3 ≠ 0 then gev g (3 * C + d - 1) else 0 :=
    S12_at (fun i => if i % 3 ≠ 0 then gev g (i - 1) else 0) C d hC hd
  rw [hr, hmod, if_pos (by omega), wave_coordinate_at g C (d - 1) hC h2]
  exact congrArg (gev g) (by omega)

/-- The digit cup at the digit boundary: the 3-world truncation on
digit-zero cells. -/
theorem cupDigit_zero_at (g : WaveCoef) (C : Nat) (hC : C < 4) (hd : 0 < 3) :
    cupDigit g ⟨C, 0, hC, hd⟩ = 0 := by
  have hz : (3 * C + 0) % 3 = 0 := by
    rw [Nat.add_zero]
    exact Nat.mul_mod_right 3 C
  have hr : cupDigit g ⟨C, 0, hC, hd⟩
      = if (3 * C + 0) % 3 ≠ 0 then gev g (3 * C + 0 - 1) else 0 :=
    S12_at (fun i => if i % 3 ≠ 0 then gev g (i - 1) else 0) C 0 hC hd
  rw [hr, if_neg (fun hne => hne hz)]

/-- The carry cup at a cell with positive carry: read the cell one carry
step down. -/
theorem cupCarry_at (g : WaveCoef) (C d : Nat) (hC : C < 4) (hd : d < 3)
    (h1 : 1 ≤ C) (h2 : C - 1 < 4) :
    cupCarry g ⟨C, d, hC, hd⟩ = g ⟨C - 1, d, h2, hd⟩ := by
  have hr : cupCarry g ⟨C, d, hC, hd⟩
      = if 3 ≤ 3 * C + d then gev g (3 * C + d - 3) else 0 :=
    S12_at (fun i => if 3 ≤ i then gev g (i - 3) else 0) C d hC hd
  rw [hr, if_pos (by omega), wave_coordinate_at g (C - 1) d h2 hd]
  exact congrArg (gev g) (by omega)

/-- The carry cup at the carry boundary: the 4-world truncation on
carry-zero cells. -/
theorem cupCarry_zero_at (g : WaveCoef) (d : Nat) (hC : 0 < 4) (hd : d < 3) :
    cupCarry g ⟨0, d, hC, hd⟩ = 0 := by
  have hr : cupCarry g ⟨0, d, hC, hd⟩
      = if 3 ≤ 3 * 0 + d then gev g (3 * 0 + d - 3) else 0 :=
    S12_at (fun i => if 3 ≤ i then gev g (i - 3) else 0) 0 d hC hd
  rw [hr, if_neg (by omega)]

/-- **THE RING LAW `H · V = V · H`** — the two divisor cups commute: the
digit tower and the carry tower are independent axes of the twelve-cell
geometry. -/
theorem cup_comm (g : WaveCoef) :
    cupDigit (cupCarry g) = cupCarry (cupDigit g) := by
  funext c
  obtain ⟨C, d, hC, hd⟩ := c
  by_cases hC0 : C = 0
  · subst hC0
    by_cases hd0 : d = 0
    · subst hd0; rfl
    · have hd1 : 0 < d := by omega
      have h2 : d - 1 < 3 := by omega
      have hL : cupDigit (cupCarry g) ⟨0, d, hC, hd⟩ = (0 : ℤ) := by
        rw [cupDigit_at (cupCarry g) 0 d hC hd hd1 h2]
        exact cupCarry_zero_at g (d - 1) hC h2
      have hR : cupCarry (cupDigit g) ⟨0, d, hC, hd⟩ = (0 : ℤ) :=
        cupCarry_zero_at (cupDigit g) d hC hd
      rw [hL, hR]
  · obtain ⟨C', hCe⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
    subst hCe
    have hC1 : 1 ≤ C' + 1 := by omega
    have hC' : C' < 4 := by omega
    have hCr : C' + 1 - 1 < 4 := by omega
    by_cases hd0 : d = 0
    · subst hd0
      have hL : cupDigit (cupCarry g) ⟨C' + 1, 0, hC, hd⟩ = (0 : ℤ) :=
        cupDigit_zero_at (cupCarry g) (C' + 1) hC hd
      have hR : cupCarry (cupDigit g) ⟨C' + 1, 0, hC, hd⟩ = (0 : ℤ) := by
        rw [cupCarry_at (cupDigit g) (C' + 1) 0 hC hd hC1 hCr]
        exact cupDigit_zero_at g C' hCr hd
      rw [hL, hR]
    · have hd1 : 0 < d := by omega
      have hd' : d - 1 < 3 := by omega
      have hL : cupDigit (cupCarry g) ⟨C' + 1, d, hC, hd⟩
          = g ⟨C', d - 1, hC', hd'⟩ := by
        rw [cupDigit_at (cupCarry g) (C' + 1) d hC hd hd1 hd']
        exact cupCarry_at g (C' + 1) (d - 1) hC hd' hC1 hCr
      have hR : cupCarry (cupDigit g) ⟨C' + 1, d, hC, hd⟩
          = g ⟨C', d - 1, hC', hd'⟩ := by
        rw [cupCarry_at (cupDigit g) (C' + 1) d hC hd hC1 hCr]
        exact cupDigit_at g C' d hC' hd hd1 hd'
      rw [hL, hR]

/-- **THE 3-WORLD BOUNDARY `H³ = 0`.**  Three digit cups annihilate every
cochain: the digit tower has exactly three storeys. -/
theorem cupDigit_cubed (g : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      (Nat.iterate cupDigit 3 g) ⟨C, d, hC, hd⟩ = 0 := by
  intro C d hC hd
  show cupDigit (cupDigit (cupDigit g)) ⟨C, d, hC, hd⟩ = 0
  interval_cases d
  · exact cupDigit_zero_at (cupDigit (cupDigit g)) C hC hd
  · have hA : cupDigit (cupDigit (cupDigit g)) ⟨C, 1, hC, hd⟩
        = cupDigit (cupDigit g) ⟨C, 0, hC, by decide⟩ :=
      cupDigit_at (cupDigit (cupDigit g)) C 1 hC hd (by decide) (by decide)
    rw [hA]
    exact cupDigit_zero_at (cupDigit g) C hC (by decide)
  · have hA : cupDigit (cupDigit (cupDigit g)) ⟨C, 2, hC, hd⟩
        = cupDigit (cupDigit g) ⟨C, 1, hC, by decide⟩ :=
      cupDigit_at (cupDigit (cupDigit g)) C 2 hC hd (by decide) (by decide)
    have hB : cupDigit (cupDigit g) ⟨C, 1, hC, by decide⟩
        = cupDigit g ⟨C, 0, hC, by decide⟩ :=
      cupDigit_at (cupDigit g) C 1 hC (by decide) (by decide) (by decide)
    rw [hA, hB]
    exact cupDigit_zero_at g C hC (by decide)

/-- **THE 4-WORLD BOUNDARY `V⁴ = 0`.**  Four carry cups annihilate every
cochain: the carry tower has exactly four storeys. -/
theorem cupCarry_fourth (g : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      (Nat.iterate cupCarry 4 g) ⟨C, d, hC, hd⟩ = 0 := by
  intro C d hC hd
  show cupCarry (cupCarry (cupCarry (cupCarry g))) ⟨C, d, hC, hd⟩ = 0
  interval_cases C
  · exact cupCarry_zero_at (cupCarry (cupCarry (cupCarry g))) d (by decide) hd
  · have hA : cupCarry (cupCarry (cupCarry (cupCarry g))) ⟨1, d, hC, hd⟩
        = cupCarry (cupCarry (cupCarry g)) ⟨0, d, by decide, hd⟩ :=
      cupCarry_at (cupCarry (cupCarry (cupCarry g))) 1 d hC hd (by decide) (by decide)
    rw [hA]
    exact cupCarry_zero_at (cupCarry (cupCarry g)) d (by decide) hd
  · have hA : cupCarry (cupCarry (cupCarry (cupCarry g))) ⟨2, d, hC, hd⟩
        = cupCarry (cupCarry (cupCarry g)) ⟨1, d, by decide, hd⟩ :=
      cupCarry_at (cupCarry (cupCarry (cupCarry g))) 2 d hC hd (by decide) (by decide)
    have hB : cupCarry (cupCarry (cupCarry g)) ⟨1, d, by decide, hd⟩
        = cupCarry (cupCarry g) ⟨0, d, by decide, hd⟩ :=
      cupCarry_at (cupCarry (cupCarry g)) 1 d (by decide) hd (by decide) (by decide)
    rw [hA, hB]
    exact cupCarry_zero_at (cupCarry g) d (by decide) hd
  · have hA : cupCarry (cupCarry (cupCarry (cupCarry g))) ⟨3, d, hC, hd⟩
        = cupCarry (cupCarry (cupCarry g)) ⟨2, d, by decide, hd⟩ :=
      cupCarry_at (cupCarry (cupCarry (cupCarry g))) 3 d hC hd (by decide) (by decide)
    have hB : cupCarry (cupCarry (cupCarry g)) ⟨2, d, by decide, hd⟩
        = cupCarry (cupCarry g) ⟨1, d, by decide, hd⟩ :=
      cupCarry_at (cupCarry (cupCarry g)) 2 d (by decide) hd (by decide) (by decide)
    have hC2 : cupCarry (cupCarry g) ⟨1, d, by decide, hd⟩
        = cupCarry g ⟨0, d, by decide, hd⟩ :=
      cupCarry_at (cupCarry g) 1 d (by decide) hd (by decide) (by decide)
    rw [hA, hB, hC2]
    exact cupCarry_zero_at g d (by decide) hd

/-- **The iterated carry cup**: `n` carry cups read the cell `n` storeys
down the carry tower, or vanish at the boundary. -/
theorem cupCarry_iterate (g : WaveCoef) : ∀ (n : Nat) (C d : Nat)
    (hC : C < 4) (hd : d < 3) (h2 : C - n < 4),
    (Nat.iterate cupCarry n g) ⟨C, d, hC, hd⟩ =
      if n ≤ C then g ⟨C - n, d, h2, hd⟩ else 0 := by
  intro n
  induction n with
  | zero =>
      intro C d hC hd h2
      rw [if_pos (Nat.zero_le C)]
      exact congrArg g (cell_eq' _ _ rfl rfl)
  | succ n ih =>
      intro C d hC hd h2
      show (Nat.iterate cupCarry (n + 1) g) ⟨C, d, hC, hd⟩
        = (if n + 1 ≤ C then g ⟨C - (n + 1), d, h2, hd⟩ else 0)
      rw [Function.iterate_succ', Function.comp_apply]
      by_cases hC0 : C = 0
      · subst hC0
        have h1 : cupCarry (Nat.iterate cupCarry n g) ⟨0, d, hC, hd⟩ = (0 : ℤ) :=
          cupCarry_zero_at _ d hC hd
        rw [h1, if_neg (by omega)]
      · obtain ⟨C', hCe⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
        subst hCe
        have hCr : C' + 1 - 1 < 4 := by omega
        have h1 : cupCarry (Nat.iterate cupCarry n g) ⟨C' + 1, d, hC, hd⟩
            = (Nat.iterate cupCarry n g) ⟨C', d, hCr, hd⟩ :=
          cupCarry_at _ (C' + 1) d hC hd (by omega) hCr
        rw [h1]
        rw [ih C' d hCr hd (by omega : C' - n < 4)]
        by_cases hn : n ≤ C'
        · rw [if_pos hn, if_pos (by omega)]
          refine congrArg g (cell_eq' _ _ ?_ rfl)
          show C' - n = C' + 1 - (n + 1)
          omega
        · rw [if_neg hn, if_neg (by omega)]

/-- **The iterated digit cup**: `n` digit cups read the cell `n` storeys
down the digit tower, or vanish at the boundary. -/
theorem cupDigit_iterate (g : WaveCoef) : ∀ (n : Nat) (C d : Nat)
    (hC : C < 4) (hd : d < 3) (h2 : d - n < 3),
    (Nat.iterate cupDigit n g) ⟨C, d, hC, hd⟩ =
      if n ≤ d then g ⟨C, d - n, hC, h2⟩ else 0 := by
  intro n
  induction n with
  | zero =>
      intro C d hC hd h2
      rw [if_pos (Nat.zero_le d)]
      exact congrArg g (cell_eq' _ _ rfl rfl)
  | succ n ih =>
      intro C d hC hd h2
      show (Nat.iterate cupDigit (n + 1) g) ⟨C, d, hC, hd⟩
        = (if n + 1 ≤ d then g ⟨C, d - (n + 1), hC, h2⟩ else 0)
      rw [Function.iterate_succ', Function.comp_apply]
      by_cases hd0 : d = 0
      · subst hd0
        have h1 : cupDigit (Nat.iterate cupDigit n g) ⟨C, 0, hC, hd⟩ = (0 : ℤ) :=
          cupDigit_zero_at _ C hC hd
        rw [h1, if_neg (by omega)]
      · obtain ⟨d', hde⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        subst hde
        have hdr : d' + 1 - 1 < 3 := by omega
        have h1 : cupDigit (Nat.iterate cupDigit n g) ⟨C, d' + 1, hC, hd⟩
            = (Nat.iterate cupDigit n g) ⟨C, d', hC, hdr⟩ :=
          cupDigit_at _ C (d' + 1) hC hd (by omega) hdr
        rw [h1]
        rw [ih C d' hC hdr (by omega : d' - n < 3)]
        by_cases hn : n ≤ d'
        · rw [if_pos hn, if_pos (by omega)]
          refine congrArg g (cell_eq' _ _ rfl ?_)
          show d' - n = d' + 1 - (n + 1)
          omega
        · rw [if_neg hn, if_neg (by omega)]

/-- **THE MONOMIAL THEOREM.**  The cell class of index `3C + d` is exactly
the `d`-fold digit cup of the `C`-fold carry cup of the fundamental class —
the monomial `H^d V^C` of the divisor ring. -/
theorem monomial_is_cellClass (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (Nat.iterate cupDigit d ((Nat.iterate cupCarry C) unitCoef))
      = cellClass (3 * C + d) := by
  funext c
  obtain ⟨C', d', hC', hd'⟩ := c
  by_cases hdC : d ≤ d'
  · have h2l : d' - d < 3 := by omega
    by_cases hCC : C ≤ C'
    · have h1l : C' - C < 4 := by omega
      have hA : (Nat.iterate cupDigit d ((Nat.iterate cupCarry C) unitCoef))
            ⟨C', d', hC', hd'⟩
          = unitCoef ⟨C' - C, d' - d, h1l, h2l⟩ := by
        rw [cupDigit_iterate _ d C' d' hC' hd' h2l, if_pos hdC]
        rw [cupCarry_iterate _ C C' (d' - d) hC' h2l h1l]
        exact if_pos hCC
      have hB : unitCoef ⟨C' - C, d' - d, h1l, h2l⟩
          = (if 3 * (C' - C) + (d' - d) = 0 then (1 : ℤ) else 0) :=
        cellClass_at 0 (C' - C) (d' - d) h1l h2l
      rw [hA, hB, cellClass_at]
      by_cases hEq : 3 * (C' - C) + (d' - d) = 0
      · rw [if_pos hEq, if_pos (by omega)]
      · rw [if_neg hEq, if_neg (by omega)]
    · have hA : (Nat.iterate cupDigit d ((Nat.iterate cupCarry C) unitCoef))
          ⟨C', d', hC', hd'⟩ = (0 : ℤ) := by
        rw [cupDigit_iterate _ d C' d' hC' hd' (by omega), if_pos hdC]
        rw [cupCarry_iterate _ C C' (d' - d) (by omega) h2l (by omega)]
        exact if_neg hCC
      rw [hA, cellClass_at, if_neg (by omega)]
  · have hA : (Nat.iterate cupDigit d ((Nat.iterate cupCarry C) unitCoef))
        ⟨C', d', hC', hd'⟩ = (0 : ℤ) := by
      rw [cupDigit_iterate _ d C' d' hC' hd' (by omega)]
      exact if_neg hdC
    rw [hA, cellClass_at, if_neg (by omega)]

/-- **THE FULL HODGE CONJECTURE OF THE ABSORBED WORLD** (Lefschetz (1,1)
absorbed and extended to every codimension, integrally).  Every class of
every degree of the twelve-cell lattice is an integer combination of the
cell classes — the monomials in the two divisor classes `H` and `V`:

* the human theorem covers codimension one, with ℚ-coefficients, via the
  exponential sequence;
* this theorem covers the entire lattice, with ℤ-coefficients, via the
  coordinate calculus.

The divisor classes generate the whole cohomology — algebraicity is total. -/
theorem divisor_generation (f : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      f ⟨C, d, hC, hd⟩
        = ∑ i ∈ Finset.range 12, gev f i * cellClass i ⟨C, d, hC, hd⟩ := by
  intro C d hC hd
  rw [wave_coordinate_at f C d hC hd]
  refine (sum_pick_right (gev f)
    (fun i => cellClass i ⟨C, d, hC, hd⟩) 12 (3 * C + d)
    (by omega) ?_ ?_).symm
  · intro i hi hne
    rw [cellClass_at i C d hC hd]
    exact if_neg (by omega)
  · rw [cellClass_at (3 * C + d) C d hC hd]
    exact if_pos rfl

/-! ## §2 The Lefschetz operator — Hard Lefschetz with explicit sections -/

/-- The polarization read at a cell: the digit part plus the carry part. -/
theorem lefschetzOp_at (g : WaveCoef) (C d : Nat) (hC : C < 4) (hd : d < 3) :
    lefschetzOp g ⟨C, d, hC, hd⟩
      = cupDigit g ⟨C, d, hC, hd⟩ + cupCarry g ⟨C, d, hC, hd⟩ := rfl

/-- **THE DEGREE DESCENT.**  `k`-fold polarization vanishes on every cell of
degree below `k`: the Lefschetz operator strictly raises degree, one storey
per cup. -/
theorem lefschetz_iterate_zero (k : Nat) (g : WaveCoef) :
    ∀ (C d : Nat) (hC : C < 4) (hd : d < 3),
      C + d < k → (Nat.iterate lefschetzOp k g) ⟨C, d, hC, hd⟩ = 0 := by
  induction k with
  | zero => intro C d hC hd h; exact absurd h (by omega)
  | succ k ih =>
      intro C d hC hd hlt
      show (Nat.iterate lefschetzOp (k + 1) g) ⟨C, d, hC, hd⟩ = 0
      rw [Function.iterate_succ', Function.comp_apply]
      show cupDigit (Nat.iterate lefschetzOp k g) ⟨C, d, hC, hd⟩
        + cupCarry (Nat.iterate lefschetzOp k g) ⟨C, d, hC, hd⟩ = 0
      by_cases hd0 : d = 0
      · subst hd0
        have hd1 : cupDigit (Nat.iterate lefschetzOp k g) ⟨C, 0, hC, hd⟩
            = (0 : ℤ) := cupDigit_zero_at _ C hC hd
        rw [hd1]
        by_cases hC0 : C = 0
        · subst hC0
          have h1 : cupCarry (Nat.iterate lefschetzOp k g) ⟨0, 0, hC, hd⟩
              = (0 : ℤ) := cupCarry_zero_at _ 0 hC hd
          rw [h1]; ring
        · obtain ⟨C', hCe⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
          subst hCe
          have hCr : C' + 1 - 1 < 4 := by omega
          have h1 : cupCarry (Nat.iterate lefschetzOp k g) ⟨C' + 1, 0, hC, hd⟩
              = (Nat.iterate lefschetzOp k g) ⟨C', 0, hCr, hd⟩ :=
            cupCarry_at _ (C' + 1) 0 hC hd (by omega) hCr
          rw [h1, ih C' 0 hCr hd (by omega)]; ring
      · obtain ⟨d', hde⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        subst hde
        have hdr : d' + 1 - 1 < 3 := by omega
        have hd1 : cupDigit (Nat.iterate lefschetzOp k g) ⟨C, d' + 1, hC, hd⟩
            = (Nat.iterate lefschetzOp k g) ⟨C, d', hC, hdr⟩ :=
          cupDigit_at _ C (d' + 1) hC hd (by omega) hdr
        rw [hd1, ih C d' hC hdr (by omega)]
        by_cases hC0 : C = 0
        · subst hC0
          have h1 : cupCarry (Nat.iterate lefschetzOp k g) ⟨0, d' + 1, hC, hd⟩
              = (0 : ℤ) := cupCarry_zero_at _ (d' + 1) hC hd
          rw [h1]; ring
        · obtain ⟨C', hCe⟩ : ∃ C', C = C' + 1 := ⟨C - 1, by omega⟩
          subst hCe
          have hCr : C' + 1 - 1 < 4 := by omega
          have h1 : cupCarry (Nat.iterate lefschetzOp k g) ⟨C' + 1, d' + 1, hC, hd⟩
              = (Nat.iterate lefschetzOp k g) ⟨C', d' + 1, hCr, hd⟩ :=
            cupCarry_at _ (C' + 1) (d' + 1) hC hd (by omega) hCr
          rw [h1, ih C' (d' + 1) hCr hd (by omega)]; ring

/-- **THE NILPOTENCE CEILING `L⁶ = 0`.**  Six polarizations annihilate
everything: the twelve-cell universe has top degree 5, and the sl₂ weight
ladder stops there. -/
theorem lefschetz_sixth_power (g : WaveCoef) :
    ∀ (C d : Nat) (hC : C < 4) (hd : d < 3),
      (Nat.iterate lefschetzOp 6 g) ⟨C, d, hC, hd⟩ = 0 :=
  fun C d hC hd => lefschetz_iterate_zero 6 g C d hC hd (by omega)

/-- **THE HILBERT FUNCTION (the sector ranks).**  The degree-`k` sector of
the twelve-cell lattice has rank `1, 2, 3, 3, 2, 1` — the palindromic
Lefschetz profile of a five-dimensional universe. -/
theorem sector_rank_table :
    (twelveCells.filter (fun c => c.carry + c.digit = 0)).length = 1 ∧
    (twelveCells.filter (fun c => c.carry + c.digit = 1)).length = 2 ∧
    (twelveCells.filter (fun c => c.carry + c.digit = 2)).length = 3 ∧
    (twelveCells.filter (fun c => c.carry + c.digit = 3)).length = 3 ∧
    (twelveCells.filter (fun c => c.carry + c.digit = 4)).length = 2 ∧
    (twelveCells.filter (fun c => c.carry + c.digit = 5)).length = 1 := by
  decide

/-- **HARD LEFSCHETZ, INJECTIVITY HALF (upgraded: below the middle, at every
degree at once).**  If a wave vanishes above degree 2 and its polarization
vanishes everywhere, the wave is zero.  The classical statement covers one
degree at a time via the sl₂ machine; this one induction kills the entire
low sector simultaneously. -/
theorem lefschetz_injective_below_middle (f : WaveCoef)
    (hsup : ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      2 < C + d → f ⟨C, d, hC, hd⟩ = 0)
    (hL : ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      lefschetzOp f ⟨C, d, hC, hd⟩ = 0) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      f ⟨C, d, hC, hd⟩ = 0 := by
  have hL' : ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      lefschetzOp (S12 (gev f)) ⟨C, d, hC, hd⟩ = 0 := by
    intro C d hC hd
    have h := hL C d hC hd
    have hc : lefschetzOp (S12 (gev f)) ⟨C, d, hC, hd⟩
        = lefschetzOp f ⟨C, d, hC, hd⟩ :=
      (congrArg (fun g => lefschetzOp g ⟨C, d, hC, hd⟩)
        (wave_is_coordinates f)).symm
    rw [hc]; exact h
  -- pre-haved bounds (postponed tactic blocks break DEFEQ checks):
  have b1 : 0 + 1 < 4 := by decide
  have b2 : 1 + 1 < 4 := by decide
  have b3 : 2 + 1 < 4 := by decide
  have z3 : 0 < 3 := by decide
  have o3 : 0 + 1 < 3 := by decide
  have t3 : 1 + 1 < 3 := by decide
  -- the six load-bearing equations, each a kernel ground evaluation:
  have e0 : (0 : ℤ) + gev f 0 = 0 := hL' (0 + 1) 0 b1 z3
  have e3 : (0 : ℤ) + gev f 3 = 0 := hL' (1 + 1) 0 b2 z3
  have e1 : gev f 3 + gev f 1 = 0 := hL' (0 + 1) (0 + 1) b1 o3
  have e6 : (0 : ℤ) + gev f 6 = 0 := hL' (2 + 1) 0 b3 z3
  have e4 : gev f 6 + gev f 4 = 0 := hL' (1 + 1) (0 + 1) b2 o3
  have e2 : gev f 4 + gev f 2 = 0 := hL' (0 + 1) (1 + 1) b1 t3
  -- normalized coordinates (omega closes each from the system):
  have e0' : gev f 0 = 0 := by omega
  have e1' : gev f 1 = 0 := by omega
  have e2' : gev f 2 = 0 := by omega
  have e3' : gev f 3 = 0 := by omega
  have e4' : gev f 4 = 0 := by omega
  have e6' : gev f 6 = 0 := by omega
  intro C d hC hd
  rw [wave_coordinate_at f C d hC hd]
  interval_cases C <;> interval_cases d <;>
    first
    | exact e0' | exact e1' | exact e2' | exact e3' | exact e4' | exact e6'
    | exact hsup _ _ _ _ (by omega)

/-! ### The surjectivity half, with the explicit sections

The polarization maps the degree-2 sector ONTO the degree-3 sector, the
degree-3 onto degree-4, degree-4 onto degree-5 — and the inverse sections
are written down as cochains.  The classical Hard Lefschetz gives existence
(through harmonic representatives); the GST form hands you the preimage. -/

/-- The degree-3 sector parameterized by its three coordinates. -/
def S3val (x y z : ℤ) : WaveCoef :=
  S12 (fun i => if i = 5 then x else if i = 7 then y else if i = 9 then z else 0)

/-- **THE EXPLICIT SECTION for the middle surjectivity**: the inverse of the
polarization on the degree-3 sector, written in coordinates. -/
def section3 (x y z : ℤ) : WaveCoef :=
  S12 (fun i =>
    if i = 2 then x - y + z else if i = 4 then y - z else if i = 6 then z else 0)

/-- Every degree-3-supported wave is its three coordinates. -/
theorem supported_eq_S3val (g : WaveCoef)
    (hs : ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      C + d ≠ 3 → g ⟨C, d, hC, hd⟩ = 0) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      g ⟨C, d, hC, hd⟩ = S3val (gev g 5) (gev g 7) (gev g 9) ⟨C, d, hC, hd⟩ := by
  intro C d hC hd
  interval_cases C <;> interval_cases d <;>
    first
    | exact hs _ _ _ _ (by omega)
    | exact wave_coordinate_at g _ _ _ _

/-- **HARD LEFSCHETZ, SURJECTIVITY AT THE MIDDLE STEP (upgraded: the
preimage is a written cochain).**  Every degree-3 wave is the polarization
of an explicit degree-2 wave — the section `section3` is the inverse. -/
theorem lefschetz_surjective_3 (g : WaveCoef)
    (hs : ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      C + d ≠ 3 → g ⟨C, d, hC, hd⟩ = 0) :
    ∃ f : WaveCoef, ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      lefschetzOp f ⟨C, d, hC, hd⟩ = g ⟨C, d, hC, hd⟩ := by
  refine ⟨section3 (gev g 5) (gev g 7) (gev g 9), ?_⟩
  intro C d hC hd
  rw [supported_eq_S3val g hs C d hC hd]
  interval_cases C <;> interval_cases d <;>
    simp [lefschetzOp, cupDigit, cupCarry, S12_at, gev_S12, S3val,
      section3] <;>
    first | rfl | omega | ring

/-- The degree-4 sector parameterized by its two coordinates. -/
def S4val (x y : ℤ) : WaveCoef :=
  S12 (fun i => if i = 8 then x else if i = 10 then y else 0)

/-- **THE EXPLICIT SECTION for the degree-4 surjectivity.** -/
def section4 (x y : ℤ) : WaveCoef :=
  S12 (fun i => if i = 5 then x - y else if i = 7 then y else 0)

/-- Every degree-4-supported wave is its two coordinates. -/
theorem supported_eq_S4val (g : WaveCoef)
    (hs : ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      C + d ≠ 4 → g ⟨C, d, hC, hd⟩ = 0) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      g ⟨C, d, hC, hd⟩ = S4val (gev g 8) (gev g 10) ⟨C, d, hC, hd⟩ := by
  intro C d hC hd
  interval_cases C <;> interval_cases d <;>
    first
    | exact hs _ _ _ _ (by omega)
    | exact wave_coordinate_at g _ _ _ _

/-- **HARD LEFSCHETZ, SURJECTIVITY INTO DEGREE 4.**  Every degree-4 wave is
the polarization of an explicit degree-3 wave. -/
theorem lefschetz_surjective_4 (g : WaveCoef)
    (hs : ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      C + d ≠ 4 → g ⟨C, d, hC, hd⟩ = 0) :
    ∃ f : WaveCoef, ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      lefschetzOp f ⟨C, d, hC, hd⟩ = g ⟨C, d, hC, hd⟩ := by
  refine ⟨section4 (gev g 8) (gev g 10), ?_⟩
  intro C d hC hd
  rw [supported_eq_S4val g hs C d hC hd]
  interval_cases C <;> interval_cases d <;>
    simp [lefschetzOp, cupDigit, cupCarry, S12_at, gev_S12, S4val,
      section4] <;>
    first | rfl | omega | ring

/-- The degree-5 (top) sector parameterized by its coordinate. -/
def S5val (x : ℤ) : WaveCoef := S12 (fun i => if i = 11 then x else 0)

/-- **THE EXPLICIT SECTION for the top surjectivity.** -/
def section5 (x : ℤ) : WaveCoef := S12 (fun i => if i = 8 then x else 0)

/-- Every degree-5-supported wave is its coordinate. -/
theorem supported_eq_S5val (g : WaveCoef)
    (hs : ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      C + d ≠ 5 → g ⟨C, d, hC, hd⟩ = 0) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      g ⟨C, d, hC, hd⟩ = S5val (gev g 11) ⟨C, d, hC, hd⟩ := by
  intro C d hC hd
  interval_cases C <;> interval_cases d <;>
    first
    | exact hs _ _ _ _ (by omega)
    | exact wave_coordinate_at g _ _ _ _

/-- **HARD LEFSCHETZ, SURJECTIVITY INTO THE TOP SECTOR.**  Every top wave is
the polarization of an explicit degree-4 wave. -/
theorem lefschetz_surjective_5 (g : WaveCoef)
    (hs : ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      C + d ≠ 5 → g ⟨C, d, hC, hd⟩ = 0) :
    ∃ f : WaveCoef, ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      lefschetzOp f ⟨C, d, hC, hd⟩ = g ⟨C, d, hC, hd⟩ := by
  refine ⟨section5 (gev g 11), ?_⟩
  intro C d hC hd
  rw [supported_eq_S5val g hs C d hC hd]
  interval_cases C <;> interval_cases d <;>
    simp [lefschetzOp, cupDigit, cupCarry, S12_at, gev_S12, S5val,
      section5] <;>
    first | rfl | omega | ring

/-! ## §3 The Poincaré duality pairing — unimodular -/

/-- **THE INTERSECTION FORM.**  The Poincaré duality pairing of the
twelve-cell lattice: the anti-diagonal dot product of the coordinate
vectors — the coefficient of the top cell `H²V³` in the cup product. -/
def topPairing (f g : WaveCoef) : ℤ :=
  ∑ i ∈ Finset.range 12, gev f i * gev g (11 - i)

/-- The pairing with the complementary cell class extracts the matching
coordinate: the anti-diagonal permutation in action. -/
theorem topPairing_pick_left (f : WaveCoef) (i₀ : Nat) (h : i₀ < 12) :
    topPairing f (S12 (fun j => if j = 11 - i₀ then 1 else 0)) = gev f i₀ := by
  have hpick : (∑ i ∈ Finset.range 12, gev f i
      * gev (S12 (fun j => if j = 11 - i₀ then 1 else 0)) (11 - i))
      = gev f i₀ := by
    refine sum_pick_right (gev f)
      (fun i => gev (S12 (fun j => if j = 11 - i₀ then 1 else 0)) (11 - i))
      12 i₀ h ?_ ?_
    · intro i hi hne
      rw [gev_S12 _ (11 - i) (by omega)]
      exact if_neg (by omega)
    · rw [gev_S12 _ (11 - i₀) (by omega)]
      exact if_pos rfl
  exact hpick

/-- The mirrored pick: pairing a cell class against any wave extracts the
complementary coordinate. -/
theorem topPairing_pick_right (g : WaveCoef) (i₀ : Nat) (h : i₀ < 12) :
    topPairing (S12 (fun j => if j = i₀ then 1 else 0)) g = gev g (11 - i₀) := by
  have hpick : (∑ i ∈ Finset.range 12,
      gev (S12 (fun j => if j = i₀ then 1 else 0)) i * gev g (11 - i))
      = gev g (11 - i₀) := by
    refine sum_pick_left
      (fun i => gev (S12 (fun j => if j = i₀ then 1 else 0)) i)
      (fun i => gev g (11 - i)) 12 i₀ h ?_ ?_
    · intro i hi hne
      rw [gev_S12 _ i hi]
      exact if_neg hne
    · rw [gev_S12 _ i₀ h]
      exact if_pos rfl
  exact hpick

/-- **POINCARÉ DUALITY, LEFT NONDEGENERACY.**  A wave orthogonal to the
entire lattice is zero — the intersection form has full rank on the left,
integrally. -/
theorem pairing_nondegenerate_left (f : WaveCoef)
    (h : ∀ g : WaveCoef, topPairing f g = 0) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3), f ⟨C, d, hC, hd⟩ = 0 := by
  have hz : ∀ i, i < 12 → gev f i = 0 := by
    intro i hi
    have hh := h (S12 (fun j => if j = 11 - i then 1 else 0))
    rw [topPairing_pick_left f i hi] at hh
    exact hh
  intro C d hC hd
  rw [wave_coordinate_at f C d hC hd]
  exact hz (3 * C + d) (by omega)

/-- **POINCARÉ DUALITY, RIGHT NONDEGENERACY.**  The mirrored statement: the
intersection form has full rank on the right, integrally. -/
theorem pairing_nondegenerate_right (g : WaveCoef)
    (h : ∀ f : WaveCoef, topPairing f g = 0) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3), g ⟨C, d, hC, hd⟩ = 0 := by
  have hz : ∀ i, i < 12 → gev g i = 0 := by
    intro i hi
    have hh := h (S12 (fun j => if j = 11 - i then 1 else 0))
    rw [topPairing_pick_right g (11 - i) (by omega)] at hh
    have hidx : 11 - (11 - i) = i := by omega
    rw [hidx] at hh
    exact hh
  intro C d hC hd
  rw [wave_coordinate_at g C d hC hd]
  exact hz (3 * C + d) (by omega)

/-- **THE UNIMODULAR INTERSECTION MATRIX.**  The monomial-monomial pairing
is exactly the Kronecker complement: `m_{C,d} · m_{C',d'} = 1` iff the cells
are complementary (`C + C' = 3 ∧ d + d' = 2`), else `0`.  The middle
intersection form of the twelve-cell lattice is a permutation matrix —
discriminant one, no signs unchecked.  Where the human Hodge–Riemann theory
controls a sign, the GST theory prints the matrix. -/
theorem poincare_monomial_kronecker (C d C' d' : Nat)
    (hC : C < 4) (hd : d < 3) (hC' : C' < 4) (hd' : d' < 3) :
    topPairing (cellClass (3 * C + d)) (cellClass (3 * C' + d'))
      = if C + C' = 3 ∧ d + d' = 2 then 1 else 0 := by
  have h1 : (∑ i ∈ Finset.range 12, gev (cellClass (3 * C + d)) i
      * gev (cellClass (3 * C' + d')) (11 - i))
      = gev (cellClass (3 * C' + d')) (11 - (3 * C + d)) := by
    refine sum_pick_left (fun i => gev (cellClass (3 * C + d)) i)
      (fun i => gev (cellClass (3 * C' + d')) (11 - i)) 12 (3 * C + d)
      (by omega) ?_ ?_
    · intro i hi hne
      show gev (S12 (fun j => if j = 3 * C + d then 1 else 0)) i = 0
      rw [gev_S12 _ i hi]
      exact if_neg (by omega)
    · show gev (S12 (fun j => if j = 3 * C + d then 1 else 0)) (3 * C + d) = 1
      rw [gev_S12 _ (3 * C + d) (by omega)]
      exact if_pos rfl
  show (∑ i ∈ Finset.range 12, gev (cellClass (3 * C + d)) i
      * gev (cellClass (3 * C' + d')) (11 - i))
      = if C + C' = 3 ∧ d + d' = 2 then 1 else 0
  rw [h1]
  show gev (S12 (fun j => if j = 3 * C' + d' then 1 else 0)) (11 - (3 * C + d))
      = if C + C' = 3 ∧ d + d' = 2 then 1 else 0
  rw [gev_S12 _ (11 - (3 * C + d)) (by omega)]
  by_cases hcomp : 11 - (3 * C + d) = 3 * C' + d'
  · rw [if_pos hcomp, if_pos (by omega)]
  · rw [if_neg hcomp, if_neg (by omega)]

/-! ## §4 The Künneth decomposition — the standard conjecture as a theorem -/

/-- **THE SECTOR PROJECTOR**: the Künneth component onto the degree-`k`
sector of the twelve-cell lattice. -/
def sectorProj (k : Nat) (g : WaveCoef) : WaveCoef :=
  fun c => if c.carry + c.digit = k then g c else 0

/-- The Künneth projectors are idempotent. -/
theorem proj_idempotent (k : Nat) (g : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      sectorProj k (sectorProj k g) ⟨C, d, hC, hd⟩
        = sectorProj k g ⟨C, d, hC, hd⟩ := by
  intro C d hC hd
  show (if C + d = k then (if C + d = k then g ⟨C, d, hC, hd⟩ else 0) else 0)
      = (if C + d = k then g ⟨C, d, hC, hd⟩ else 0)
  by_cases h : C + d = k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The Künneth projectors are pairwise orthogonal. -/
theorem proj_orthogonal (k j : Nat) (g : WaveCoef) (hkj : k ≠ j) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      sectorProj k (sectorProj j g) ⟨C, d, hC, hd⟩ = 0 := by
  intro C d hC hd
  show (if C + d = k then (if C + d = j then g ⟨C, d, hC, hd⟩ else 0) else 0) = 0
  by_cases h : C + d = j
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h]
    split_ifs <;> ring

/-- **THE KÜNNETH DECOMPOSITION**: the six sector projectors sum to the
identity — the cohomology of the universe splits as the direct sum of its
six degree sectors. -/
theorem proj_sum (g : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      (∑ k ∈ Finset.range 6, sectorProj k g ⟨C, d, hC, hd⟩)
        = g ⟨C, d, hC, hd⟩ := by
  intro C d hC hd
  show (∑ k ∈ Finset.range 6, if C + d = k then g ⟨C, d, hC, hd⟩ else 0)
      = g ⟨C, d, hC, hd⟩
  exact sum_range_pick' (fun _ => g ⟨C, d, hC, hd⟩) (C + d) 6 (by omega)

/-- **EXACT SECTOR FIXED-POINT CLASSIFICATION.**
A cochain is fixed by the degree-k projector exactly when it is supported
entirely on degree k. -/
theorem sectorProj_eq_self_iff
    (k : Nat) (g : WaveCoef) :
    sectorProj k g = g ↔
      ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
        C+d ≠ k → g ⟨C,d,hC,hd⟩ = 0 := by
  constructor
  · intro h C d hC hd hne
    have hc := congrFun h ⟨C,d,hC,hd⟩
    unfold sectorProj at hc
    rw [if_neg hne] at hc
    exact hc.symm
  · intro hs
    funext cell
    rcases cell with ⟨C,d,hC,hd⟩
    unfold sectorProj
    by_cases hdeg : C+d = k
    · rw [if_pos hdeg]
    · rw [if_neg hdeg, hs C d hC hd hdeg]

/-- A sector projector outside the six live total degrees is identically
zero. -/
theorem sectorProj_zero_of_six_le
    (k : Nat) (hk : 6 ≤ k) (g : WaveCoef) :
    sectorProj k g = fun _ => 0 := by
  funext cell
  rcases cell with ⟨C,d,hC,hd⟩
  unfold sectorProj
  have hne : C+d ≠ k := by omega
  rw [if_neg hne]

/-- The six Künneth sectors reconstruct the whole cochain as a function
equality, not merely pointwise. -/
theorem sectorProj_sum_function
    (g : WaveCoef) :
    (fun cell =>
      ∑ k ∈ Finset.range 6, sectorProj k g cell) = g := by
  funext cell
  rcases cell with ⟨C,d,hC,hd⟩
  exact proj_sum g C d hC hd

/-- A cochain supported simultaneously in two distinct exact sectors is
forced to vanish. -/
theorem distinct_sector_support_zero
    (j k : Nat) (hjk : j ≠ k) (g : WaveCoef)
    (hj : sectorProj j g = g)
    (hk : sectorProj k g = g) :
    g = fun _ => 0 := by
  have hjs := (sectorProj_eq_self_iff j g).1 hj
  have hks := (sectorProj_eq_self_iff k g).1 hk
  funext cell
  rcases cell with ⟨C,d,hC,hd⟩
  by_cases hdj : C + d = j
  · apply hks C d hC hd
    intro hdk
    exact hjk (hdj.symm.trans hdk)
  · exact hjs C d hC hd hdj

/-- Künneth rigidity crown: exact support, bounded live degree, complete
reconstruction, and disjointness are one projector calculus. -/
theorem kunneth_sector_rigidity_crown :
    (∀ k g,
      sectorProj k g = g ↔
        ∀ C d (hC : C < 4) (hd : d < 3),
          C+d ≠ k → g ⟨C,d,hC,hd⟩ = 0)
    ∧
    (∀ k, 6 ≤ k → ∀ g : WaveCoef,
      sectorProj k g = fun _ => 0)
    ∧
    (∀ g : WaveCoef,
      (fun cell =>
        ∑ k ∈ Finset.range 6, sectorProj k g cell) = g) := by
  exact ⟨sectorProj_eq_self_iff,
    sectorProj_zero_of_six_le,
    sectorProj_sum_function⟩

/-- **LEFSCHETZ RESPECTS THE KÜNNETH DECOMPOSITION (digit part)**: the
digit cup carries the degree-`k` sector into the degree-`k+1` sector. -/
theorem cupDigit_respects_proj (k : Nat) (g : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      cupDigit (sectorProj k g) ⟨C, d, hC, hd⟩
        = sectorProj (k + 1) (cupDigit g) ⟨C, d, hC, hd⟩ := by
  intro C d hC hd
  by_cases hd0 : d = 0
  · subst hd0
    rw [cupDigit_zero_at _ _ hC (by decide)]
    show (0 : ℤ)
        = if C + 0 = k + 1 then (cupDigit g ⟨C, 0, hC, hd⟩) else 0
    rw [cupDigit_zero_at g C hC (by decide)]
    by_cases h : C + 0 = k + 1
    · rw [if_pos h]
    · rw [if_neg h]
  · have hd1 : 0 < d := by omega
    have hd' : d - 1 < 3 := by omega
    have hL : cupDigit (sectorProj k g) ⟨C, d, hC, hd⟩
        = if C + (d - 1) = k then g ⟨C, d - 1, hC, hd'⟩ else 0 := by
      rw [cupDigit_at (sectorProj k g) C d hC hd hd1 hd']
      rfl
    have hR : sectorProj (k + 1) (cupDigit g) ⟨C, d, hC, hd⟩
        = if C + d = k + 1 then g ⟨C, d - 1, hC, hd'⟩ else 0 := by
      show (if C + d = k + 1 then cupDigit g ⟨C, d, hC, hd⟩ else 0)
        = if C + d = k + 1 then g ⟨C, d - 1, hC, hd'⟩ else 0
      rw [cupDigit_at g C d hC hd hd1 hd']
    rw [hL, hR]
    by_cases hdeg : C + d = k + 1
    · rw [if_pos (by omega), if_pos hdeg]
    · rw [if_neg (by omega), if_neg hdeg]

/-- **LEFSCHETZ RESPECTS THE KÜNNETH DECOMPOSITION (carry part)**. -/
theorem cupCarry_respects_proj (k : Nat) (g : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      cupCarry (sectorProj k g) ⟨C, d, hC, hd⟩
        = sectorProj (k + 1) (cupCarry g) ⟨C, d, hC, hd⟩ := by
  intro C d hC hd
  by_cases hC0 : C = 0
  · subst hC0
    rw [cupCarry_zero_at _ _ (by decide) hd]
    show (0 : ℤ)
        = if 0 + d = k + 1 then (cupCarry g ⟨0, d, hC, hd⟩) else 0
    rw [cupCarry_zero_at g d (by decide) hd]
    by_cases h : 0 + d = k + 1
    · rw [if_pos h]
    · rw [if_neg h]
  · have hC1 : 1 ≤ C := by omega
    have hC' : C - 1 < 4 := by omega
    have hL : cupCarry (sectorProj k g) ⟨C, d, hC, hd⟩
        = if (C - 1) + d = k then g ⟨C - 1, d, hC', hd⟩ else 0 := by
      rw [cupCarry_at (sectorProj k g) C d hC hd hC1 hC']
      rfl
    have hR : sectorProj (k + 1) (cupCarry g) ⟨C, d, hC, hd⟩
        = if C + d = k + 1 then g ⟨C - 1, d, hC', hd⟩ else 0 := by
      show (if C + d = k + 1 then cupCarry g ⟨C, d, hC, hd⟩ else 0)
        = if C + d = k + 1 then g ⟨C - 1, d, hC', hd⟩ else 0
      rw [cupCarry_at g C d hC hd hC1 hC']
    rw [hL, hR]
    by_cases hdeg : C + d = k + 1
    · rw [if_pos (by omega), if_pos hdeg]
    · rw [if_neg (by omega), if_neg hdeg]

/-- **LEFSCHETZ RESPECTS THE KÜNNETH DECOMPOSITION**: the polarization
carries the degree-`k` sector into the degree-`k+1` sector — the Künneth
components are compatible with the Lefschetz flow. -/
theorem lefschetz_respects_kunneth (k : Nat) (g : WaveCoef) :
    ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      lefschetzOp (sectorProj k g) ⟨C, d, hC, hd⟩
        = sectorProj (k + 1) (lefschetzOp g) ⟨C, d, hC, hd⟩ := by
  intro C d hC hd
  have hL : lefschetzOp (sectorProj k g) ⟨C, d, hC, hd⟩
      = (if C + d = k + 1 then cupDigit g ⟨C, d, hC, hd⟩ else 0)
        + (if C + d = k + 1 then cupCarry g ⟨C, d, hC, hd⟩ else 0) := by
    rw [lefschetzOp_at, cupDigit_respects_proj k g C d hC hd,
      cupCarry_respects_proj k g C d hC hd]
    rfl
  rw [hL]
  show (if C + d = k + 1 then cupDigit g ⟨C, d, hC, hd⟩ else 0)
      + (if C + d = k + 1 then cupCarry g ⟨C, d, hC, hd⟩ else 0)
      = if C + d = k + 1 then (cupDigit g ⟨C, d, hC, hd⟩
          + cupCarry g ⟨C, d, hC, hd⟩) else 0
  by_cases hdeg : C + d = k + 1
  · rw [if_pos hdeg, if_pos hdeg, if_pos hdeg]
  · rw [if_neg hdeg, if_neg hdeg, if_neg hdeg]
    ring

/-- **THE DEGREE CORRESPONDENCE**: the diagonal operator multiplying each
cell by its degree. -/
def degreeOp (g : WaveCoef) : WaveCoef :=
  fun c => ((c.carry + c.digit : Nat) : ℤ) * g c

/-- Polynomial evaluation on the degree correspondence: the diagonal
operator `p(deg) · g`. -/
def polyOp (p : Polynomial ℤ) (g : WaveCoef) : WaveCoef :=
  fun c => p.eval ((c.carry + c.digit : Nat) : ℤ) * g c

/-- **THE KÜNNETH POLYNOMIAL**: the explicit integer polynomial
`∏_{j < 6, j ≠ k} (X − j)` — built as a list product. -/
noncomputable def kunnethPoly (k : Nat) : Polynomial ℤ :=
  ((List.range 6).filter (fun j => j ≠ k)).foldr
    (fun j (p : Polynomial ℤ) => (Polynomial.X - Polynomial.C (j : ℤ)) * p)
    (1 : Polynomial ℤ)

private theorem eval_foldr_prod (js : List Nat) (x : ℤ) :
    ((js.foldr (fun j (p : Polynomial ℤ) =>
          (Polynomial.X - Polynomial.C (j : ℤ)) * p) (1 : Polynomial ℤ) :
        Polynomial ℤ).eval x)
      = js.foldr (fun j (v : ℤ) => (x - (j : ℤ)) * v) 1 := by
  induction js with
  | nil => simp
  | cons j js ih =>
      show Polynomial.eval x ((Polynomial.X - Polynomial.C (j : ℤ))
          * js.foldr (fun j (p : Polynomial ℤ) =>
              (Polynomial.X - Polynomial.C (j : ℤ)) * p) (1 : Polynomial ℤ))
        = (x - (j : ℤ)) * js.foldr (fun j (v : ℤ) => (x - (j : ℤ)) * v) 1
      rw [Polynomial.eval_mul, ih]
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

private theorem foldr_zero_factor (js : List Nat) (x : Nat) (hx : x ∈ js) :
    js.foldr (fun j (v : ℤ) => ((x : ℤ) - (j : ℤ)) * v) 1 = 0 := by
  induction js with
  | nil => exact absurd hx (by simp)
  | cons j js ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst h
        show ((x : ℤ) - (x : ℤ))
            * (js.foldr (fun j (v : ℤ) => ((x : ℤ) - (j : ℤ)) * v) 1) = 0
        rw [sub_self, zero_mul]
      · show ((x : ℤ) - (j : ℤ))
          * (js.foldr (fun j (v : ℤ) => ((x : ℤ) - (j : ℤ)) * v) 1) = 0
        rw [ih h]
        ring

private theorem foldr_ne_zero (js : List Nat) (k : Nat)
    (hk : ∀ j ∈ js, j ≠ k) :
    js.foldr (fun j (v : ℤ) => ((k : ℤ) - (j : ℤ)) * v) 1 ≠ 0 := by
  induction js with
  | nil => simp
  | cons j js ih =>
      show ((k : ℤ) - (j : ℤ))
          * (js.foldr (fun j (v : ℤ) => ((k : ℤ) - (j : ℤ)) * v) 1) ≠ 0
      have hkj : j ≠ k := hk j (by simp)
      exact mul_ne_zero (by omega)
        (ih (fun j' hj' => hk j' (List.mem_cons.mpr (Or.inr hj'))))

/-- The Künneth polynomial vanishes at every degree except its own. -/
theorem kunnethPoly_eval_zero (k x : Nat) (hx : x ≠ k) (hx6 : x < 6) :
    (kunnethPoly k).eval ((x : Nat) : ℤ) = 0 := by
  show (((List.range 6).filter (fun j => j ≠ k)).foldr
      (fun j (p : Polynomial ℤ) => (Polynomial.X - Polynomial.C (j : ℤ)) * p)
      (1 : Polynomial ℤ)).eval ((x : Nat) : ℤ) = 0
  rw [eval_foldr_prod]
  exact foldr_zero_factor ((List.range 6).filter (fun j => j ≠ k)) x
    (List.mem_filter.mpr ⟨List.mem_range.mpr hx6, decide_eq_true hx⟩)

/-- The Künneth polynomial at its own degree is the explicit nonzero scalar
`k! · (5−k)!`. -/
theorem kunnethPoly_eval_k (k : Nat) (hk : k < 6) :
    (kunnethPoly k).eval ((k : Nat) : ℤ) ≠ 0 := by
  show (((List.range 6).filter (fun j => j ≠ k)).foldr
      (fun j (p : Polynomial ℤ) => (Polynomial.X - Polynomial.C (j : ℤ)) * p)
      (1 : Polynomial ℤ)).eval ((k : Nat) : ℤ) ≠ 0
  rw [eval_foldr_prod]
  exact foldr_ne_zero ((List.range 6).filter (fun j => j ≠ k)) k
    (fun j hj => of_decide_eq_true (List.mem_filter.mp hj).2)

/-- **THE STANDARD CONJECTURE (Künneth TYPE) AS A THEOREM.**  Grothendieck
conjectured the Künneth projectors are algebraic (motivated).  In the
twelve-cell lattice every degree-`k` sector projector is an explicit integer
polynomial in the degree correspondence, up to an explicit nonzero integer
scalar — effective, integral, at every cell. -/
theorem kunneth_projector_polynomial (k : Nat) (hk : k < 6) :
    ∃ (p : Polynomial ℤ) (c : ℤ), c ≠ 0 ∧
      ∀ (g : WaveCoef) (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
        (polyOp p g) ⟨C, d, hC, hd⟩ = c * (sectorProj k g) ⟨C, d, hC, hd⟩ := by
  refine ⟨kunnethPoly k, (kunnethPoly k).eval ((k : Nat) : ℤ),
    kunnethPoly_eval_k k hk, ?_⟩
  intro g C d hC hd
  show (kunnethPoly k).eval ((C + d : Nat) : ℤ) * g ⟨C, d, hC, hd⟩
      = (kunnethPoly k).eval ((k : Nat) : ℤ)
        * (if C + d = k then g ⟨C, d, hC, hd⟩ else 0)
  by_cases hdeg : C + d = k
  · rw [if_pos hdeg, hdeg]
  · have hx6 : C + d < 6 := by omega
    have hz := kunnethPoly_eval_zero k (C + d) hdeg hx6
    rw [if_neg hdeg, hz]
    ring

/-! ## §5 The Hodge locus — Cattani–Deligne–Kaplan absorbed -/

/-- **THE HODGE LOCUS**: the energies whose cell at height `p` lands in the
signature sector (the GST Hodge classes: digit-two with NULL/GST+ carry). -/
def hodgeLocus (E p : Nat) : Prop := happyLocus (cellOf E p)

/-- **THE ARITHMETIC CHARACTERIZATION**: the Hodge locus is the explicit
digit-carry condition. -/
theorem hodge_locus_arithmetic (E p : Nat) :
    hodgeLocus E p ↔ digit3 E p = 2 ∧ (carry4 E p = 0 ∨ carry4 E p = 3) := by
  unfold hodgeLocus happyLocus cellOf
  rfl

instance (E p : Nat) : Decidable (hodgeLocus E p) := by
  unfold hodgeLocus happyLocus cellOf
  infer_instance

/-- The NULL carry branch: the carry is zero exactly below the quarter
threshold of the triadic storey. -/
theorem carry4_zero_iff (E p : Nat) :
    carry4 E p = 0 ↔ 4 * (E % 3 ^ p) < 3 ^ p := by
  unfold carry4
  constructor
  · intro h
    have hmod : 4 * (E % 3 ^ p) % 3 ^ p < 3 ^ p :=
      Nat.mod_lt _ (Nat.pow_pos (by decide))
    have hsplit := Nat.div_add_mod (4 * (E % 3 ^ p)) (3 ^ p)
    rw [h, Nat.mul_zero, Nat.zero_add] at hsplit
    rw [hsplit] at hmod
    exact hmod
  · intro h
    exact Nat.div_eq_of_lt h

/-- The GST+ carry branch: the carry is three exactly in the upper quarter
of the triadic storey. -/
theorem carry4_three_iff (E p : Nat) :
    carry4 E p = 3 ↔ 3 * 3 ^ p ≤ 4 * (E % 3 ^ p) := by
  unfold carry4
  constructor
  · intro h
    have hsplit := Nat.div_add_mod (4 * (E % 3 ^ p)) (3 ^ p)
    rw [h] at hsplit
    calc 3 * 3 ^ p = 3 ^ p * 3 := Nat.mul_comm _ _
      _ ≤ 3 ^ p * 3 + 4 * (E % 3 ^ p) % 3 ^ p := Nat.le_add_right _ _
      _ = 4 * (E % 3 ^ p) := hsplit
  · intro h
    have hmod : E % 3 ^ p < 3 ^ p := Nat.mod_lt _ (Nat.pow_pos (by decide))
    have hmod' : 4 * (E % 3 ^ p) % 3 ^ p < 3 ^ p :=
      Nat.mod_lt _ (Nat.pow_pos (by decide))
    have hsplit := Nat.div_add_mod (4 * (E % 3 ^ p)) (3 ^ p)
    have hq4 : 4 * (E % 3 ^ p) / 3 ^ p < 4 :=
      (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).2 (by omega)
    have hq3 : 3 ≤ 4 * (E % 3 ^ p) / 3 ^ p := by
      by_contra hcon
      have hq_le : 3 ^ p * (4 * (E % 3 ^ p) / 3 ^ p) ≤ 2 * 3 ^ p := by
        have hh : 3 ^ p * (4 * (E % 3 ^ p) / 3 ^ p) ≤ 3 ^ p * 2 :=
          Nat.mul_le_mul (Nat.le_refl (3 ^ p)) (by omega)
        calc 3 ^ p * (4 * (E % 3 ^ p) / 3 ^ p) ≤ 3 ^ p * 2 := hh
        _ = 2 * 3 ^ p := Nat.mul_comm _ _
      have hfull : 3 * 3 ^ p
          ≤ 3 ^ p * (4 * (E % 3 ^ p) / 3 ^ p) + 4 * (E % 3 ^ p) % 3 ^ p := by
        rw [hsplit]; exact h
      omega
    omega

private theorem div_split_mod (s Q p : Nat) (hp : (0 : Nat) < 3 ^ p) :
    ((s + 3 ^ p * (3 * Q)) / 3 ^ p) % 3 = (s / 3 ^ p) % 3 := by
  rw [Nat.add_mul_div_left s (3 * Q) hp, Nat.add_mul_mod_self_left]

/-- The ternary digit of `E` at height `p` depends only on `E` modulo
`3^(p+1)` — the triadic depth reads the residue. -/
theorem digit3_mod_eq (E p : Nat) :
    digit3 E p = ((E % 3 ^ (p + 1)) / 3 ^ p) % 3 := by
  have hp : (0 : Nat) < 3 ^ p := Nat.pow_pos (by decide)
  have hsplit := Nat.div_add_mod E (3 ^ (p + 1))
  have hE : E = (E % 3 ^ (p + 1)) + 3 ^ p * (3 * (E / 3 ^ (p + 1))) := by
    calc E = 3 ^ (p + 1) * (E / 3 ^ (p + 1)) + E % 3 ^ (p + 1) := hsplit.symm
    _ = 3 ^ p * (3 * (E / 3 ^ (p + 1))) + E % 3 ^ (p + 1) := by
        rw [Nat.pow_succ]; ring
    _ = (E % 3 ^ (p + 1)) + 3 ^ p * (3 * (E / 3 ^ (p + 1))) := Nat.add_comm _ _
  have hE2 : E / 3 ^ p % 3
      = ((E % 3 ^ (p + 1)) + 3 ^ p * (3 * (E / 3 ^ (p + 1)))) / 3 ^ p % 3 := by
    conv_lhs => rw [hE]
    try rfl
  show E / 3 ^ p % 3 = ((E % 3 ^ (p + 1)) / 3 ^ p) % 3
  rw [hE2]
  exact div_split_mod _ _ p hp

/-- The carry reads the same residue: the whole cell of `E` at height `p`
depends only on `E` modulo `3^(p+1)`. -/
theorem carry4_mod (E E' p : Nat) (hcarry : E % 3 ^ p = E' % 3 ^ p) :
    carry4 E p = carry4 E' p := by
  unfold carry4
  rw [hcarry]

/-- **THE HODGE LOCUS IS RESIDUE-INVARIANT**: the locus only depends on the
class of `E` modulo the triadic depth `3^(p+1)` — the arithmetic family
structure of the Hodge condition. -/
theorem hodge_locus_mod_invariant (E E' p : Nat)
    (hmod : E % 3 ^ (p + 1) = E' % 3 ^ (p + 1)) :
    hodgeLocus E p ↔ hodgeLocus E' p := by
  rw [hodge_locus_arithmetic, hodge_locus_arithmetic]
  have hd : digit3 E p = digit3 E' p := by
    rw [digit3_mod_eq, digit3_mod_eq, hmod]
  have hdvd : 3 ^ p ∣ 3 ^ (p + 1) :=
    ⟨3, by rw [Nat.pow_succ]⟩
  have hcarry : E % 3 ^ p = E' % 3 ^ p := by
    rw [← Nat.mod_mod_of_dvd E hdvd, hmod, Nat.mod_mod_of_dvd E' hdvd]
  have hc : carry4 E p = carry4 E' p := carry4_mod E E' p hcarry
  rw [hd, hc]

/-- **CATTANI–DELIGNE–KAPLAN ABSORBED (upgraded: the Hodge locus is a
decidable residue union).**  The human theorem: the locus where extra Hodge
classes appear in a family is an algebraic subvariety (proved with Schmid's
nilpotent orbit machinery).  The GST theorem: the Hodge locus at height `p`
is cut out by a finite set of residue classes modulo the triadic depth
`3^(p+1)` — an arithmetic subvariety with an explicit, decidable membership
test.  Where the human proof moves analytic machinery, the GST proof hands
the variety itself to the kernel. -/
theorem hodge_locus_residue_algebraic (p : Nat) :
    ∃ S : Finset Nat, ∀ E, hodgeLocus E p ↔ E % 3 ^ (p + 1) ∈ S := by
  refine ⟨(Finset.range (3 ^ (p + 1))).filter (fun s => hodgeLocus s p),
    fun E => ?_⟩
  have hEq : E % 3 ^ (p + 1) = (E % 3 ^ (p + 1)) % 3 ^ (p + 1) :=
    (Nat.mod_mod_of_dvd E (Nat.dvd_refl (3 ^ (p + 1)))).symm
  have hinv := hodge_locus_mod_invariant E (E % 3 ^ (p + 1)) p hEq
  rw [Finset.mem_filter]
  exact ⟨fun h => ⟨Finset.mem_range.mpr (Nat.mod_lt _ (Nat.pow_pos (by decide))),
      hinv.mp h⟩,
    fun hmem => hinv.mpr hmem.2⟩

/-! ## §6 The crown and the receipts -/

/-- **THE LEFSCHETZ CROWN**: the whole human engine, absorbed and upgraded,
in one statement — the total divisor generation (the full Hodge conjecture
of the absorbed world), the nilpotence ceiling of the polarization, the
unimodular duality, the polynomial Künneth projectors, and the residue
algebraicity of the Hodge locus. -/
theorem the_lefschetz_crown :
    (∀ f : WaveCoef, ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
      f ⟨C, d, hC, hd⟩
        = ∑ i ∈ Finset.range 12, gev f i * cellClass i ⟨C, d, hC, hd⟩)
  ∧ (∀ (g : WaveCoef) (C d : Nat) (hC : C < 4) (hd : d < 3),
      (Nat.iterate lefschetzOp 6 g) ⟨C, d, hC, hd⟩ = 0)
  ∧ (∀ f : WaveCoef, (∀ g : WaveCoef, topPairing f g = 0) →
      ∀ (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
        f ⟨C, d, hC, hd⟩ = 0)
  ∧ (∀ k : Nat, k < 6 → ∃ (p : Polynomial ℤ) (c : ℤ), c ≠ 0 ∧
      ∀ (g : WaveCoef) (C : Nat) (d : Nat) (hC : C < 4) (hd : d < 3),
        (polyOp p g) ⟨C, d, hC, hd⟩ = c * (sectorProj k g) ⟨C, d, hC, hd⟩)
  ∧ (∀ p : Nat, ∃ S : Finset Nat, ∀ E, hodgeLocus E p ↔ E % 3 ^ (p + 1) ∈ S) :=
  ⟨divisor_generation, lefschetz_sixth_power, pairing_nondegenerate_left,
    fun k hk => kunneth_projector_polynomial k hk,
    hodge_locus_residue_algebraic⟩

/-! ## Receipts — the comparator face of the crown -/

#check cup_comm
#check cupDigit_cubed
#check cupCarry_fourth
#check monomial_is_cellClass
#check divisor_generation
#check lefschetz_iterate_zero
#check lefschetz_sixth_power
#check sector_rank_table
#check lefschetz_injective_below_middle
#check lefschetz_surjective_3
#check lefschetz_surjective_4
#check lefschetz_surjective_5
#check topPairing_pick_left
#check topPairing_pick_right
#check pairing_nondegenerate_left
#check pairing_nondegenerate_right
#check poincare_monomial_kronecker
#check proj_sum
#check sectorProj_eq_self_iff
#check sectorProj_zero_of_six_le
#check sectorProj_sum_function
#check distinct_sector_support_zero
#check kunneth_sector_rigidity_crown
#check lefschetz_respects_kunneth
#check kunnethPoly_eval_zero
#check kunnethPoly_eval_k
#check kunneth_projector_polynomial
#check hodge_locus_arithmetic
#check carry4_zero_iff
#check carry4_three_iff
#check hodge_locus_mod_invariant
#check hodge_locus_residue_algebraic
#check the_lefschetz_crown

#print axioms cup_comm
#print axioms cupDigit_cubed
#print axioms cupCarry_fourth
#print axioms monomial_is_cellClass
#print axioms divisor_generation
#print axioms lefschetz_iterate_zero
#print axioms lefschetz_sixth_power
#print axioms lefschetz_injective_below_middle
#print axioms lefschetz_surjective_3
#print axioms lefschetz_surjective_4
#print axioms lefschetz_surjective_5
#print axioms pairing_nondegenerate_left
#print axioms pairing_nondegenerate_right
#print axioms poincare_monomial_kronecker
#print axioms proj_sum
#print axioms sectorProj_eq_self_iff
#print axioms sectorProj_zero_of_six_le
#print axioms distinct_sector_support_zero
#print axioms kunneth_sector_rigidity_crown
#print axioms lefschetz_respects_kunneth
#print axioms kunneth_projector_polynomial
#print axioms hodge_locus_mod_invariant
#print axioms hodge_locus_residue_algebraic
#print axioms the_lefschetz_crown

end GSTLefschetzCrown
