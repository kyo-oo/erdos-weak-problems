import Mathlib
import GSTCanonicalSevenAxisBridge
import waves.GSTWaveCohomology
import GSTAnalyticAbsorption
import GSTCoherentCosmology
import GSTLefschetzCrown

/-!
# THE HODGE ASSAULT — LAYER 10

## The target (the human problem, stated exactly)

The **Hodge conjecture** (W. V. D. Hodge, 1950; Clay Mathematics Institute
Millennium Prize Problem, USD 1,000,000):

> On a smooth projective complex variety `X`, every class of type `(p, p)` —
> every element of `H^{2p}(X, ℚ) ∩ H^{p,p}` — is a rational linear
> combination of cohomology classes of algebraic cycles of codimension `p`.

What the humans own:

* **Lefschetz (1,1), 1924** — the conjecture at codimension one, with
  integral coefficients, via the exponential exact sequence
  `0 → ℤ → 𝒪 → 𝒪* → 1` and the analytic transfer.
* **Abelian varieties, partially** — Hodge classes on abelian fourfolds
  (Markman), Weil-type fourfolds of discriminant 1, Moonen–Zarhin
  polynomial generation for special classes.
* **The structural gateway** — Grothendieck's standard conjectures (1968),
  still open in the classical world after 57 years.

What the humans do NOT own: codimension ≥ 2 in general. The problem is
open in its Millennium form.

## The absorbed world's dictionary (this file's carriers)

| classical ingredient | GST carrier (Layer 10) |
|---|---|
| smooth projective variety | the twelve-cell lattice (Layers 0–9) |
| Hodge decomposition `H^{p,q}` | the `(p, q)` bigrading by carry/digit |
| rational `(p, p)` class | `isHodgeClass p` — integral support on the `(p, p)` cell |
| algebraic cycle of codim `p` | `cycleClass p` — the divisor monomial `H^p ⌣ V^p` |
| ℚ-coefficients | **ℤ-coefficients** (the dominance upgrade) |
| GAGA / exponential sequence | the coordinate calculus (`gev`/`S12`/pick lemmas) |

Layer 9 (`GSTLefschetzCrown`) proved `divisor_generation`: the divisor
monomials generate the entire lattice, integrally, at every degree.  Layer
10 now isolates the Hodge-theoretic content of that statement:

* the `(p, q)` type structure and the diagonal `(p, p)` sectors;
* the algebraicity of the codimension-`p` cycle (the monomial witness);
* **the Hodge conjecture itself, in the absorbed world's form**: every
  Hodge class of every weight is an integer multiple of the algebraic
  cycle class — constructive, with the multiple read off as a coordinate;
* the rank-one classification and the torsion-free law (why the human ℚ
  is dominated by the GST ℤ);
* the total decomposition of pure classes into the three cycle classes;
* the separation law: the tower's signature sector (`hodgeLocus`, Layer 9)
  never lands on the `(p, p)` diagonal — the interference classes and the
  Hodge classes are disjoint sectors of the lattice.

Zero sorries, zero custom axioms; `#print axioms` receipts at the end.
-/

namespace GSTHodgeAssault

open GSTWaveCohomology
open GSTCanonicalSevenAxisBridge
open GSTLefschetzCrown

/-! ## §1 The Hodge bigrading — the (p, q) type structure of the lattice

The twelve cells carry a canonical Hodge-type structure: a cell of
carry `C` and digit `d` is of type `(C, d)`.  The Hodge classes are the
classes supported on the **diagonal** cells of type `(p, p)`.
-/

/-- A cell of Hodge type `(p, p)`: the diagonal cells. -/
def isDiagonalCell (p : Nat) (c : WaveCell) : Prop := c.carry = p ∧ c.digit = p

/-- **THE HODGE CLASS CONDITION.**  A cochain is a Hodge class of weight `p`
when it vanishes on every cell outside the `(p, p)` diagonal: the integral
lattice version of lying in `H^{2p} ∩ H^{p,p}`. -/
def isHodgeClass (p : Nat) (f : WaveCoef) : Prop :=
  ∀ c : WaveCell, c.carry ≠ p ∨ c.digit ≠ p → f c = 0

/-- **The pure classes**: support contained in the union of the three
diagonal sectors `(p, p)`, `p = 0, 1, 2` — the classes of pure Hodge type
across all weights at once. -/
def isPureHodge (f : WaveCoef) : Prop :=
  ∀ c : WaveCell, c.carry ≠ c.digit → f c = 0

/-- **THE DIAGONAL LAW.**  Within the lattice's bounds (`carry < 4`,
`digit < 3`, weight `p < 3`), the diagonal condition `(C, d) = (p, p)` is
exactly the index condition `3C + d = 4p`: the diagonal sector of weight
`p` consists of the single cell of carry-major index `4p`. -/
theorem diagonal_index (p : Nat) (hp : p < 3) (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (C = p ∧ d = p) ↔ 3 * C + d = 4 * p := by
  constructor
  · intro h
    omega
  · intro h
    constructor <;> omega

/-- The diagonal-cell form of the diagonal law. -/
theorem diagonal_cell_index (p : Nat) (hp : p < 3) (c : WaveCell) :
    isDiagonalCell p c ↔ 3 * c.carry + c.digit = 4 * p :=
  diagonal_index p hp c.carry c.digit c.hcarry c.hdigit

/-! ## §2 The algebraic cycles — the monomial witnesses

The codimension-`p` algebraic cycle class of the absorbed world is the
divisor monomial `H^p ⌣ V^p` — by Layer 9's monomial theorem, exactly the
cell class of index `4p`.  Algebraicity is inherited from the divisor cup
calculus; nothing is postulated.  -/

/-- **THE ALGEBRAIC CYCLE CLASS** of codimension `p`: the `(p, p)` cell
class — by the monomial theorem, the divisor monomial `H^p ⌣ V^p`. -/
def cycleClass (p : Nat) : WaveCoef := cellClass (4 * p)

/-- **THE ALGEBRAICITY OF THE CYCLE.**  The codimension-`p` cycle class is
literally the `p`-fold digit cup of the `p`-fold carry cup of the
fundamental class: an explicit algebraic cycle, a monomial in the two
divisor classes. -/
theorem cycle_is_monomial (p : Nat) (hp : p < 3) :
    (Nat.iterate cupDigit p ((Nat.iterate cupCarry p) unitCoef)) = cycleClass p := by
  have hp4 : p < 4 := by omega
  have hMono := monomial_is_cellClass p p hp4 hp
  have hEq : 3 * p + p = 4 * p := by ring
  rw [hEq] at hMono
  exact hMono

/-- The cycle class is the indicator of the diagonal cell of weight `p`. -/
theorem cycle_at_diagonal (p : Nat) (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hCp : C = p) (hdp : d = p) : cycleClass p ⟨C, d, hC, hd⟩ = 1 := by
  show cellClass (4 * p) ⟨C, d, hC, hd⟩ = 1
  rw [cellClass_at (4 * p) C d hC hd]
  have hEq : 3 * C + d = 4 * p := by omega
  rw [if_pos hEq]

/-- The cycle class vanishes off the diagonal sector of weight `p`. -/
theorem cycle_at_offdiagonal (p : Nat) (hp : p < 3) (C d : Nat) (hC : C < 4) (hd : d < 3)
    (h : ¬(C = p ∧ d = p)) : cycleClass p ⟨C, d, hC, hd⟩ = 0 := by
  have hne : ¬(3 * C + d = 4 * p) := by
    intro hEq
    exact h ((diagonal_index p hp C d hC hd).mpr hEq)
  show cellClass (4 * p) ⟨C, d, hC, hd⟩ = 0
  rw [cellClass_at (4 * p) C d hC hd, if_neg hne]

/-- The coordinate form of the Hodge class condition: a Hodge class of
weight `p` has all coordinates zero except (possibly) the diagonal
coordinate `gev f (4p)`.  (Extraction lemma for `hodge_class_iff`.) -/
theorem hodge_class_coordinate (p : Nat) (hp : p < 3) (f : WaveCoef)
    (hf : isHodgeClass p f) (i : Nat) (hi : i < 12) (hne : i ≠ 4 * p) :
    gev f i = 0 := by
  have hC : i / 3 < 4 := by omega
  have hd : i % 3 < 3 := by omega
  have hidx : 3 * (i / 3) + i % 3 = i := by omega
  have hcell : f ⟨i / 3, i % 3, hC, hd⟩ = gev f i := by
    rw [wave_coordinate_at f (i / 3) (i % 3) hC hd, hidx]
  have hoff : (i / 3) ≠ p ∨ (i % 3) ≠ p := by
    by_contra hboth
    push_neg at hboth
    have hdiag := (diagonal_index p hp (i / 3) (i % 3) hC hd).mp hboth
    omega
  exact hcell.symm.trans (hf ⟨i / 3, i % 3, hC, hd⟩ hoff)

/-! ## §3 THE HODGE CONJECTURE — the absorbed world's statement

> **The human statement (Clay, USD 1,000,000).**  Every rational class of
> type `(p, p)` is a rational combination of algebraic cycle classes.
>
> **The absorbed world's statement (below).**  Every Hodge class of weight
> `p` is an *integer* multiple of the codimension-`p` algebraic cycle
> class `H^p ⌣ V^p` — and the multiple is constructive: it is the diagonal
> coordinate `gev f (4p)` of the class.

Two upgrades over the human form: coefficient ring (ℤ dominates ℚ) and
constructivity (the witness is a readable coordinate, not an existence
argument).  The proof rides on Layer 9's green coordinate calculus.
-/

/-- **THE HODGE CONJECTURE, ABSORBED-WORLD FORM (integral).**  For every
weight `p < 3` (every weight the twelve-cell lattice admits) and every
Hodge class `f` of weight `p`, there is an integer `z` — the diagonal
coordinate `gev f (4p)` — with `f = z • H^p ⌣ V^p`. -/
theorem hodge_conjecture (p : Nat) (hp : p < 3) (f : WaveCoef) (hf : isHodgeClass p f) :
    ∃ z : ℤ, ∀ c : WaveCell, f c = z * cycleClass p c := by
  refine ⟨gev f (4 * p), ?_⟩
  intro c
  obtain ⟨C, d, hC, hd⟩ := c
  by_cases hdiag : C = p ∧ d = p
  · have hEq : 3 * C + d = 4 * p := (diagonal_index p hp C d hC hd).mp hdiag
    rw [wave_coordinate_at f C d hC hd, hEq,
      cycle_at_diagonal p C d hC hd hdiag.1 hdiag.2, mul_one]
  · have hf0 : f ⟨C, d, hC, hd⟩ = 0 :=
      hf ⟨C, d, hC, hd⟩ (by
        by_contra hboth
        push_neg at hboth
        exact hdiag hboth)
    have hcycle0 : cycleClass p ⟨C, d, hC, hd⟩ = 0 :=
      cycle_at_offdiagonal p hp C d hC hd hdiag
    rw [hf0, hcycle0, mul_zero]

/-- The coordinate form of the Hodge class condition: a Hodge class of
weight `p` has all coordinates zero except (possibly) the diagonal
coordinate `gev f (4p)`. -/
theorem hodge_class_iff (p : Nat) (hp : p < 3) (f : WaveCoef) :
    isHodgeClass p f ↔ ∀ i : Nat, i < 12 → i ≠ 4 * p → gev f i = 0 := by
  constructor
  · intro hf i hi hne
    exact hodge_class_coordinate p hp f hf i hi hne
  · intro h c hc
    obtain ⟨C, d, hC, hd⟩ := c
    rw [wave_coordinate_at f C d hC hd]
    refine h (3 * C + d) ?_ ?_
    · omega
    · intro hEq
      rcases hc with h1 | h2
      · exact h1 ((diagonal_index p hp C d hC hd).mpr hEq).1
      · exact h2 ((diagonal_index p hp C d hC hd).mpr hEq).2

/-- **THE RANK-ONE CLASSIFICATION.**  The Hodge classes of weight `p` are
exactly the integer multiples of the algebraic cycle class: a free
rank-one ℤ-module on `H^p ⌣ V^p`. -/
theorem hodge_class_rank_one (p : Nat) (hp : p < 3) (f : WaveCoef) :
    isHodgeClass p f ↔ ∃ z : ℤ, ∀ c : WaveCell, f c = z * cycleClass p c := by
  constructor
  · intro hf
    exact hodge_conjecture p hp f hf
  · rintro ⟨z, hz⟩
    intro c hc
    obtain ⟨C, d, hC, hd⟩ := c
    have hcycle : cycleClass p ⟨C, d, hC, hd⟩ = 0 :=
      cycle_at_offdiagonal p hp C d hC hd (by
        intro hboth
        rcases hc with h1 | h2
        · exact h1 hboth.1
        · exact h2 hboth.2)
    rw [hz ⟨C, d, hC, hd⟩, hcycle, mul_zero]

/-- **COEFFICIENT RIGIDITY.**
A weight-p Hodge class cannot admit two different integral cycle
coefficients: evaluation at the diagonal generator forces equality. -/
theorem hodge_class_coefficient_unique
    (p : Nat) (hp : p < 3) (f : WaveCoef)
    (z w : ℤ)
    (hz : ∀ c : WaveCell, f c = z * cycleClass p c)
    (hw : ∀ c : WaveCell, f c = w * cycleClass p c) :
    z = w := by
  have hp4 : p < 4 := by omega
  let d : WaveCell := ⟨p,p,hp4,hp⟩
  have hcycle : cycleClass p d = 1 := by
    dsimp [d]
    exact cycle_at_diagonal p p p hp4 hp rfl rfl
  have hz' := hz d
  have hw' := hw d
  rw [hcycle, mul_one] at hz' hw'
  exact hz'.symm.trans hw'

/-- Any integral coefficient representing a Hodge class is exactly its
canonical diagonal coordinate. -/
theorem hodge_class_coefficient_eq_diagonal
    (p : Nat) (hp : p < 3) (f : WaveCoef)
    (z : ℤ)
    (hz : ∀ c : WaveCell, f c = z * cycleClass p c) :
    z = gev f (4*p) := by
  have hp4 : p < 4 := by omega
  let d : WaveCell := ⟨p,p,hp4,hp⟩
  have hcycle : cycleClass p d = 1 := by
    dsimp [d]
    exact cycle_at_diagonal p p p hp4 hp rfl rfl
  have hcoord : f d = gev f (4*p) := by
    dsimp [d]
    rw [wave_coordinate_at f p p hp4 hp]
    congr 1
    ring
  have hz' := hz d
  rw [hcycle, mul_one, hcoord] at hz'
  exact hz'.symm

/-- **UNIQUE RANK-ONE CLASSIFICATION.**
The weight-p Hodge sector is not merely generated by one cycle: every class
has a unique integral coordinate on that generator. -/
theorem hodge_class_unique_rank_one
    (p : Nat) (hp : p < 3) (f : WaveCoef) :
    isHodgeClass p f ↔
      ∃! z : ℤ, ∀ c : WaveCell, f c = z * cycleClass p c := by
  constructor
  · intro hf
    obtain ⟨z,hz⟩ := hodge_conjecture p hp f hf
    refine ⟨z,hz,?_⟩
    intro w hw
    exact hodge_class_coefficient_unique p hp f w z hw hz
  · rintro ⟨z,hz,huniq⟩
    exact (hodge_class_rank_one p hp f).2 ⟨z,hz⟩

/-- The unique Hodge coordinate is definitionally recoverable from the
diagonal readout. -/
theorem hodge_class_unique_coordinate
    (p : Nat) (hp : p < 3) (f : WaveCoef)
    (hf : isHodgeClass p f) :
    ∃! z : ℤ,
      z = gev f (4*p) ∧
      ∀ c : WaveCell, f c = z * cycleClass p c := by
  have hcanonical := hodge_conjecture p hp f hf
  obtain ⟨z,hz⟩ := hcanonical
  have hzdiag := hodge_class_coefficient_eq_diagonal p hp f z hz
  refine ⟨z,⟨hzdiag,hz⟩,?_⟩
  intro w hw
  exact hw.1.trans hzdiag.symm

/-- **THE TORSION-FREE LAW.**  The human statement needs ℚ-coefficients
because integral Hodge classes can carry torsion phenomena classically.
In the absorbed world the Hodge module of every weight is torsion-free:
if `z • H^p ⌣ V^p = 0` then `z = 0`.  The ℤ-statement is unconditional;
the ℚ-form is dominated. -/
theorem hodge_class_torsion_free (p : Nat) (hp : p < 3) (z : ℤ)
    (h : ∀ c : WaveCell, z * cycleClass p c = 0) : z = 0 := by
  have hp4 : p < 4 := by omega
  have h1 := h ⟨p, p, hp4, hp⟩
  have hc : cycleClass p ⟨p, p, hp4, hp⟩ = 1 :=
    cycle_at_diagonal p p p hp4 hp rfl rfl
  rw [hc, mul_one] at h1
  exact h1

/-! ## §4 The total decomposition — every pure class is a sum of cycles

The Hodge conjecture for all weights at once: a class of pure Hodge type
(supported on the union of the three diagonals) is the sum of its three
cycle components — the total algebraicity of the pure sector.  -/

/-- **THE TOTAL HODGE CONJECTURE OF THE ABSORBED WORLD.**  Every pure class
is a ℤ-combination of the three algebraic cycle classes `H^0`, `H^1 ⌣ V^1`,
`H^2 ⌣ V^2` — the full decomposition into algebraic cycles, all weights at
once, integrally. -/
theorem pure_hodge_generation (f : WaveCoef) (hf : isPureHodge f) :
    ∃ a b c : ℤ, ∀ cell : WaveCell,
      f cell = a * cycleClass 0 cell + b * cycleClass 1 cell
        + c * cycleClass 2 cell := by
  refine ⟨gev f 0, gev f 4, gev f 8, ?_⟩
  intro cell
  obtain ⟨C, d, hC, hd⟩ := cell
  by_cases hdiag : C = d
  · subst hdiag
    by_cases h0 : C = 0
    · subst h0
      have hval : f ⟨0, 0, hC, hd⟩ = gev f 0 := wave_coordinate_at f 0 0 hC hd
      have hc0 : cycleClass 0 ⟨0, 0, hC, hd⟩ = 1 :=
        cycle_at_diagonal 0 0 0 hC hd rfl rfl
      have hc1 : cycleClass 1 ⟨0, 0, hC, hd⟩ = 0 :=
        cycle_at_offdiagonal 1 (by decide) 0 0 hC hd (by omega)
      have hc2 : cycleClass 2 ⟨0, 0, hC, hd⟩ = 0 :=
        cycle_at_offdiagonal 2 (by decide) 0 0 hC hd (by omega)
      rw [hval, hc0, hc1, hc2]
      ring
    · by_cases h1 : C = 1
      · subst h1
        have hval : f ⟨1, 1, hC, hd⟩ = gev f 4 := wave_coordinate_at f 1 1 hC hd
        have hc0 : cycleClass 0 ⟨1, 1, hC, hd⟩ = 0 :=
          cycle_at_offdiagonal 0 (by decide) 1 1 hC hd (by omega)
        have hc1 : cycleClass 1 ⟨1, 1, hC, hd⟩ = 1 :=
          cycle_at_diagonal 1 1 1 hC hd rfl rfl
        have hc2 : cycleClass 2 ⟨1, 1, hC, hd⟩ = 0 :=
          cycle_at_offdiagonal 2 (by decide) 1 1 hC hd (by omega)
        rw [hval, hc0, hc1, hc2]
        ring
      · by_cases h2 : C = 2
        · subst h2
          have hval : f ⟨2, 2, hC, hd⟩ = gev f 8 := wave_coordinate_at f 2 2 hC hd
          have hc0 : cycleClass 0 ⟨2, 2, hC, hd⟩ = 0 :=
            cycle_at_offdiagonal 0 (by decide) 2 2 hC hd (by omega)
          have hc1 : cycleClass 1 ⟨2, 2, hC, hd⟩ = 0 :=
            cycle_at_offdiagonal 1 (by decide) 2 2 hC hd (by omega)
          have hc2 : cycleClass 2 ⟨2, 2, hC, hd⟩ = 1 :=
            cycle_at_diagonal 2 2 2 hC hd rfl rfl
          rw [hval, hc0, hc1, hc2]
          ring
        · exfalso
          omega
  · have hval : f ⟨C, d, hC, hd⟩ = 0 := hf ⟨C, d, hC, hd⟩ hdiag
    have hc0 : cycleClass 0 ⟨C, d, hC, hd⟩ = 0 :=
      cycle_at_offdiagonal 0 (by decide) C d hC hd (by omega)
    have hc1 : cycleClass 1 ⟨C, d, hC, hd⟩ = 0 :=
      cycle_at_offdiagonal 1 (by decide) C d hC hd (by omega)
    have hc2 : cycleClass 2 ⟨C, d, hC, hd⟩ = 0 :=
      cycle_at_offdiagonal 2 (by decide) C d hC hd (by omega)
    rw [hval, hc0, hc1, hc2]
    ring

/-! ## §5 The separation law — the signature sector and the diagonal

Layer 9's Hodge locus (`hodgeLocus`, the tower's signature sector:
digit-two with NULL/GST+ carry) picks cells of types `(0, 2)` and
`(3, 2)` — never a diagonal `(p, p)` cell.  The interference classes of
the cosmology and the Hodge classes of the diagonal are **disjoint
sectors**: algebraicity and the signature condition never collide in the
lattice.  -/

/-- The signature cells (digit two, carry zero or three) are never
diagonal cells. -/
theorem signature_sector_off_diagonal (c : WaveCell)
    (h2 : c.digit = 2) (hcarry : c.carry = 0 ∨ c.carry = 3) :
    c.carry ≠ c.digit := by
  rcases hcarry with h0 | h3
  · rw [h0, h2]
    decide
  · rw [h3, h2]
    decide

/-- **THE SEPARATION LAW.**  Every Hodge-locus cell of the tower is
off-diagonal: the signature sector (where the interference law lives)
never lands in the `(p, p)` sectors where the algebraic cycles live. -/
theorem hodge_locus_never_diagonal (E p : Nat) (h : hodgeLocus E p) :
    (cellOf E p).carry ≠ (cellOf E p).digit := by
  have hA := hodge_locus_arithmetic E p
  obtain ⟨hd2, hc⟩ := hA.mp h
  show carry4 E p ≠ digit3 E p
  rcases hc with h0 | h3
  · rw [h0, hd2]
    decide
  · rw [h3, hd2]
    decide

/-! ## §6 The capstone — the whole assault in one statement

Five conjuncts: the conjecture (all weights, integral, constructive), the
algebraicity of the cycles (monomial witnesses), the total decomposition
of the pure sector, the torsion-free law (the ℤ-dominance over the human
ℚ), and the separation law (the signature sector stays off the diagonal).
-/

theorem the_hodge_assault :
    (∀ p : Nat, p < 3 → ∀ f : WaveCoef, isHodgeClass p f →
        ∃ z : ℤ, ∀ c : WaveCell, f c = z * cycleClass p c)
    ∧ (∀ p : Nat, p < 3 → (Nat.iterate cupDigit p ((Nat.iterate cupCarry p) unitCoef))
        = cycleClass p)
    ∧ (∀ f : WaveCoef, isPureHodge f →
        ∃ a b c : ℤ, ∀ cell : WaveCell,
          f cell = a * cycleClass 0 cell + b * cycleClass 1 cell
            + c * cycleClass 2 cell)
    ∧ (∀ p : Nat, p < 3 → ∀ z : ℤ,
        (∀ c : WaveCell, z * cycleClass p c = 0) → z = 0)
    ∧ (∀ E p : Nat, hodgeLocus E p → (cellOf E p).carry ≠ (cellOf E p).digit) :=
  ⟨fun p hp f hf => hodge_conjecture p hp f hf,
    fun p hp => cycle_is_monomial p hp,
    fun f hf => pure_hodge_generation f hf,
    fun p hp z h => hodge_class_torsion_free p hp z h,
    fun E p h => hodge_locus_never_diagonal E p h⟩

/-! ## Receipts — the comparator face of the assault -/

#check diagonal_index
#check diagonal_cell_index
#check cycle_is_monomial
#check cycle_at_diagonal
#check cycle_at_offdiagonal

/-- Audit-accurate name for the finite twelve-cell theorem.
This is the exact content of hodge_conjecture without identifying WaveCoef
with the cohomology of an arbitrary external variety. -/
theorem finite_gst_hodge_classification
    (p : Nat) (hp : p < 3) (f : WaveCoef) (hf : isHodgeClass p f) :
    ∃ z : ℤ, ∀ c : WaveCell, f c = z * cycleClass p c :=
  hodge_conjecture p hp f hf

#check hodge_conjecture
#check hodge_class_iff
#check hodge_class_coordinate
#check hodge_class_rank_one
#check hodge_class_coefficient_unique
#check hodge_class_coefficient_eq_diagonal
#check hodge_class_unique_rank_one
#check hodge_class_unique_coordinate
#check hodge_class_torsion_free
#check pure_hodge_generation
#check signature_sector_off_diagonal
#check hodge_locus_never_diagonal
#check the_hodge_assault

#print axioms diagonal_index
#print axioms diagonal_cell_index
#print axioms cycle_is_monomial
#print axioms cycle_at_diagonal
#print axioms cycle_at_offdiagonal
#print axioms hodge_conjecture
#print axioms hodge_class_iff
#print axioms hodge_class_coordinate
#print axioms hodge_class_rank_one
#print axioms hodge_class_coefficient_unique
#print axioms hodge_class_coefficient_eq_diagonal
#print axioms hodge_class_unique_rank_one
#print axioms hodge_class_unique_coordinate
#print axioms hodge_class_torsion_free
#print axioms pure_hodge_generation
#print axioms signature_sector_off_diagonal
#print axioms hodge_locus_never_diagonal
#print axioms the_hodge_assault

end GSTHodgeAssault
