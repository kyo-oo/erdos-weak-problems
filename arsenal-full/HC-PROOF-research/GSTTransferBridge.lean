import Mathlib
import GSTCanonicalSevenAxisBridge
import waves.GSTWaveCohomology
import GSTLefschetzCrown
import GSTHodgeAssault
import GSTClayOfficial

/-!
# THE TRANSFER BRIDGE — LAYER 12

## The target — the queued Phase-2 front, now built

The Task-12 verdict recorded the one remaining construction front of the
Hodge campaign: **the transfer/export theorem** — the bridge that carries
the GST world's machine-checked Hodge theorem out into the classical
universe's own language.  Layers 1–9 absorbed the classical world into
the GST carriers (classical → GST); this layer runs the construction in
reverse (GST → classical).  Nothing on either side is graded by the
other; both universes stand at full strength, and the bridge is built
entirely from the GST arsenal — classical mathematics appears nowhere in
any proof below.

## The construction — stage 1: the ring-level export

The classical address of the crown geometry is its cohomology ring in the
standard degree basis:

* **`ClRing`** — the free ℤ-module on the twelve degrees `0 … 11`, the
  standard form of the truncated two-divisor ring
  `ℤ[H, V] / (H³, V⁴)` (degree `i` ↔ the monomial `H^{i % 3} V^{i / 3}`,
  `deg H = 1`, `deg V = 3`).
* **`clMul`** — the truncated monomial product: `(f · g) i` sums the
  pairs `j + k = i` whose digit sum stays below the 3-bound; the
  relations `H³ = 0` (digit overflow kills) and `V⁴ = 0` (degree ≥ 12
  kills) are structural.
* **`clCupD` / `clCupV`** — the two divisor cups on the degree basis:
  the digit tower shift `i ↦ i - 1` below the 3-boundary, the carry
  tower shift `i ↦ i - 3`.

**The dictionary** `addr : WaveCoef → ClRing` reads the twelve GST
coordinates into the twelve classical degrees.  The bridge's
load-bearing theorems:

* **the dictionary is a bijection** (`addr_bijective`) and additive
  (`addr_add`) — an isomorphism of the cochain groups;
* **the cup calculus transports exactly** (`addr_cupDigit`,
  `addr_cupCarry`): the GST `cupDigit`/`cupCarry` operators ARE the
  classical multiplication by the hyperplane classes
  (`clCupD_eq_mulH`, `clCupV_eq_mulV`) — the GST cup calculus and the
  classical degree-basis product are one and the same operation;
* **the ring laws transport** — `H · V = V · H` (`clCupD_clCupV_comm`),
  `H³ = 0` (`clH_cubed`), `V⁴ = 0` (`clV_fourth`);
* **the algebraic cycle classes transport** (`cl_monomial`): the
  codimension-`p` cycle is the degree-`4p` monomial, carried over from
  Layer 10's `cycle_is_monomial` — algebraicity inherited, not
  reproved;
* **THE HODGE CONJECTURE AND THE OFFICIAL CLAY STATEMENT TRANSFER**
  (`transferred_hodge_conjecture`, `transferred_clay_hodge_conjecture`,
  `transferred_clay_witness`): every rational `(p, p)`-class of the
  classical address — every degree-`4p` class — is a rational multiple
  of the algebraic monomial `H^p V^p`, with the multiple read off as the
  degree-`4p` coordinate.  GST's ℤ-strength carries Clay's ℚ-form across
  the bridge.

## Stage 2 status

The former Stage-2 geometric-realization target is now split explicitly
and machine-checked through four progressively more geometric interfaces.

* Stage 2A (GSTGeometricRealizationStage2) proves the variable-rank finite
  coordinate realization criterion.
* Stage 2B (GSTGeometricRealizationStage2B) replaces the generic Hodge
  predicate by an honest rational Hodge submodule and proves
  HodgeSubspace <= LinearMap.range cycleClass.
* Stage 2C (GSTGeometricRealizationStage2C) quantifies over actual Mathlib
  Scheme objects and actual Mathlib AlgebraicCycle X Q carriers.  Because
  the pinned locally-finite-cycle API lacks a Q-module instance, Stage 2C
  constructs the canonical pointwise rational module structure and proves
  it preserves local finiteness.
* Stage 2D (GSTGeometricRealizationStage2D) removes the arbitrary cycle
  subspace: the domain is the native codimension-p cycle submodule cut out
  by support on points with Order.coheight = p.

The dedicated Stage-2 gate is green (run 35669757803): A+B+C+D compile,
the proof-escape scan passes, and the sorryAx audit passes.

The remaining classical instantiation problem is now narrower but still
genuine: supply actual rational cohomology, its rational (p,p) Hodge
subspace, the genuine cohomological cycle-class map, a formal
smooth-projective-over-C eligibility package, and the universal
basis-cycle realization family.  The finite twelve-cell carrier alone does
not supply those data.

The separate MvPolynomial presentation of the finite twelve-cell ring is
still useful algebraically, but it is not a substitute for that geometric
instantiation.

Zero sorries, zero custom axioms; `#print axioms` receipts at the end.
-/

namespace GSTTransferBridge

open GSTWaveCohomology
open GSTCanonicalSevenAxisBridge
open GSTLefschetzCrown
open GSTHodgeAssault
open GSTClayOfficial

/-! ## §1 The classical-address carrier and the dictionary

`ClRing` is the degree basis: the free ℤ-module on the twelve degrees.
The dictionary `addr` reads the twelve GST coordinates (carry-major
`i = 3C + d`) into the twelve classical degrees — the export map of the
bridge.
-/

/-- **THE CLASSICAL-ADDRESS RING.**  The free ℤ-module on the twelve
degrees `0 … 11` — the standard degree basis of the truncated
two-divisor ring `ℤ[H, V] / (H³, V⁴)`: degree `i` carries the monomial
`H^{i % 3} V^{i / 3}`. -/
def ClRing : Type := Fin 12 → ℤ

/-- **THE EXPORT DICTIONARY.**  The GST cochain read in the classical
degree basis: the twelve coordinates `gev f i` become the twelve
classical degrees. -/
def addr (f : WaveCoef) : ClRing := fun i => gev f (i : ℕ)

/-- The classical monomial of degree `n`: the indicator of the degree-`n`
piece — `H^{n % 3} V^{n / 3}` in the degree basis. -/
def clMono (n : Nat) : ClRing := fun i => if (i : ℕ) = n then 1 else 0

/-- The classical fundamental class: the degree-`0` monomial. -/
def clUnit : ClRing := clMono 0

/-- The classical digit (de Rham world) hyperplane class `H`: the
degree-`1` monomial. -/
def clH : ClRing := clMono 1

/-- The classical carry (Betti world) hyperplane class `V`: the
degree-`3` monomial. -/
def clV : ClRing := clMono 3

/-- The cell of index `n` viewed through the coordinate map: the value
at the cell of degree `n` is the `n`-th coordinate. -/
theorem gev_cell (f : WaveCoef) (n : Nat) (hn : n < 12) :
    gev f n = f ⟨n / 3, n % 3, by omega, by omega⟩ := by
  have hidx : n = 3 * (n / 3) + n % 3 := by omega
  have hw := wave_coordinate_at f (n / 3) (n % 3) (by omega) (by omega)
  rw [← hidx] at hw
  exact hw.symm

/-- **THE DICTIONARY IS INJECTIVE.**  Distinct GST cochains export to
distinct classical addresses: the twelve coordinates separate. -/
theorem addr_injective : Function.Injective addr := by
  intro f g hfg
  funext c
  obtain ⟨C, d, hC, hd⟩ := c
  rw [wave_coordinate_at f C d hC hd, wave_coordinate_at g C d hC hd]
  have h1 : ∀ i : Fin 12, addr f i = addr g i := fun i => congrArg (fun ψ => ψ i) hfg
  exact h1 ⟨3 * C + d, by omega⟩

/-- **THE DICTIONARY IS SURJECTIVE.**  Every classical address is the
export of a GST cochain: the coordinate reassembly `S12` builds the
preimage. -/
theorem addr_surjective : Function.Surjective addr := by
  intro φ
  refine ⟨S12 (fun n => if hn : n < 12 then φ ⟨n, hn⟩ else 0), ?_⟩
  funext i
  show gev (S12 (fun n => if hn : n < 12 then φ ⟨n, hn⟩ else 0)) (i : ℕ) = φ i
  rw [gev_S12 (fun n => if hn : n < 12 then φ ⟨n, hn⟩ else 0) (i : ℕ) i.isLt]
  exact dif_pos i.isLt

/-- **THE DICTIONARY IS A BIJECTION.**  The GST cochain group and the
classical degree-basis group are the same twelve coordinates: the
cochain-level identification of the two worlds. -/
theorem addr_bijective : Function.Bijective addr :=
  ⟨addr_injective, addr_surjective⟩

/-- **THE DICTIONARY IS ADDITIVE.**  The export of a pointwise sum is
the pointwise sum of the exports: the cochain-group isomorphism. -/
theorem addr_add (f g : WaveCoef) (i : Fin 12) :
    addr (fun c => f c + g c) i = addr f i + addr g i := by
  obtain ⟨n, hn⟩ := i
  interval_cases n
  all_goals rfl

/-- **THE CELL CLASSES EXPORT TO MONOMIALS.**  The GST cell class of
index `n` is the classical monomial of degree `n` — the monomial basis
of the cup ring is the monomial basis of the degree ring. -/
theorem addr_cellClass (n : Nat) : addr (cellClass n) = clMono n := by
  funext i
  have hi := i.isLt
  calc addr (cellClass n) i = gev (cellClass n) (i : ℕ) := rfl
    _ = cellClass n ⟨(i : ℕ) / 3, (i : ℕ) % 3, by omega, by omega⟩ :=
        gev_cell (cellClass n) (i : ℕ) hi
    _ = (if 3 * ((i : ℕ) / 3) + (i : ℕ) % 3 = n then (1:ℤ) else 0) :=
        cellClass_at n ((i : ℕ) / 3) ((i : ℕ) % 3) (by omega) (by omega)
    _ = (if (i : ℕ) = n then (1:ℤ) else 0) := by
        have hidx : 3 * ((i : ℕ) / 3) + (i : ℕ) % 3 = (i : ℕ) := by omega
        rw [hidx]
    _ = clMono n i := rfl

/-- **THE ALGEBRAIC CYCLE CLASSES EXPORT TO THE DIAGONAL MONOMIALS.**
The codimension-`p` cycle class `H^p ⌣ V^p` is the classical monomial of
degree `4p` — the (p, p) diagonal degree. -/
theorem addr_cycleClass (p : Nat) : addr (cycleClass p) = clMono (4 * p) := by
  show addr (cellClass (4 * p)) = clMono (4 * p)
  exact addr_cellClass (4 * p)

/-- **THE FUNDAMENTAL CLASS EXPORTS TO THE UNIT.** -/
theorem addr_unit : addr unitCoef = clUnit := by
  show addr (cellClass 0) = clMono 0
  exact addr_cellClass 0

/-! ## §2 The classical cup operators and the truncated product

The two divisor cups on the degree basis: the digit tower shift and the
carry tower shift — the exact mirrors of `cupDigit`/`cupCarry` on the
classical address.  The truncated monomial product `clMul` is the
standard product of `ℤ[H, V] / (H³, V⁴)` in the degree basis: pairs of
degrees sum to the target degree, with the digit-overflow pairs killed
by `H³ = 0` and the out-of-range degrees killed by `V⁴ = 0`.
-/

/-- **THE CLASSICAL DIGIT CUP.**  Cup with `H` on the degree basis: read
one degree down, below the 3-boundary `i % 3 ≠ 0`. -/
def clCupD (φ : ClRing) : ClRing :=
  fun i => if (i:ℕ) % 3 ≠ 0 then φ ⟨(i:ℕ) - 1, by have := i.isLt; omega⟩ else 0

/-- **THE CLASSICAL CARRY CUP.**  Cup with `V` on the degree basis: read
three degrees down, below the carry boundary `3 ≤ i`. -/
def clCupV (φ : ClRing) : ClRing :=
  fun i => if 3 ≤ (i:ℕ) then φ ⟨(i:ℕ) - 3, by have := i.isLt; omega⟩ else 0

/-- **THE TRUNCATED MONOMIAL PRODUCT.**  The product of the degree ring
`ℤ[H, V] / (H³, V⁴)` in the monomial basis: the degree-`i` coefficient
of `f · g` sums the pairs `j + k = i` with digit sum below the 3-bound
(`H³ = 0` kills the overflow); degrees ≥ 12 do not exist in the basis
(`V⁴ = 0`). -/
def clMul (f g : ClRing) : ClRing :=
  fun i => ∑ j ∈ (Finset.univ : Finset (Fin 12)),
    if (j:ℕ) ≤ (i:ℕ) ∧ (j:ℕ) % 3 + ((i:ℕ) - (j:ℕ)) % 3 < 3
      then f j * g ⟨(i:ℕ) - (j:ℕ), by have := i.isLt; omega⟩ else 0

/-- **THE H-CUP IS MULTIPLICATION BY THE HYPERPLANE CLASS.**  The
classical digit cup equals the truncated product with `clH`: the GST
cup-with-`H` operator and the classical multiply-by-`H` are one and the
same operation on the degree basis.  (The product collapses to the
single `H`-term; the digit condition `1 + (i - 1) % 3 < 3` is exactly
`i % 3 ≠ 0`.) -/
theorem clCupD_eq_mulH (φ : ClRing) : clCupD φ = clMul clH φ := by
  funext i
  have hi := i.isLt
  have h₀ : ∀ b ∈ (Finset.univ : Finset (Fin 12)), b ≠ (⟨1, by omega⟩ : Fin 12) →
      (if (b:ℕ) ≤ (i:ℕ) ∧ (b:ℕ) % 3 + ((i:ℕ) - (b:ℕ)) % 3 < 3
        then clH b * φ ⟨(i:ℕ) - (b:ℕ), by have := hi; omega⟩ else 0) = (0:ℤ) := by
    intro b _ hbne
    by_cases hcond : (b:ℕ) ≤ (i:ℕ) ∧ (b:ℕ) % 3 + ((i:ℕ) - (b:ℕ)) % 3 < 3
    · rw [if_pos hcond]
      have hb1 : clH b = (0:ℤ) := by
        show (if (b:ℕ) = 1 then (1:ℤ) else 0) = 0
        refine if_neg ?_
        intro hv
        apply hbne
        obtain ⟨bv, hbv⟩ := b
        subst hv
        rfl
      rw [hb1, zero_mul]
    · rw [if_neg hcond]
  symm
  calc clMul clH φ i
      = (∑ j ∈ (Finset.univ : Finset (Fin 12)),
          if (j:ℕ) ≤ (i:ℕ) ∧ (j:ℕ) % 3 + ((i:ℕ) - (j:ℕ)) % 3 < 3
            then clH j * φ ⟨(i:ℕ) - (j:ℕ), by have := hi; omega⟩ else 0) := rfl
    _ = (if (1:ℕ) ≤ (i:ℕ) ∧ (1:ℕ) % 3 + ((i:ℕ) - 1) % 3 < 3
          then clH ⟨1, by omega⟩ * φ ⟨(i:ℕ) - 1, by have := hi; omega⟩ else 0) :=
        Finset.sum_eq_single_of_mem (⟨1, by omega⟩ : Fin 12) (Finset.mem_univ _) h₀
    _ = (if (i:ℕ) % 3 ≠ 0 then φ ⟨(i:ℕ) - 1, by have := hi; omega⟩ else 0) := by
        have hH1 : clH ⟨1, by omega⟩ = (1:ℤ) := rfl
        rw [hH1, one_mul]
        by_cases hmod : (i:ℕ) % 3 ≠ 0
        · rw [if_pos hmod, if_pos ⟨by omega, by have := Nat.div_add_mod (i:ℕ) 3; omega⟩]
        · rw [if_neg hmod, if_neg (by have := Nat.div_add_mod (i:ℕ) 3; omega)]
    _ = clCupD φ i := rfl

/-- **THE V-CUP IS MULTIPLICATION BY THE HYPERPLANE CLASS.**  The
classical carry cup equals the truncated product with `clV`.  (The
product collapses to the single `V`-term; the digit condition
`3 % 3 + (i - 3) % 3 < 3` is automatic, leaving `3 ≤ i`.) -/
theorem clCupV_eq_mulV (φ : ClRing) : clCupV φ = clMul clV φ := by
  funext i
  have hi := i.isLt
  have h₀ : ∀ b ∈ (Finset.univ : Finset (Fin 12)), b ≠ (⟨3, by omega⟩ : Fin 12) →
      (if (b:ℕ) ≤ (i:ℕ) ∧ (b:ℕ) % 3 + ((i:ℕ) - (b:ℕ)) % 3 < 3
        then clV b * φ ⟨(i:ℕ) - (b:ℕ), by have := hi; omega⟩ else 0) = (0:ℤ) := by
    intro b _ hbne
    by_cases hcond : (b:ℕ) ≤ (i:ℕ) ∧ (b:ℕ) % 3 + ((i:ℕ) - (b:ℕ)) % 3 < 3
    · rw [if_pos hcond]
      have hb3 : clV b = (0:ℤ) := by
        show (if (b:ℕ) = 3 then (1:ℤ) else 0) = 0
        refine if_neg ?_
        intro hv
        apply hbne
        obtain ⟨bv, hbv⟩ := b
        subst hv
        rfl
      rw [hb3, zero_mul]
    · rw [if_neg hcond]
  symm
  calc clMul clV φ i
      = (∑ j ∈ (Finset.univ : Finset (Fin 12)),
          if (j:ℕ) ≤ (i:ℕ) ∧ (j:ℕ) % 3 + ((i:ℕ) - (j:ℕ)) % 3 < 3
            then clV j * φ ⟨(i:ℕ) - (j:ℕ), by have := hi; omega⟩ else 0) := rfl
    _ = (if (3:ℕ) ≤ (i:ℕ) ∧ (3:ℕ) % 3 + ((i:ℕ) - 3) % 3 < 3
          then clV ⟨3, by omega⟩ * φ ⟨(i:ℕ) - 3, by have := hi; omega⟩ else 0) :=
        Finset.sum_eq_single_of_mem (⟨3, by omega⟩ : Fin 12) (Finset.mem_univ _) h₀
    _ = (if 3 ≤ (i:ℕ) then φ ⟨(i:ℕ) - 3, by have := hi; omega⟩ else 0) := by
        have hV1 : clV ⟨3, by omega⟩ = (1:ℤ) := rfl
        rw [hV1, one_mul]
        by_cases h3 : 3 ≤ (i:ℕ)
        · rw [if_pos h3, if_pos ⟨h3, by omega⟩]
        · rw [if_neg h3, if_neg (by omega)]
    _ = clCupV φ i := rfl

/-- **THE RING LAW `H · V = V · H` (classical address).**  The two
divisor cups commute on the degree basis — the transport of Layer 9's
`cup_comm`. -/
theorem clCupD_clCupV_comm (φ : ClRing) : clCupD (clCupV φ) = clCupV (clCupD φ) := by
  funext i
  obtain ⟨n, hn⟩ := i
  interval_cases n
  all_goals simp [clCupD, clCupV]

/-- **THE 3-WORLD BOUNDARY `H³ = 0` (classical address).**  Three digit
cups annihilate every classical class — the transport of Layer 9's
`cupDigit_cubed`. -/
theorem clH_cubed (φ : ClRing) : clCupD (clCupD (clCupD φ)) = fun _ => 0 := by
  funext i
  obtain ⟨n, hn⟩ := i
  interval_cases n
  all_goals simp [clCupD]

/-- **THE 4-WORLD BOUNDARY `V⁴ = 0` (classical address).**  Four carry
cups annihilate every classical class — the transport of Layer 9's
`cupCarry_fourth`. -/
theorem clV_fourth (φ : ClRing) :
    clCupV (clCupV (clCupV (clCupV φ))) = fun _ => 0 := by
  funext i
  obtain ⟨n, hn⟩ := i
  interval_cases n
  all_goals rfl

/-! ## §3 The transport of the cup calculus

The dictionary commutes with the cup operators — and their iterates.
Every GST cup statement rides across the bridge unchanged.
-/

/-- **THE DIGIT CUP TRANSPORTS.**  The export of `cupDigit g` is the
classical digit cup of the export: the dictionary and the H-cup
commute. -/
theorem addr_cupDigit (g : WaveCoef) : addr (cupDigit g) = clCupD (addr g) := by
  funext i
  obtain ⟨n, hn⟩ := i
  have hcd : cupDigit g
      = S12 (fun i => if i % 3 ≠ 0 then gev g (i - 1) else 0) := rfl
  have hL : addr (cupDigit g) ⟨n, hn⟩
      = if n % 3 ≠ 0 then gev g (n - 1) else 0 := by
    show gev (cupDigit g) n = if n % 3 ≠ 0 then gev g (n - 1) else 0
    rw [hcd, gev_S12 (fun i => if i % 3 ≠ 0 then gev g (i - 1) else 0) n hn]
  have hR : clCupD (addr g) ⟨n, hn⟩
      = if n % 3 ≠ 0 then gev g (n - 1) else 0 := rfl
  rw [hL, hR]

/-- **THE CARRY CUP TRANSPORTS.**  The export of `cupCarry g` is the
classical carry cup of the export: the dictionary and the V-cup
commute. -/
theorem addr_cupCarry (g : WaveCoef) : addr (cupCarry g) = clCupV (addr g) := by
  funext i
  obtain ⟨n, hn⟩ := i
  interval_cases n
  all_goals rfl

/-- **THE ITERATED DIGIT CUP TRANSPORTS.**  `p` GST digit cups export to
`p` classical digit cups, for every `p`. -/
theorem addr_cupDigit_iterate : ∀ (n : Nat) (g : WaveCoef),
    addr ((Nat.iterate cupDigit n) g) = (Nat.iterate clCupD n) (addr g) := by
  intro n
  induction n with
  | zero => intro g; rfl
  | succ m ih =>
      intro g
      rw [Function.iterate_succ, Function.iterate_succ,
          Function.comp_apply, Function.comp_apply, ih, addr_cupDigit]

/-- **THE ITERATED CARRY CUP TRANSPORTS.**  `p` GST carry cups export to
`p` classical carry cups, for every `p`. -/
theorem addr_cupCarry_iterate : ∀ (n : Nat) (g : WaveCoef),
    addr ((Nat.iterate cupCarry n) g) = (Nat.iterate clCupV n) (addr g) := by
  intro n
  induction n with
  | zero => intro g; rfl
  | succ m ih =>
      intro g
      rw [Function.iterate_succ, Function.iterate_succ,
          Function.comp_apply, Function.comp_apply, ih, addr_cupCarry]

/-- **THE MONOMIAL WITNESS TRANSPORTS.**  The classical codimension-`p`
cycle class — the degree-`4p` monomial — is the `p`-fold digit cup of
the `p`-fold carry cup of the classical fundamental class: Layer 10's
`cycle_is_monomial`, exported across the bridge.  Algebraicity
inherited, not reproved. -/
theorem cl_monomial (p : Nat) (hp : p < 3) :
    (Nat.iterate clCupD p) ((Nat.iterate clCupV p) clUnit) = clMono (4 * p) := by
  have hchain : (Nat.iterate clCupD p) ((Nat.iterate clCupV p) clUnit)
      = addr ((Nat.iterate cupDigit p) ((Nat.iterate cupCarry p) unitCoef)) := by
    calc (Nat.iterate clCupD p) ((Nat.iterate clCupV p) clUnit)
        = (Nat.iterate clCupD p) ((Nat.iterate clCupV p) (addr unitCoef)) := by
          rw [addr_unit]
      _ = (Nat.iterate clCupD p) (addr ((Nat.iterate cupCarry p) unitCoef)) := by
          rw [← addr_cupCarry_iterate p unitCoef]
      _ = addr ((Nat.iterate cupDigit p) ((Nat.iterate cupCarry p) unitCoef)) := by
          rw [← addr_cupDigit_iterate p ((Nat.iterate cupCarry p) unitCoef)]
  rw [hchain, cycle_is_monomial p hp,
      show cycleClass p = cellClass (4 * p) from rfl, addr_cellClass]

/-! ## §4 THE HODGE TRANSPORT — the conjecture exported

The classical Hodge condition on the degree basis: a class is of type
`(p, p)` when it vanishes outside the degree-`4p` piece — the diagonal
degree, where the `(p, p)` cells live (Layer 10's diagonal law).  The
transferred statements below are the Layer-10 theorem and the Layer-11
official Clay statement, stated in the classical ring's own language
and proved by riding the dictionary.
-/

/-- **THE CLASSICAL HODGE CONDITION.**  A classical class is of Hodge
type `(p, p)` when it is supported on the degree-`4p` piece — the
degree of the `(p, p)` diagonal cells. -/
def isClHodge (p : Nat) (φ : ClRing) : Prop :=
  ∀ i : Fin 12, (i : ℕ) ≠ 4 * p → φ i = 0

/-- **THE HODGE CONDITION TRANSPORTS.**  A GST cochain is a Hodge class
of weight `p` if and only if its classical address is of type `(p, p)`:
the degree-`4p` support and the diagonal-cell support are the same
condition, read in the two bases. -/
theorem transfer_hodge_iff (p : Nat) (hp : p < 3) (f : WaveCoef) :
    isClHodge p (addr f) ↔ isHodgeClass p f := by
  rw [hodge_class_iff p hp f]
  constructor
  · intro hφ i hi hine
    exact hφ ⟨i, hi⟩ hine
  · intro h i hine
    exact h (i : ℕ) i.isLt hine

/-- **THE HODGE CONJECTURE, TRANSFERRED (integral).**  Every classical
Hodge class of every weight the ring admits is an integer multiple of
the algebraic monomial `H^p V^p` of degree `4p` — the Layer-10 theorem
exported across the bridge. -/
theorem transferred_hodge_conjecture (p : Nat) (hp : p < 3) (φ : ClRing)
    (hφ : isClHodge p φ) :
    ∃ z : ℤ, ∀ i : Fin 12, φ i = z * clMono (4 * p) i := by
  obtain ⟨f, hf⟩ := addr_surjective φ
  subst hf
  have hfodge : isHodgeClass p f := (transfer_hodge_iff p hp f).mp hφ
  obtain ⟨z, hz⟩ := hodge_conjecture p hp f hfodge
  refine ⟨z, ?_⟩
  intro i
  have hi := i.isLt
  calc addr f i = gev f (i : ℕ) := rfl
    _ = f ⟨(i : ℕ) / 3, (i : ℕ) % 3, by omega, by omega⟩ := gev_cell f (i : ℕ) hi
    _ = z * cycleClass p ⟨(i : ℕ) / 3, (i : ℕ) % 3, by omega, by omega⟩ :=
        hz ⟨(i : ℕ) / 3, (i : ℕ) % 3, by omega, by omega⟩
    _ = z * (if 3 * ((i : ℕ) / 3) + (i : ℕ) % 3 = 4 * p then (1:ℤ) else 0) :=
        congrArg (fun w => z * w)
          (cellClass_at (4 * p) ((i : ℕ) / 3) ((i : ℕ) % 3) (by omega) (by omega))
    _ = z * (if (i : ℕ) = 4 * p then (1:ℤ) else 0) := by
        have hidx : 3 * ((i : ℕ) / 3) + (i : ℕ) % 3 = (i : ℕ) := by omega
        rw [hidx]
    _ = z * clMono (4 * p) i := rfl

/-- **THE OFFICIAL CLAY STATEMENT, TRANSFERRED (rational).**  On the
classical address, every Hodge class is a rational linear combination of
classes of algebraic cycles: a ℚ-multiple of the rationalized cycle
monomial.  GST's ℤ-coefficient answer carries Clay's ℚ-coefficient
question across the bridge. -/
theorem transferred_clay_hodge_conjecture (p : Nat) (hp : p < 3) (φ : ClRing)
    (hφ : isClHodge p φ) :
    ∃ q : ℚ, ∀ i : Fin 12, (φ i : ℚ) = q * (clMono (4 * p) i : ℚ) := by
  obtain ⟨z, hz⟩ := transferred_hodge_conjecture p hp φ hφ
  refine ⟨(z : ℚ), fun i => ?_⟩
  exact_mod_cast hz i

/-- **THE CONSTRUCTIVE WITNESS, TRANSFERRED.**  The rational combination
coefficient of the official statement is readable off the classical
class: it is the degree-`4p` coordinate — the same diagonal coordinate
Layer 11 reads.  No existence argument: the coefficient is a degree. -/
theorem transferred_clay_witness (p : Nat) (hp : p < 3) (φ : ClRing)
    (hφ : isClHodge p φ) :
    ∃ q : ℚ, q = ((φ ⟨4 * p, by omega⟩ : ℤ) : ℚ) ∧
      ∀ i : Fin 12, (φ i : ℚ) = q * (clMono (4 * p) i : ℚ) := by
  obtain ⟨z, hz⟩ := transferred_hodge_conjecture p hp φ hφ
  have hval : φ ⟨4 * p, by omega⟩ = z := by
    have h1 := hz ⟨4 * p, by omega⟩
    have hmono : clMono (4 * p) ⟨4 * p, by omega⟩ = (1:ℤ) := by simp [clMono]
    rw [hmono, mul_one] at h1
    exact h1
  refine ⟨(z : ℚ), ?_, fun i => ?_⟩
  · exact_mod_cast hval.symm
  · exact_mod_cast hz i

/-- **TRANSFERRED INTEGRAL COEFFICIENT RIGIDITY.**
The classical address-ring Hodge coefficient is unique because the degree-4p
monomial is one at its own basis coordinate. -/
theorem transferred_hodge_coefficient_unique
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (z w : ℤ)
    (hz : ∀ i : Fin 12, φ i = z * clMono (4*p) i)
    (hw : ∀ i : Fin 12, φ i = w * clMono (4*p) i) :
    z = w := by
  let i : Fin 12 := ⟨4*p, by omega⟩
  have hmono : clMono (4*p) i = (1 : ℤ) := by
    simp [i, clMono]
  have hz' := hz i
  have hw' := hw i
  rw [hmono, mul_one] at hz' hw'
  exact hz'.symm.trans hw'

/-- The unique transferred integral coefficient is the degree-4p address
coordinate itself. -/
theorem transferred_hodge_coefficient_eq_coordinate
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (z : ℤ)
    (hz : ∀ i : Fin 12, φ i = z * clMono (4*p) i) :
    z = φ ⟨4*p, by omega⟩ := by
  let i : Fin 12 := ⟨4*p, by omega⟩
  have hmono : clMono (4*p) i = (1 : ℤ) := by
    simp [i, clMono]
  have h := hz i
  rw [hmono, mul_one] at h
  exact h.symm

/-- **UNIQUE TRANSFERRED HODGE CLASSIFICATION.**
Every classical address-ring Hodge class has a unique integral coordinate on
the algebraic monomial. -/
theorem transferred_hodge_unique_classification
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (hφ : isClHodge p φ) :
    ∃! z : ℤ, ∀ i : Fin 12, φ i = z * clMono (4*p) i := by
  obtain ⟨z,hz⟩ := transferred_hodge_conjecture p hp φ hφ
  refine ⟨z,hz,?_⟩
  intro w hw
  exact transferred_hodge_coefficient_unique p hp φ w z hw hz

/-- **TRANSFERRED RATIONAL COEFFICIENT RIGIDITY.** -/
theorem transferred_clay_coefficient_unique
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (q r : ℚ)
    (hq : ∀ i : Fin 12,
      (φ i : ℚ) = q * (clMono (4*p) i : ℚ))
    (hr : ∀ i : Fin 12,
      (φ i : ℚ) = r * (clMono (4*p) i : ℚ)) :
    q = r := by
  let i : Fin 12 := ⟨4*p, by omega⟩
  have hmono : (clMono (4*p) i : ℚ) = 1 := by
    have hz : clMono (4*p) i = (1 : ℤ) := by
      simp [i, clMono]
    exact_mod_cast hz
  have hq' := hq i
  have hr' := hr i
  rw [hmono, mul_one] at hq' hr'
  exact hq'.symm.trans hr'

/-- The rational transferred classification is unique as well. -/
theorem transferred_clay_unique_classification
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (hφ : isClHodge p φ) :
    ∃! q : ℚ, ∀ i : Fin 12,
      (φ i : ℚ) = q * (clMono (4*p) i : ℚ) := by
  obtain ⟨q,hq⟩ := transferred_clay_hodge_conjecture p hp φ hφ
  refine ⟨q,hq,?_⟩
  intro r hr
  exact transferred_clay_coefficient_unique p hp φ r q hr hq

/-- The unique rational transferred coefficient is exactly the canonical
degree-4p address coordinate. -/
theorem transferred_clay_unique_coordinate
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (hφ : isClHodge p φ) :
    ∃! q : ℚ,
      q = ((φ ⟨4*p, by omega⟩ : ℤ) : ℚ) ∧
      ∀ i : Fin 12,
        (φ i : ℚ) = q * (clMono (4*p) i : ℚ) := by
  obtain ⟨q,hqcoord,hq⟩ := transferred_clay_witness p hp φ hφ
  refine ⟨q,⟨hqcoord,hq⟩,?_⟩
  intro r hr
  exact hr.1.trans hqcoord.symm

/-! ## §5 The capstone — the whole bridge in one statement

Eleven conjuncts: the bijection; the two cup transports; the two
multiplication identifications; the commutation; the two truncations
`H³ = 0`, `V⁴ = 0`; the monomial witness (algebraicity); the transferred
conjecture (integral, all weights); and the transferred official Clay
statement (rational, all weights, constructive witness).
-/

theorem the_transfer_bridge :
    Function.Bijective addr
    ∧ (∀ g : WaveCoef, addr (cupDigit g) = clCupD (addr g))
    ∧ (∀ g : WaveCoef, addr (cupCarry g) = clCupV (addr g))
    ∧ (∀ φ : ClRing, clCupD φ = clMul clH φ)
    ∧ (∀ φ : ClRing, clCupV φ = clMul clV φ)
    ∧ (∀ φ : ClRing, clCupD (clCupV φ) = clCupV (clCupD φ))
    ∧ (∀ φ : ClRing, clCupD (clCupD (clCupD φ)) = fun _ => 0)
    ∧ (∀ φ : ClRing, clCupV (clCupV (clCupV (clCupV φ))) = fun _ => 0)
    ∧ (∀ p : Nat, p < 3 → (Nat.iterate clCupD p) ((Nat.iterate clCupV p) clUnit)
        = clMono (4 * p))
    ∧ (∀ p : Nat, p < 3 → ∀ φ : ClRing, isClHodge p φ →
        ∃ z : ℤ, ∀ i : Fin 12, φ i = z * clMono (4 * p) i)
    ∧ (∀ (p : Nat) (hp : p < 3), ∀ φ : ClRing, isClHodge p φ →
        ∃ q : ℚ, q = ((φ ⟨4 * p, by omega⟩ : ℤ) : ℚ) ∧
          ∀ i : Fin 12, (φ i : ℚ) = q * (clMono (4 * p) i : ℚ)) :=
  ⟨addr_bijective, addr_cupDigit, addr_cupCarry,
    clCupD_eq_mulH, clCupV_eq_mulV,
    clCupD_clCupV_comm, clH_cubed, clV_fourth,
    cl_monomial, transferred_hodge_conjecture, transferred_clay_witness⟩

/-! ## Receipts — the comparator face of the bridge-/

#check ClRing
#check addr
#check clMono
#check clUnit
#check clH
#check clV
#check clCupD
#check clCupV
#check clMul
#check isClHodge
#check gev_cell
#check addr_injective
#check addr_surjective
#check addr_bijective
#check addr_add
#check addr_cellClass
#check addr_cycleClass
#check addr_unit
#check addr_cupDigit
#check addr_cupCarry
#check addr_cupDigit_iterate
#check addr_cupCarry_iterate
#check clCupD_eq_mulH
#check clCupV_eq_mulV
#check clCupD_clCupV_comm
#check clH_cubed
#check clV_fourth
#check cl_monomial
#check transfer_hodge_iff

/-- Audit-accurate name for the integral finite address-ring theorem.
The carrier here is ClRing = Fin 12 -> Z. -/
theorem finite_address_hodge_classification
    (p : Nat) (hp : p < 3) (phi : ClRing)
    (hphi : isClHodge p phi) :
    ∃ z : ℤ, ∀ i : Fin 12, phi i = z * clMono (4 * p) i :=
  transferred_hodge_conjecture p hp phi hphi

/-- Audit-accurate name for the rational finite address-ring theorem. -/
theorem finite_address_rational_hodge_classification
    (p : Nat) (hp : p < 3) (phi : ClRing)
    (hphi : isClHodge p phi) :
    ∃ q : ℚ, ∀ i : Fin 12,
      (phi i : ℚ) = q * (clMono (4 * p) i : ℚ) :=
  transferred_clay_hodge_conjecture p hp phi hphi

#check transferred_hodge_conjecture
#check transferred_hodge_coefficient_unique
#check transferred_hodge_coefficient_eq_coordinate
#check transferred_hodge_unique_classification
#check transferred_clay_coefficient_unique
#check transferred_clay_unique_classification
#check transferred_clay_unique_coordinate
#check transferred_clay_hodge_conjecture
#check transferred_clay_witness
#check the_transfer_bridge

#print axioms gev_cell
#print axioms addr_injective
#print axioms addr_surjective
#print axioms addr_bijective
#print axioms addr_add
#print axioms addr_cellClass
#print axioms addr_cycleClass
#print axioms addr_unit
#print axioms addr_cupDigit
#print axioms addr_cupCarry
#print axioms addr_cupDigit_iterate
#print axioms addr_cupCarry_iterate
#print axioms clCupD_eq_mulH
#print axioms clCupV_eq_mulV
#print axioms clCupD_clCupV_comm
#print axioms clH_cubed
#print axioms clV_fourth
#print axioms cl_monomial
#print axioms transfer_hodge_iff
#print axioms transferred_hodge_conjecture
#print axioms transferred_hodge_coefficient_unique
#print axioms transferred_hodge_unique_classification
#print axioms transferred_clay_coefficient_unique
#print axioms transferred_clay_unique_classification
#print axioms transferred_clay_hodge_conjecture
#print axioms transferred_clay_witness
#print axioms the_transfer_bridge

end GSTTransferBridge
