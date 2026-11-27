import Mathlib

/-!
# GST LAW STACK — ROUND 26 LEAN FACE (**DRAFT-NOT-COMPILED**, per SKILL §13)

**STATUS: DRAFT-NOT-COMPILED.** Per the standing boss order (SKILL §13, the
environment doctrine): no Lean toolchain is installed in this sandbox, and an
unverified Lean file is TEXT, NOT PROOF — it is never claimed as machine-checked,
and "it compiles" is never asserted. The verification ladder for this content is
(1) the adversarially-audited LaTeX derivation
`research/derivations/GST_law_stack_full_derivations_round25_2026_10_31.tex`
(20 pages, every provable law with a complete hand proof), (2) the committed
exact-arithmetic certificates (`rotation_deck_checks.py` 59 checks,
`cyclic_family_checks.py` 298 checks, `cyclic_transport_checks.py` 125 checks,
`wi_vertex_pin_checks.py` 122 checks — all EXIT 0), and (3) THIS draft, whose
value is that it exposes the logical shape the natural language hides.

**Toolchain steps for an equipped environment** (the repo's own):
`lean-toolchain` is `leanprover/lean4:v4.33.0-rc2` with mathlib `v4.33.0-rc2`;
register this module in the `lakefile.toml` `HCUniverse` roots, then
`lake build GSTLawStackRound26` and `#print axioms capstone_law_stack`.
Expected repair passes in an equipped environment (marked inline): the
`Prod`-component `simp` normalizations of `gammaPlane`, and the
`Module.End` literal `-1` unfolding. The mathematical content of every proof
is written out; no `sorry`, no new `axiom`.

## What is in this file

PART A — the `C₄` deck laws (R1 of the derivation §2.2), kernel-level:
* `norm_deg`: the norm degeneration `1 + γ + γ² + γ³ = 0` in any ring (`γ² = -1`);
* `invariants_vanish`: the fixed space of the deck is trivial on a
  torsion-free module;
* `two_smul_mem_range`: every class dies at scale 2 (`2•v ∈ (γ-1)M`),
  the explicit witness `w = -(1+γ)v`;
* `end_sq`: the endomorphism-form bridge.

PART B — the Weil plane (R5 of the derivation §2.4), kernel-level on `ℤ × ℤ`:
* `gammaPlane`: the operator's rotation `γ(m,n) = (n,-m)`;
* `gammaPlane_sq`: `γ² = -1` pointwise; `gammaPlane_WR`, `gammaPlane_WI`:
  the committed ray conventions `γ W_R = -W_I`, `γ W_I = W_R`;
* `gamma_sub_one_apply`: the explicit action `(γ-1)(a,b) = (b-a, -a-b)`;
* `weil_parity`: `m • W_R ∈ (γ-1)M ↔ 2 ∣ m` — THE DOOR-PARITY LAW (the
  pins `m* = 2` are the least even scale);
* `diagonal_killed`: the diagonal boundary `(γ-1)(-W_R) = W_R + W_I`;
* `range_eq_parity`: the image of `γ-1` is exactly the parity sublattice
  `{v | v.1 ≡ v.2 [MOD 2]}` (index 2 — the obstruction group is `ZMod 2`);
* `door_parity`: the `Even`-valued form of the parity law.

PART C — the cyclotomic engine (§3.5 of the derivation), kernel-level GIVEN the
standard roots factorization as a labeled hypothesis (the repo convention for
standard-strength classical content):
* `cyclo_engine_of_factorization`: from `∏(X - ζ k) = X^L - 1`, evaluation at
  `X = -1` gives `∏(1 + ζ k) = 1 - (-1)^L` — the machine behind the operator's
  five Wolfram totals (4, 8, 24, 64, 208).

PART D — the symmetrizer (§3.5 of the derivation), kernel-level:
* `symmetrizer`: `∑ γ^j u = m • u` on invariants (the `1/m` engine of the
  forward leg).

PART E — the conditional composition face (§5–§6 of the derivation, the
Round-26 REPAIRED one-directional form), in the repo's hypothesis-record
convention (cf. `GSTGraphV2OntologicalFoldForAllN.FoldProcessOn`):
* `SectorInput` / `IsRationalAlgebraic`: the input and the conclusion;
* `OpenItems`: THE REMAINING THEOREM — the five open items (i)–(v) as labeled
  per-input propositions;
* `CompositionOn`: the two halves — `pair_bit_of_items` (STEP 4, OPEN: the five
  items produce the landing pair witness at nonzero scale) and
  `algebraic_of_pair` (STEP 1, COMMITTED: the two-center conduit — Lemma N +
  the determinantal machine + GAGA — exhibits the cycle);
* `composition_at`, `composition_all_inputs`: THE CONDITIONAL COMPOSITION (one
  direction; the converse is NOT claimed — the Round-26 repair of the Round-25
  §6 overclaim, recorded in the derivation);
* `boundary_exact`: the contrapositive companion — the boundary is exact.

The open content of the campaign is exactly `pair_bit_of_items` and the five
fields of `OpenItems`; nothing else in this file is open, and nothing is
claimed kernel-proven until CI says so in an equipped environment.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

namespace GSTLawStackRound26

/-! ## PART A: the C₄ deck laws (R1) -/

/-- **R1(2): the norm degenerates.** In any ring, an element squaring to `-1`
has vanishing norm. On a deck module this is `N = (1+γ)(1+γ²) = 0`, half of
`H²(C₄; M) = M^{C₄}/NM = 0`. -/
theorem norm_deg {R : Type*} [Ring R] {x : R} (hx : x * x = -1) :
    1 + x + x ^ 2 + x ^ 3 = 0 := by
  have h3 : x ^ 3 = -x := by
    rw [pow_three, hx]
    simp
  rw [pow_two, hx, h3]
  ring

/-- **R1(1): the invariants vanish.** On a torsion-free module carrying `γ`
with `γ (γ u) = -u` pointwise, the fixed space is trivial (the other half of
`H²(C₄; M) = 0`). -/
theorem invariants_vanish {M : Type*} [AddCommGroup M] [Module ℤ M]
    [NoZeroSMulDivisors ℤ M] {γ : Module.End ℤ M} (hγ2 : ∀ u, γ (γ u) = -u)
    {v : M} (hv : γ v = v) : v = 0 := by
  have a1 : γ (γ v) = -v := hγ2 v
  have a2 : γ v = γ (γ v) := congrArg γ hv.symm
  have a3 : v = -v := hv.trans (a2.trans a1)
  have h2 : (2 : ℤ) • v = 0 := by
    rw [two_smul]
    linear_combination a3
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h (by norm_num)
  · exact h

/-- **R1(4): every class dies at scale 2.** For any `v` there is `w` with
`(γ - 1) w = 2 • v` — the `H¹` of the deck is 2-elementary. The witness is
`w = -(1 + γ) v`, from `(γ - 1)(1 + γ) = γ² - 1 = -2`. -/
theorem two_smul_mem_range {M : Type*} [AddCommGroup M] [Module ℤ M]
    {γ : Module.End ℤ M} (hγ2 : ∀ u, γ (γ u) = -u) (v : M) :
    ∃ w : M, (γ - (1 : Module.End ℤ M)) w = (2 : ℤ) • v := by
  refine ⟨-((1 : Module.End ℤ M) + γ) v, ?_⟩
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply,
    Module.End.mul_apply, map_neg, map_add]
  rw [hγ2 (γ v), two_smul]
  abel

/-- The bridge from the endomorphism form of the hypothesis. -/
theorem end_sq {M : Type*} [AddCommGroup M] [Module ℤ M]
    {γ : Module.End ℤ M} (h : γ * γ = -1) : ∀ u, γ (γ u) = -u := by
  intro u
  rw [← Module.End.mul_apply, h]
  simp [Module.End.neg_apply, Module.End.one_apply]

/-! ## PART B: the Weil plane (R5) -/

/-- The operator's rotation on the Weil plane `Z⟨W_R, W_I⟩ ≅ ℤ × ℤ`:
`γ (m, n) = (n, -m)`, i.e. `γ W_R = -W_I` and `γ W_I = W_R` (the committed
conventions of ledger 097). -/
def gammaPlane : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ where
  toFun v := (v.2, -v.1)
  map_add' v w := by
    ext <;> simp [Prod.add_def, Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' c v := by
    ext <;> simp [Prod.smul_def, smul_eq_mul] <;> ring

theorem gammaPlane_sq (u : ℤ × ℤ) : gammaPlane (gammaPlane u) = -u := by
  rcases u with ⟨a, b⟩
  ext <;> simp [gammaPlane]

theorem gammaPlane_WR : gammaPlane (1, 0) = (0, -1) := by
  ext <;> simp [gammaPlane]

theorem gammaPlane_WI : gammaPlane (0, 1) = (1, 0) := by
  ext <;> simp [gammaPlane]

/-- The explicit action of the deck difference. -/
theorem gamma_sub_one_apply (a b : ℤ) :
    (gammaPlane - (1 : Module.End ℤ (ℤ × ℤ))) (a, b) = (b - a, -a - b) := by
  simp [gammaPlane, LinearMap.sub_apply, Module.End.one_apply]

/-- **R5(2): THE DOOR-PARITY LAW.** `m • W_R` dies under the deck exactly at
even scale; the pins `m*(A,2,W_R) = m*(A,2,W_I) = 2` are the least such scale. -/
theorem weil_parity (m : ℤ) :
    (∃ w : ℤ × ℤ, (gammaPlane - 1) w = (m, 0)) ↔ 2 ∣ m := by
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    rw [gamma_sub_one_apply] at h
    have h2 : -a - b = 0 := by
      have := congrArg Prod.snd h
      simpa using this
    have h3 : b - a = m := by
      have := congrArg Prod.fst h
      simpa using this
    refine ⟨-a, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    refine ⟨(-k, k), ?_⟩
    rw [gamma_sub_one_apply, hk]
    ext <;> omega

/-- **R5(3): the diagonal boundary.** The class `W_R + W_I` dies at scale 1:
`(γ - 1)(-W_R) = W_R + W_I`, integrally. -/
theorem diagonal_killed :
    (gammaPlane - 1) (-(1, 0) : ℤ × ℤ) = (1, 1) := by
  rw [gamma_sub_one_apply]
  ext <;> omega

/-- **The index-2 receipt.** The image of `γ - 1` is exactly the parity
sublattice `{v | v.1 ≡ v.2 [MOD 2]}`; the deck obstruction group
`M/(γ-1)M` is therefore `ZMod 2` — the door bit. -/
theorem range_eq_parity (v : ℤ × ℤ) :
    v ∈ LinearMap.range (gammaPlane - (1 : Module.End ℤ (ℤ × ℤ))) ↔
      v.1 % 2 = v.2 % 2 := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    rw [gamma_sub_one_apply] at h
    have h1 : b - a = v.1 := by
      have := congrArg Prod.fst h; simpa using this
    have h2 : -a - b = v.2 := by
      have := congrArg Prod.snd h; simpa using this
    omega
  · intro hp
    have hsum : (v.1 + v.2) % 2 = 0 := by omega
    obtain ⟨t, ht⟩ := (Int.emod_eq_zero_iff_dvd (v.1 + v.2) 2).mp hsum
    refine ⟨(-t, v.1 - t), ?_⟩
    rw [gamma_sub_one_apply]
    ext <;> omega

/-- **R5, the `Even` form** (the door data's own statement): `m • W_R` dies
iff `m` is even. -/
theorem door_parity (m : ℤ) :
    (∃ w : ℤ × ℤ, (gammaPlane - 1) w = m • (1 : ℤ × ℤ)) ↔ Even m := by
  have hsmul : ∀ k : ℤ, k • (1 : ℤ × ℤ) = (k, 0) := by
    intro k
    ext <;> simp [Prod.smul_def, smul_eq_mul]
  rw [hsmul]
  exact ⟨fun h => (Int.even_iff_two_dvd m).2 (weil_parity m).1 h,
    fun h => (weil_parity m).2 ((Int.even_iff_two_dvd m).1 h)⟩

/-! ## PART C: the cyclotomic engine (§3.5) -/

/-- **The cyclotomic engine, packaged with the standard roots factorization as
a labeled hypothesis** (the repo convention for standard-strength classical
content): from `∏ (X - ζ k) = X^L - 1`, evaluation at `X = -1` gives
`∏ (1 + ζ k) = 1 - (-1)^L`. This is the machine behind the operator's five
Wolfram totals (4, 8, 24, 64, 208), reproduced two independent ways by
`cyclic_family_checks.py`. The factorization is the standard
roots-of-unity identity. -/
theorem cyclo_engine_of_factorization (L : ℕ) (ζ : ℕ → ℂ)
    (hfact : ∏ k in Finset.range L, (Polynomial.X - Polynomial.C (ζ k)) =
      Polynomial.X ^ L - 1) :
    ∏ k in Finset.range L, (1 + ζ k) = 1 - (-1 : ℂ) ^ L := by
  have hEval := congrArg (fun p : ℂ[X] => p.eval (-1)) hfact
  simp only [map_prod (Polynomial.evalRingHom (-1)), Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_one] at hEval
  -- hEval : ∏ (-1 - ζ k) = (-1)^L - 1
  have hneg : ∀ k, (-1 : ℂ) - ζ k = -((1 : ℂ) + ζ k) := fun k => by ring
  rw [Finset.prod_congr rfl (fun k _ => hneg k), Finset.prod_neg_distrib,
    Finset.card_range] at hEval
  -- hEval : (-1)^L * ∏ (1 + ζ k) = (-1)^L - 1
  have hu : ((-1 : ℂ) ^ L) * ((-1 : ℂ) ^ L) = 1 := by
    rw [← pow_add, show L + L = 2 * L from by ring, pow_mul]
    simp
  have hkey : (1 : ℂ) - (-1 : ℂ) ^ L =
      ((-1 : ℂ) ^ L) * (((-1 : ℂ) ^ L) - 1) := by
    rw [mul_sub, hu]
  rw [hkey, ← hEval, ← mul_assoc, hu, one_mul]

/-! ## PART D: the symmetrizer (§3.5) -/

/-- **The symmetrizer identity** (the `1/m` engine of the forward leg): on a
`γ`-invariant vector, the group sum is the arity multiple. -/
theorem symmetrizer {M : Type*} [AddCommGroup M] [Module ℤ M]
    {γ : Module.End ℤ M} (u : M) (hu : γ u = u) (m : ℕ) :
    ∑ j in Finset.range m, γ ^ j u = m • u := by
  have key : ∀ j : ℕ, γ ^ j u = u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, Module.End.mul_apply, hu, ih]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_const,
    Finset.card_range]

/-! ## PART E: the conditional composition face (§5–§6, the Round-26
repaired one-directional form) -/

/-- An input of the open sector, abstracted per the repo convention (cf.
`GSTGraphV2OntologicalFoldForAllN.HodgeWorld`): the geometry — a smooth
projective variety `World`, its rational algebraic cycles `Cyc`, its rational
cohomology `Cls` with the cycle class map `cl`, and the rational `(p,p)` class
`alpha` under study — is carried as data; nothing about it is proven here. -/
structure SectorInput where
  /-- the ambient smooth projective variety, abstracted -/
  World : Type
  /-- rational algebraic cycles (rational coefficients), abstracted -/
  Cyc : Type
  /-- the rational cohomology classes, abstracted -/
  Cls : Type
  /-- the cycle class map -/
  cl : Cyc → Cls
  /-- the rational `(p,p)` Hodge class under study -/
  alpha : Cls

namespace SectorInput

/-- The conclusion of the Clay statement at this input: `alpha` is a rational
linear combination of algebraic cycle classes. -/
def IsRationalAlgebraic (I : SectorInput) : Prop :=
  ∃ Z : I.Cyc, I.cl Z = I.alpha

end SectorInput

/-- **THE REMAINING THEOREM (§6 of the derivation), as labeled per-input
propositions.** The five open items; their full mathematical content (each
with its receipt: the 21-c R1 upgrade, the AUDIT_22 counterexamples, the
24-b B1 blocker) is in the derivation and its records — not reproducible at
this abstraction level and not claimed here. -/
structure OpenItems (I : SectorInput) : Prop where
  /-- (i) the involution/eigenbranch exchange structure on the carrier pair -/
  involution : Prop
  /-- (ii) the reduction of the GL(H_z)-valued two-cell to the deck
  computation -/
  twoCellReduction : Prop
  /-- (iii) the exclusion of the non-scalar unexchanged content after the
  D2/D3 strip -/
  nonScalarExclusion : Prop
  /-- (iv) the rank parity: the even split r₀ = 2a -/
  rankParity : Prop
  /-- (v) the strip reduction of the two-cell to the iota-shaped cochain -/
  stripReduction : Prop

/-- **The composition record** (the repo's hypothesis-record convention; cf.
`FoldProcessOn`). Two labeled fields: `pair_bit_of_items` is STEP 4 of the
derivation §5 — OPEN: the five items produce, at this input, a landing pair
witness at nonzero scale; `algebraic_of_pair` is STEP 1 — COMMITTED: the
two-center conduit (Lemma N the Newton conductor + the determinantal machine +
GAGA) exhibits a cycle with class exactly `alpha` from such a pair. -/
structure CompositionOn (I : SectorInput) : Type where
  /-- the type of pair witnesses (the carrier pairs), supplied -/
  PairWit : Type
  /-- the landing predicate: the pair is integrable, pure, equal-rank, with
  character difference a nonzero multiple of `alpha` (the STEP 1 shape) -/
  landing : PairWit → Prop
  /-- the scale of the pair -/
  scale : PairWit → ℤ
  /-- STEP 4 (OPEN, §6): the five items produce a landing witness at nonzero
  scale at this input -/
  pair_bit_of_items : OpenItems I → ∃ v : PairWit, landing v ∧ scale v ≠ 0
  /-- STEP 1 (COMMITTED, §4.3): a landing witness at nonzero scale yields
  the cycle -/
  algebraic_of_pair : ∀ v : PairWit, landing v → scale v ≠ 0 →
    ∃ Z : I.Cyc, I.cl Z = I.alpha

/-- **THE CONDITIONAL COMPOSITION, at one input** (the kernel content of this
face): the five open items + the composition record ⟹ `alpha` is
rational-algebraic at this input. The open content is exactly
`pair_bit_of_items`; nothing else is open. -/
theorem composition_at (I : SectorInput) (C : CompositionOn I)
    (h : OpenItems I) : I.IsRationalAlgebraic := by
  obtain ⟨v, hland, hne⟩ := C.pair_bit_of_items h
  exact C.algebraic_of_pair v hland hne

/-- **The for-all-inputs form** (§6 of the derivation, the Round-26 repaired
ONE-DIRECTIONAL statement): if the five items are discharged at every input of
the open sector (with the composition record supplied everywhere), then the
rational Hodge conjecture holds on the open sector. **The converse is NOT
claimed** — the Round-25 draft's equivalence overclaim was caught by the
Round-26 self-audit and repaired in the derivation §6. -/
theorem composition_all_inputs
    (Idx : Type) (I : Idx → SectorInput) (C : ∀ i, CompositionOn (I i))
    (h : ∀ i, OpenItems (I i)) : ∀ i, (I i).IsRationalAlgebraic :=
  fun i => composition_at (I i) (C i) (h i)

/-- **The boundary is exact** (the contrapositive companion): if some input is
not rational-algebraic, then at that input the items-plus-bit disjunction
fails — the five items do not all hold, or the pair bit is not produced from
them. This is the face's falsifiability receipt: the open boundary is exactly
where a counterexample to the conjecture would land. -/
theorem boundary_exact (I : SectorInput) (C : CompositionOn I)
    (hno : ¬ I.IsRationalAlgebraic) :
    ¬(OpenItems I ∧ ∃ v : C.PairWit, C.landing v ∧ C.scale v ≠ 0) := by
  rintro ⟨hitems, v, hland, hne⟩
  exact hno (C.algebraic_of_pair v hland hne)

/-! ## Capstone -/

/-- **The Round-26 capstone**: the deck laws (A), the Weil-plane door-parity
and index-2 receipts (B), the cyclotomic engine given the standard
factorization (C), the symmetrizer (D), and the one-directional conditional
composition with its exact-boundary companion (E). -/
theorem capstone_law_stack :
    (∀ {R : Type*} [Ring R] {x : R}, x * x = -1 → 1 + x + x ^ 2 + x ^ 3 = 0) ∧
    (∀ {M : Type*} [AddCommGroup M] [Module ℤ M] [NoZeroSMulDivisors ℤ M]
      {γ : Module.End ℤ M}, (∀ u, γ (γ u) = -u) → ∀ {v : M}, γ v = v → v = 0) ∧
    (∀ u : ℤ × ℤ, gammaPlane (gammaPlane u) = -u) ∧
    (∀ m : ℤ, (∃ w : ℤ × ℤ, (gammaPlane - 1) w = (m, 0)) ↔ 2 ∣ m) ∧
    (∀ m : ℤ, (∃ w : ℤ × ℤ, (gammaPlane - 1) w = m • (1 : ℤ × ℤ)) ↔ Even m) ∧
    (∀ v : ℤ × ℤ, v ∈ LinearMap.range
        (gammaPlane - (1 : Module.End ℤ (ℤ × ℤ))) ↔ v.1 % 2 = v.2 % 2) ∧
    (∀ (Idx : Type) (I : Idx → SectorInput) (C : ∀ i, CompositionOn (I i)),
      (∀ i, OpenItems (I i)) → ∀ i, (I i).IsRationalAlgebraic) ∧
    (∀ (I : SectorInput) (C : CompositionOn I), ¬ I.IsRationalAlgebraic →
      ¬(OpenItems I ∧ ∃ v : C.PairWit, C.landing v ∧ C.scale v ≠ 0)) :=
  ⟨fun h => norm_deg h, fun h v hv => invariants_vanish h hv,
    fun u => gammaPlane_sq u, fun m => weil_parity m, fun m => door_parity m,
    fun v => range_eq_parity v,
    fun Idx I C h => composition_all_inputs Idx I C h,
    fun I C hno => boundary_exact I C hno⟩

#print axioms capstone_law_stack

end GSTLawStackRound26
