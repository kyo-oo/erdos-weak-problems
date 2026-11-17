import Mathlib
import GSTExactSequenceTorsion

/-!
# GST BOUNDARY BREACH — ROUND 29 LEAN FACE (**DRAFT-NOT-COMPILED**, per SKILL §13)

**STATUS: DRAFT-NOT-COMPILED.** Updated 2026-10-28 at the owner's request;
compilation is intentionally left to the owner. An unverified Lean file is
TEXT, NOT PROOF — it is never claimed as machine-checked, and "it compiles"
is never asserted. The verification ladder for this content is (1) the
adversarially-audited LaTeX derivation
`research/derivations/GST_boundary_breach_round29_2026_11_01.tex`
(0 errors, tectonic), (2) the committed exact-arithmetic certificate
(`research/experiments/boundary_breach_checks.py` — 154 checks, EXIT 0,
deterministic double-run byte-identical; the audit's different-route
recompute `hodge-campaign/audits/audit29_selfaudit_recompute.py` — 10
probes, EXIT 0), and (3) THIS draft, whose value is that it exposes the
logical shape the natural language hides.

**Toolchain steps for an equipped environment** (the repo's own):
`lean-toolchain` is `leanprover/lean4:v4.33.0-rc2` with mathlib
`v4.33.0-rc2`; this module is now registered in `GSTOpenAISourceUpgrade`.
Use `lake build GSTOpenAISourceUpgrade` and
`#print axioms capstone_boundary_breach`.

## What is in this file (PART F of the law stack)

PART F-1 — the |C_4|-torsion law, kernel-level: the cyclic-norm identity
`cycloid_sub_one` ((1+γ+γ²+γ³)∘(γ−1) = γ⁴−1 = 0 — the identity underlying
both the H¹ and the H² four-torsion structure), and the doubling witness
`two_smul_of_norm_sq` (the R1-style 2-torsion witness on a γ² = −1 module:
2v = −(γ−1)((1+γ)v)).

PART F-2 — actual exact-sequence maps and equations, with the
16-bound as the theorem `uniform_kill_of_five_term` (the proof's
arithmetic: 4·(mixed image) = 0 by the |C_4| law; 4c then lies in the
inflation image, itself 4-torsion; 16c = 0), the rational denominator
bound. The five-term cohomology specialization remains an explicit input;
the group-theoretic theorem now proves 16 • c = 0 instead of `True`.

PART F-3 — the honest-invariant dichotomy, kernel-level conditional: the
concentration criterion record (`ConcentrationCriterion`): the mixed-cell
map's injectivity on the post-strip sector given
zero inflation and exactness — the criterion that replaces Round 28's
A^Γ = A idealization (boundary (b)). No field asserts injectivity itself.

PART F-4 — the 2×2 no-go, kernel-level on the explicit quaternion order:
WR² = 1, WI² = −1, WR·WI = WK, WI·WR = −WK (all kernel-provable on the
explicit matrices), and the deck-action mismatch as the labeled statement
(`no_algebra_hom_of_cont`): the computed witness
(CONT W_I)² = +I ≠ −I: the 2×2 content envelope cannot carry the committed
deck — the first computed obstruction datum of the nonabelian boundary (a).

PART F-5 — the equivariant envelope, as the hypothesis-record
(`EquivariantEnvelope`): the rotation lattice's intertwinement
(γ A' γ⁻¹ = −B', γ B' γ⁻¹ = A') and square-zero span are actual equations.
The dressing multiplication law is derived. The 64×64 exact kernel, trace
cross-check
tr(Φ²) = (tr γ²)² = 16, and the complete 4096-cell basis sweep live in the
certificate remain historical receipts, not verification of this revision.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

namespace GSTLawStackRound29

/-! ## PART F-1: the |C_4|-torsion law identities -/

/-- The cyclic-norm identity: for any endomorphism `g` with `g ^ 4 = 1`,
the cyclic norm annihilates the difference: this is the identity underlying
the four-torsion structure of `H^n(C_4; M)` in both degrees (the H^1
relation `im (g - 1) ⊆ ker N` and the H^2 relation `im N ⊆ ker (g - 1)`). -/
theorem cycloid_sub_one {M : Type*} [AddCommGroup M] [Module ℤ M]
    {g : Module.End ℤ M} (hg : g * g * g * g = 1) :
    (1 + g + g * g + g * g * g) * (g - 1) = 0 := by
  have key : (1 + g + g * g + g * g * g) * (g - 1)
      = g * g * g * g - 1 := by
    noncomm_ring
  rw [key, hg]
  simp

/-- The R1-style doubling witness on a `g ^ 2 = -1` module: every element
dies at scale 2 in the difference image. -/
theorem two_smul_of_norm_sq {M : Type*} [AddCommGroup M] [Module ℤ M]
    {g : Module.End ℤ M} (hg2 : g * g = -1) (v : M) :
    (2 : ℤ) • v = -((g - (1 : Module.End ℤ M))) ((1 + g) v) := by
  have h : (g - (1 : Module.End ℤ M)) ((1 + g) v) = (-2 : ℤ) • v := by
    have e : (g - (1 : Module.End ℤ M)) * (1 + g) = g * g - 1 := by noncomm_ring
    rw [← Module.End.mul_apply, e, hg2]
    simp [LinearMap.sub_apply, Module.End.one_apply]
    abel
  rw [h]
  simp

/-! ## PART F-2: the uniform kill (the hypothesis-record composition) -/

/-- Actual abelian-group data for the 16-kill. A particular Hochschild--Serre
sequence must supply these groups, homomorphisms and equations separately.
The theorem no longer replaces this mathematical data by truth-valued labels. -/
structure FiveTermData (A K B : Type*)
    [AddCommGroup A] [AddCommGroup K] [AddCommGroup B] where
  /-- Actual inflation and mixed maps; no cohomology realization is hidden. -/
  inflation : K →+ A
  mix : A →+ B
  exactness : ∀ x, mix x = 0 → ∃ k, inflation k = x
  inflationFourTorsion : ∀ k : K, (4 : ℕ) • k = 0
  mixedFourTorsion : ∀ x, (4 : ℕ) • mix x = 0

/-- **The uniform kill's arithmetic (Round 29's T1).** Given the five-term
exactness and the |C_4|-torsion law (both standard, both gated instance-wise
in the certificate: exponents 2, 4, 4 on the content/glue/trivial modules),
every post-strip two-cell class `c` dies at scale 16:
`4 • (mix c) = 0` (the law) ⟹ `mix (4 • c) = 0` (linearity) ⟹
`4 • c ∈ im(infl)` (exactness) ⟹ `4 • (4 • c) = 0` (the law again) ⟹
`16 • c = 0`. This conclusion applies to every instance of the displayed
data. Geometric existence of such an instance on a general input, and its
comparison with the descent chain, are separate obligations. -/
theorem uniform_kill_of_five_term {A K B : Type*}
    [AddCommGroup A] [AddCommGroup K] [AddCommGroup B]
    (D : FiveTermData A K B) (c : A) : (16 : ℕ) • c = 0 := by
  exact GSTExactSequenceTorsion.sixteen_annihilates
    D.inflation D.mix D.exactness D.inflationFourTorsion D.mixedFourTorsion c

/-! ## PART F-3: the honest-invariant dichotomy (boundary (b)) -/

/-- Actual concentration input: exactness and zero inflation. Identifying
the inflation term with a vanishing cohomology group in a geometric
five-term sequence is an external specialization, not a field of type True. -/
structure ConcentrationCriterion (A K B : Type*)
    [AddCommGroup A] [AddCommGroup K] [AddCommGroup B] where
  data : FiveTermData A K B
  /-- Actual zero inflation, not a truth-valued description of vanishing. -/
  inflation_zero : ∀ k, data.inflation k = 0

/-- Concentration is derived from exactness and zero inflation. -/
theorem ConcentrationCriterion.mixed_injective
    {A K B : Type*} [AddCommGroup A] [AddCommGroup K] [AddCommGroup B]
    (C : ConcentrationCriterion A K B) :
    Function.Injective C.data.mix := by
  exact GSTExactSequenceTorsion.injective_of_zero_inflation
    C.data.inflation C.data.mix C.data.exactness C.inflation_zero

/-! ## PART F-4: the 2×2 no-go (the first computed obstruction of (a)) -/

/-- the quaternion order's generators as explicit 2×2 integer matrices -/
def WR : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
def WI : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]
def WK : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

theorem WR_sq : WR * WR = 1 := by decide
theorem WI_sq : WI * WI = -1 := by decide
theorem WR_WI : WR * WI = WK := by decide
theorem WI_WR : WI * WR = -WK := by decide

/-- the deck action on the content coordinates (α, β) ↦ (β, -α): on the
generators W_R ↦ -W_I, W_I ↦ W_R -/
def CONT : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

/-- **The deck-action mismatch (the 2×2 no-go), the labeled statement.**
The deck's coordinate action is NOT an algebra homomorphism of the
quaternion content order: `CONT (W_I) = W_R` and `W_R ^ 2 = +1` while the
algebra relation demands the image of `W_I ^ 2 = -1` be `-1`. The
certificate gates the witness on the explicit matrices (check 0134) and
the non-innerness (every unit squares to ±1, so every inner automorphism
has order ≤ 2 < 4, check 0135): the 2×2 content envelope cannot carry the
committed deck; the equivariant realization must live at the `H_z` level
(PART F-5). The identities `WR_sq`, `WI_sq`, `WR_WI`, `WI_WR` above are
the kernel content; the full homomorphism-structure statement is the
equipped environment's instantiation target. -/
theorem no_algebra_hom_witness :
    (WR * WR = 1) ∧ (WI * WI = -1) ∧
    -- an algebra homomorphism φ with φ (W_I-content) = WR would give
    -- φ (W_I) ^ 2 = φ (W_I ^ 2) = -1; but WR ^ 2 = +1: contradiction.
    (WR * WR ≠ -1) :=
  ⟨WR_sq, WI_sq, by
    intro h
    rw [WR_sq] at h
    exact absurd h (by decide : (1 : Matrix (Fin 2) (Fin 2) ℤ) ≠ -1)⟩

/-! ## PART F-5: the equivariant envelope (the hypothesis record) -/

/-- The rotation-lattice realization data: the 8-letter level's equivariant
content realization. The 64×64 exact kernel `L = ker (Φ² + 1)` (rank 24),
the trace cross-check `tr (Φ²) = (tr γ²)² = 16`, the intertwinement
`γ A' γ⁻¹ = -B'`, `γ B' γ⁻¹ = A'` for all 24 basis candidates, and the
dressed two-cell identity (the complete 4096-cell basis sweep: 0 failures
— the universal quantifier closed, not sampled) are gated in the
certificate (checks 0136–0144); here the structure is the labeled input. -/
structure EquivariantEnvelope where
  /-- the realization's first leg -/
  A' : Matrix (Fin 8) (Fin 8) ℤ
  /-- the realization's second leg -/
  B' : Matrix (Fin 8) (Fin 8) ℤ
  /-- the intertwinement: γ A' γ⁻¹ = -B' and γ B' γ⁻¹ = A'
  [the certificate's gate 0137] -/
  deck : (Matrix (Fin 8) (Fin 8) ℤ)ˣ
  intertwineA : (deck : Matrix (Fin 8) (Fin 8) ℤ) * A' *
    (↑(deck⁻¹) : Matrix (Fin 8) (Fin 8) ℤ) = -B'
  intertwineB : (deck : Matrix (Fin 8) (Fin 8) ℤ) * B' *
    (↑(deck⁻¹) : Matrix (Fin 8) (Fin 8) ℤ) = A'
  /-- Square zero is a real identity on the realization span.
  It does not claim the whole ambient rotation lattice has square zero. -/
  span_product_zero : ∀ a b c d : ℤ,
    (a • A' + b • B') * (c • A' + d • B') = 0

/-- The multiplicative law is proved from the span identity. -/
theorem EquivariantEnvelope.dressing_add (E : EquivariantEnvelope)
    (a b c d : ℤ) :
    (1 + (a • E.A' + b • E.B')) * (1 + (c • E.A' + d • E.B')) =
      1 + ((a • E.A' + b • E.B') + (c • E.A' + d • E.B')) := by
  rw [add_mul, one_mul, mul_add, mul_one, E.span_product_zero]
  abel

/-! ## Capstone -/

/-- Legacy Round-29 capstone for the cyclic and quaternion identities.
The strengthened F-2/F-3/F-5 conclusions are separately stated and receive
their own axiom-print commands below; they are not hidden in this conjunction. -/
theorem capstone_boundary_breach :
    (∀ {M : Type*} [AddCommGroup M] [Module ℤ M]
      {g : Module.End ℤ M}, g * g * g * g = 1 →
      (1 + g + g * g + g * g * g) * (g - 1) = 0) ∧
    (∀ {M : Type*} [AddCommGroup M] [Module ℤ M]
      {g : Module.End ℤ M}, g * g = -1 → ∀ v : M,
      (2 : ℤ) • v = -((g - (1 : Module.End ℤ M))) ((1 + g) v)) ∧
    (WR * WR = 1) ∧ (WI * WI = -1) ∧ (WR * WI = WK) ∧ (WI * WR = -WK) ∧
    (WR * WR ≠ -1) :=
  ⟨fun h => cycloid_sub_one h, fun h v => two_smul_of_norm_sq h v,
    WR_sq, WI_sq, WR_WI, WI_WR, no_algebra_hom_witness.2.2⟩

#print axioms capstone_boundary_breach
#print axioms uniform_kill_of_five_term
#print axioms ConcentrationCriterion.mixed_injective
#print axioms EquivariantEnvelope.dressing_add

end GSTLawStackRound29
