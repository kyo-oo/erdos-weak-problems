import Mathlib

/-!
# GST GRAPH V2 ONTOLOGICAL FOLD FOR-ALL-N CERTIFICATE (Cycle 3, Strike 1)

Lean shadow of the derivation
`research/derivations/GST_for_all_N_universal_fold_process_reduction_and_ontological_upgrade_2026_10_25.tex`
and the record
`research/records/2026-10-25-gst-for-all-n-universal-fold-process-reduction-and-ontological-upgrade.md`.

## What is certified here (all statements are exact finite algebra or abstract labeled records)

PART A -- the P2 seed witness and the parity obstruction (Theorem P of the derivation):
* `p2_pair_purity_identity`: the literal ch-identity behind the witness pair
  (O(1)+O(1), O(1)+O(-1)): 2*expTr(1) - (expTr(1) + expTr(-1)) = 2*h exactly
  (grade-0 cancels by equal ranks, grade-2 cancels because sinh is odd);
* `int_sq_mod_two`, `list_sq_sum_mod_two`, `p2_scale_even`: the parity obstruction
  x*x % 2 = x % 2, its list-sum form, and the consequence: every witness pair on the
  P2 line-sum model has EVEN scale.

PART B -- the fold-pair calculus and the scale-group laws (Theorems T2/T3/T5 and M
of the derivation), as an abstract labeled record `FoldPairCalculus` whose fields
are the transport laws:
* `mem_zero`, `mem_add`, `mem_neg`, `mem_mul`, `mem_zmul`: the scale set is closed
  under 0, +, negation, and all integer multiples (the additive-subgroup certificate);
* `scaleSet_principal`: IF a positive scale exists THEN there is a least positive
  scale m* that divides every scale (the principal-invariant theorem: the scale set
  is m* * Z or {0}).
The concrete instance `P2PairCal` (line-sum pairs on P2: pairs of sums of line
bundles) instantiates the record with real arithmetic (list sums and lengths);
`p2_bit_fires` exhibits the witness (scale 2); and `p2_mstar_eq_two` is the
DETERMINATION m* = 2 WITHIN THE LINE-SUM CALCULUS INSTANCE (witness + line-sum
parity + principality). SCOPE: the extension of the parity obstruction to ALL
holomorphic pairs on P2 via Chern-lattice integrality (Theorem P(ii) of the
derivation) is derivation-level mathematics and is NOT kernel-checked here.

The graded-character purity laws at the function level: `PureAt`, `pure_sum`,
`pure_neg`, `pure_smul` (purity is preserved under the pair operations), and
`p2_witness_grades` (witness character differences are exactly scale * alpha-grades).

PART C -- the universal pipeline packaging (Theorems U and N(iii) of the derivation),
as abstract labeled records `HodgeWorld` / `FoldProcessOn` whose `landing_cycle`
field is the committed Theorem C + Serre + Thom-Porteous + GAGA chain (clearly
labeled: the classical content is a supplied field per the repo convention):
* `forAllN_landing`: on ANY type of inputs, the single universal bit (every input
  admits a landing witness at nonzero scale) implies the landing conclusion for
  EVERY input simultaneously -- the for-all-N reduction at the logical level;
* `bit_exact_of_no_landing`: the contrapositive companion -- the bit is the exact
  content.

No placeholder stubs, no new axioms; capstones carry `#print axioms`. The classical
integrability/landing content lives ONLY in the labeled record fields and is never
claimed kernel-proven here. GitHub Actions CI (path-filtered workflow) verifies this
file; no local Lean is used or required.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

namespace GSTGraphV2OntologicalFoldForAllN

/-! ## PART A: the P2 seed witness and the parity obstruction -/

/-- Truncated exponential of a line bundle of degree `a` on P2: ch through grade 2
(the grade-2 term is `a^2/2`, the square of the degree). -/
def expTr (a : ℚ) (h : ℚ) : ℚ := 1 + a * h + (a * a / 2) * h ^ 2

/-- **The P2 witness purity identity.** With `h` the hyperplane class, the character
difference of the pair (O(1)+O(1), O(1)+O(-1)) is exactly `2*h`: grade 0 cancels
(ranks 2 = 2), grade 2 cancels (sinh is odd), grade 1 is the scale. This is the
literal identity behind Theorem P(i) of the derivation. -/
theorem p2_pair_purity_identity (h : ℚ) :
    2 * expTr 1 h - (expTr 1 h + expTr (-1) h) = 2 * h := by
  simp only [expTr]
  ring

/-- Squares are themselves modulo two: the parity engine. -/
theorem int_sq_mod_two (x : ℤ) : x * x % 2 = x % 2 := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx
  · rw [Int.mul_emod, hx]
    norm_num
  · rw [Int.mul_emod, hx]
    norm_num

/-- List form: the sum of squares is the sum, modulo two. -/
theorem list_sq_sum_mod_two (L : List ℤ) :
    (L.map (fun x => x * x)).sum % 2 = L.sum % 2 := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.sum_cons,
        Int.add_emod (x * x) ((List.map (fun x => x * x) xs).sum) 2,
        Int.add_emod x xs.sum 2,
        int_sq_mod_two x, ih]

/-- A line-sum pair on P2: multisets of line degrees on the two sides. -/
structure P2Pair where
  A : List ℤ
  B : List ℤ

/-- The scale: grade-1 difference of the character (c1-difference). -/
def p2scale (v : P2Pair) : ℤ := v.A.sum - v.B.sum

/-- The rank difference: grade-0 difference of the character. -/
def p2rank (v : P2Pair) : ℤ := (v.A.length : ℤ) - (v.B.length : ℤ)

/-- The grade-2 difference of the character (half the difference of square sums). -/
def p2grade2 (v : P2Pair) : ℚ :=
  (((v.A.map (fun x => x * x)).sum - (v.B.map (fun x => x * x)).sum : ℤ) : ℚ) / 2

/-- The full graded character difference of the pair (grades >= 3 vanish on P2). -/
def p2grades (v : P2Pair) : ℕ → ℚ
  | 0 => ((p2rank v : ℤ) : ℚ)
  | 1 => ((p2scale v : ℤ) : ℚ)
  | 2 => p2grade2 v
  | (_ + 3) => 0

/-- The landing (purity) condition for a P2 line-sum pair: equal ranks and
vanishing grade-2 difference. Line bundles are holomorphic, so integrability is
automatic on this model. -/
def p2Landing (v : P2Pair) : Prop := p2rank v = 0 ∧ p2grade2 v = 0

/-- The alpha-grades of the line class on P2: concentrated at grade 1. -/
def p2Alpha : ℕ → ℚ := fun k => if k = 1 then 1 else 0

/-- **The parity obstruction (witness-class case).** Every P2 line-sum pair whose
character difference is pure has EVEN scale. -/
theorem p2_scale_even (v : P2Pair) (h : p2Landing v) : p2scale v % 2 = 0 := by
  obtain ⟨-, h2⟩ := h
  have hx : (((v.A.map (fun x => x * x)).sum - (v.B.map (fun x => x * x)).sum : ℤ) : ℚ) = 0 := by
    rw [p2grade2] at h2
    linarith
  have hxi : (v.A.map (fun x => x * x)).sum - (v.B.map (fun x => x * x)).sum = 0 := by
    exact_mod_cast hx
  have hmodA := list_sq_sum_mod_two v.A
  have hmodB := list_sq_sum_mod_two v.B
  show (v.A.sum - v.B.sum) % 2 = 0
  omega

/-- The witness character is exactly scale * alpha-grades: the typed class law. -/
theorem p2_witness_grades (v : P2Pair) (h : p2Landing v) (k : ℕ) :
    p2grades v k = ((p2scale v : ℤ) : ℚ) * p2Alpha k := by
  match k with
  | 0 =>
      show ((p2rank v : ℤ) : ℚ) = ((p2scale v : ℤ) : ℚ) * (if (0 : ℕ) = 1 then 1 else 0)
      rw [if_neg (by omega), h.1]
      norm_num
  | 1 =>
      show ((p2scale v : ℤ) : ℚ) = ((p2scale v : ℤ) : ℚ) * (if (1 : ℕ) = 1 then 1 else 0)
      rw [if_pos rfl]
      ring
  | 2 =>
      show p2grade2 v = ((p2scale v : ℤ) : ℚ) * (if (2 : ℕ) = 1 then 1 else 0)
      rw [if_neg (by omega), h.2]
      ring
  | (k + 3) =>
      show (0 : ℚ) = ((p2scale v : ℤ) : ℚ) * (if (k + 3 : ℕ) = 1 then 1 else 0)
      rw [if_neg (by omega)]
      ring

/-! ## PART B: the abstract fold-pair calculus and the scale-group laws -/

/-- The graded-character purity predicate: support concentrated at grade `p`. -/
def PureAt (p : ℕ) (g : ℕ → ℚ) : Prop := ∀ k, k ≠ p → g k = 0

theorem pure_sum (p : ℕ) (g f : ℕ → ℚ) (hg : PureAt p g) (hf : PureAt p f) :
    PureAt p (fun k => g k + f k) := by
  intro k hk
  show g k + f k = 0
  rw [hg k hk, hf k hk]
  ring

theorem pure_neg (p : ℕ) (g : ℕ → ℚ) (hg : PureAt p g) :
    PureAt p (fun k => -g k) := by
  intro k hk
  show -g k = 0
  rw [hg k hk]
  ring

theorem pure_smul (c : ℚ) (p : ℕ) (alpha g : ℕ → ℚ) (ha : PureAt p alpha)
    (h : ∀ k, g k = c * alpha k) : PureAt p g := by
  intro k hk
  rw [h k, ha k hk]
  ring

/-- **The typed fold-pair calculus** on a type `W` of pair-witnesses. The fields
are the transport laws T2/T3/T5 of the derivation (Theorem T), stated abstractly:
pair-sum adds scales, pair-swap negates scales, the trivial pair has scale zero,
and witnesses transport along sum and swap. These are labeled fields in the repo's
hypothesis-record convention: the geometric content behind them is the committed
derivation, not this file. -/
structure FoldPairCalculus (W : Type) where
  scale : W → ℤ
  isWitness : W → Prop
  pairSum : W → W → W
  pairNeg : W → W
  pairZero : W
  scale_sum : ∀ v w, scale (pairSum v w) = scale v + scale w
  scale_neg : ∀ v, scale (pairNeg v) = -scale v
  scale_zero : scale pairZero = 0
  witness_sum : ∀ v w, isWitness v → isWitness w → isWitness (pairSum v w)
  witness_neg : ∀ v, isWitness v → isWitness (pairNeg v)
  witness_zero : isWitness pairZero

/-- The scale set of a calculus: the scales at which witnesses exist. -/
def ScaleSet {W : Type} (C : FoldPairCalculus W) : Set ℤ :=
  {m | ∃ v, C.isWitness v ∧ C.scale v = m}

theorem mem_zero {W : Type} (C : FoldPairCalculus W) : (0 : ℤ) ∈ ScaleSet C :=
  ⟨C.pairZero, C.witness_zero, C.scale_zero⟩

theorem mem_add {W : Type} (C : FoldPairCalculus W) {m m' : ℤ}
    (hm : m ∈ ScaleSet C) (hm' : m' ∈ ScaleSet C) : m + m' ∈ ScaleSet C := by
  obtain ⟨v, hv, hvm⟩ := hm
  obtain ⟨w, hw, hwm⟩ := hm'
  exact ⟨C.pairSum v w, C.witness_sum v w hv hw, by rw [C.scale_sum, hvm, hwm]⟩

theorem mem_neg {W : Type} (C : FoldPairCalculus W) {m : ℤ}
    (hm : m ∈ ScaleSet C) : -m ∈ ScaleSet C := by
  obtain ⟨v, hv, hvm⟩ := hm
  exact ⟨C.pairNeg v, C.witness_neg v hv, by rw [C.scale_neg, hvm]⟩

theorem mem_mul {W : Type} (C : FoldPairCalculus W) (k : ℕ) {m : ℤ}
    (hm : m ∈ ScaleSet C) : ((k : ℤ)) * m ∈ ScaleSet C := by
  induction k with
  | zero =>
      have h0 : ((0 : ℕ) : ℤ) * m = 0 := by norm_num
      rw [h0]
      exact mem_zero C
  | succ k ih =>
      have hstep : (((k + 1 : ℕ) : ℤ)) * m = ((k : ℕ) : ℤ) * m + m := by
        push_cast
        ring
      rw [hstep]
      exact mem_add C ih hm

theorem mem_zmul {W : Type} (C : FoldPairCalculus W) {m : ℤ}
    (hm : m ∈ ScaleSet C) (k : ℤ) : k * m ∈ ScaleSet C := by
  rcases lt_trichotomy k 0 with hneg | hzero | hpos
  · have h1 : 0 ≤ -k := by omega
    have hn1 := Int.natAbs_of_nonneg h1
    have hn2 : k.natAbs = (-k).natAbs := (Int.natAbs_neg k).symm
    have habs : ((k.natAbs : ℕ) : ℤ) = -k := by omega
    have hbase := mem_mul C k.natAbs hm
    have hrw : k * m = -(((k.natAbs : ℕ) : ℤ) * m) := by
      rw [habs]
      ring
    rw [hrw]
    exact mem_neg C hbase
  · rw [hzero]
    have h0 : (0 : ℤ) * m = 0 := by ring
    rw [h0]
    exact mem_zero C
  · have h1 : 0 ≤ k := by omega
    have habs : ((k.natAbs : ℕ) : ℤ) = k := Int.natAbs_of_nonneg h1
    have hbase := mem_mul C k.natAbs hm
    rw [← habs]
    exact hbase

/-- **Principality of the scale group** (Theorem M(ii) of the derivation): if a
positive scale exists, there is a least positive scale `m*` that divides every
scale. Together with the closure laws, the scale set is `m* * Z` or `{0}`: the
complete per-type content of the bit is ONE nonnegative integer. -/
theorem scaleSet_principal {W : Type} (C : FoldPairCalculus W)
    (hpos : ∃ m, m ∈ ScaleSet C ∧ 0 < m) :
    ∃ mstar : ℤ, 0 < mstar ∧ mstar ∈ ScaleSet C ∧ ∀ m ∈ ScaleSet C, mstar ∣ m := by
  obtain ⟨m₀, hm₀mem, hm₀pos⟩ := hpos
  have h1 : 0 ≤ m₀ := by omega
  have hc0 : ((m₀.natAbs : ℕ) : ℤ) = m₀ := Int.natAbs_of_nonneg h1
  -- the least positive member, by well-ordering (Nat.find; no bounded filter needed)
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ ((k : ℕ) : ℤ) ∈ ScaleSet C :=
    ⟨m₀.natAbs, by omega, by rw [hc0]; exact hm₀mem⟩
  obtain ⟨n, hnpos, hnmemZ, hnmin⟩ : ∃ n : ℕ, 0 < n ∧ ((n : ℕ) : ℤ) ∈ ScaleSet C ∧
      ∀ k : ℕ, 0 < k → ((k : ℕ) : ℤ) ∈ ScaleSet C → n ≤ k :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun k hk0 hkS => Nat.find_min' hex ⟨hk0, hkS⟩⟩
  refine ⟨((n : ℕ) : ℤ), by omega, hnmemZ, ?_⟩
  -- the divisability core, by Nat descent (Nat.div_add_mod; minimality of n)
  have key : ∀ P : ℕ, 0 < P → ((P : ℕ) : ℤ) ∈ ScaleSet C → ((n : ℕ)) ∣ P := by
    intro P hP0 hPS
    obtain ⟨Q, R, hqr, hRsmall⟩ : ∃ Q R : ℕ, P = Q * n + R ∧ R < n := by
      have hdiv := Nat.div_add_mod P n
      refine ⟨P / n, P % n, ?_, ?_⟩
      · rw [Nat.mul_comm]
        exact hdiv.symm
      · exact Nat.mod_lt P (by omega : 0 < n)
    by_cases hR0 : R = 0
    · exact ⟨Q, by rw [Nat.mul_comm]; omega⟩
    · exfalso
      have hqr' : ((P : ℕ) : ℤ) = ((Q : ℕ) : ℤ) * ((n : ℕ) : ℤ) + ((R : ℕ) : ℤ) := by
        exact_mod_cast hqr
      have hRS : ((R : ℕ) : ℤ) ∈ ScaleSet C := by
        have hRcast : ((R : ℕ) : ℤ) = ((P : ℕ) : ℤ) + -(((Q : ℕ) : ℤ) * ((n : ℕ) : ℤ)) := by
          omega
        rw [hRcast]
        exact mem_add C hPS (mem_neg C (mem_zmul C hnmemZ ((Q : ℕ) : ℤ)))
      have hcontr := hnmin R (by omega : 0 < R) hRS
      omega
  intro m hm
  rcases lt_trichotomy m 0 with hneg | hzero | hpp
  · have hmS : -m ∈ ScaleSet C := mem_neg C hm
    have hMc : (((-m).natAbs : ℕ) : ℤ) = -m := Int.natAbs_of_nonneg (by omega)
    have hM0 : 0 < (-m).natAbs := by omega
    have hMS : (((-m).natAbs : ℕ) : ℤ) ∈ ScaleSet C := by rw [hMc]; exact hmS
    obtain ⟨c, hc⟩ := key (-m).natAbs hM0 hMS
    refine ⟨-((c : ℕ) : ℤ), ?_⟩
    have hthis : m = -(((n : ℕ) : ℤ) * ((c : ℕ) : ℤ)) := by omega
    have hcomm : ((n : ℕ) : ℤ) * -(((c : ℕ) : ℤ)) =
        -(((n : ℕ) : ℤ) * ((c : ℕ) : ℤ)) := by ring
    rw [hcomm]
    exact hthis
  · rw [hzero]
    exact dvd_zero _
  · have hMc : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg (by omega)
    have hM0 : 0 < m.natAbs := by omega
    have hMS : ((m.natAbs : ℕ) : ℤ) ∈ ScaleSet C := by rw [hMc]; exact hm
    obtain ⟨c, hc⟩ := key m.natAbs hM0 hMS
    refine ⟨((c : ℕ) : ℤ), ?_⟩
    have h' : ((m.natAbs : ℕ) : ℤ) = ((n : ℕ) : ℤ) * ((c : ℕ) : ℤ) := by
      exact_mod_cast hc
    omega

/-- **The P2 calculus instance**: line-sum pairs with list concatenation as the
pair-sum and component-swap as the pair-swap. All laws are proved by real
arithmetic (list sums and lengths). -/
def P2PairCal : FoldPairCalculus P2Pair where
  scale := p2scale
  isWitness := p2Landing
  pairSum v w := ⟨v.A ++ w.A, v.B ++ w.B⟩
  pairNeg v := ⟨v.B, v.A⟩
  pairZero := ⟨[], []⟩
  scale_sum v w := by
    show (v.A ++ w.A).sum - (v.B ++ w.B).sum = (v.A.sum - v.B.sum) + (w.A.sum - w.B.sum)
    rw [List.sum_append, List.sum_append]
    ring
  scale_neg v := by
    show v.B.sum - v.A.sum = -(v.A.sum - v.B.sum)
    ring
  scale_zero := by
    show ([] : List ℤ).sum - ([] : List ℤ).sum = 0
    simp
  witness_sum v w hv hw := by
    constructor
    · show ((v.A ++ w.A).length : ℤ) - ((v.B ++ w.B).length : ℤ) = 0
      rw [List.length_append, List.length_append]
      push_cast
      have h1 : ((v.A.length : ℤ)) - ((v.B.length : ℤ)) = 0 := hv.1
      have h2 : ((w.A.length : ℤ)) - ((w.B.length : ℤ)) = 0 := hw.1
      omega
    · show p2grade2 ⟨v.A ++ w.A, v.B ++ w.B⟩ = 0
      simp only [p2grade2, List.map_append, List.sum_append]
      push_cast
      have h2 := hv.2
      have h3 := hw.2
      simp only [p2grade2] at h2 h3
      push_cast at h2 h3
      linarith
  witness_neg v hv := by
    constructor
    · show ((v.B.length : ℤ)) - ((v.A.length : ℤ)) = 0
      have h1 : ((v.A.length : ℤ)) - ((v.B.length : ℤ)) = 0 := hv.1
      omega
    · show p2grade2 ⟨v.B, v.A⟩ = 0
      simp only [p2grade2]
      push_cast
      have h2 := hv.2
      simp only [p2grade2] at h2
      push_cast at h2
      linarith
  witness_zero := by
    constructor
    · show (([] : List ℤ).length : ℤ) - (([] : List ℤ).length : ℤ) = 0
      simp
    · show p2grade2 ⟨[], []⟩ = 0
      simp [p2grade2]

/-- **The witness pair data**: (O(1)+O(1), O(1)+O(-1)) as line-degree multisets.
The Int-valued components are decided; the single rational division is closed by
`norm_num` (the raw `decide` cannot reduce the rational-normalization instance). -/
theorem p2witness_rank : (([1, 1] : List ℤ).length : ℤ) - (([1, -1] : List ℤ).length : ℤ) = 0 := by
  decide

theorem p2witness_sqdiff : (([1, 1] : List ℤ).map (fun x => x * x)).sum -
    (([1, -1] : List ℤ).map (fun x => x * x)).sum = 0 := by
  decide

theorem p2grade2_eq_witness :
    p2grade2 ⟨([1, 1] : List ℤ), [1, -1]⟩ = ((((([1, 1] : List ℤ).map (fun x => x * x)).sum - (([1, -1] : List ℤ).map (fun x => x * x)).sum : ℤ) : ℚ) / 2) := rfl

theorem p2witness_landing : p2Landing ⟨([1, 1] : List ℤ), [1, -1]⟩ := by
  constructor
  · exact p2witness_rank
  · show p2grade2 ⟨[1, 1], [1, -1]⟩ = 0
    rw [p2grade2_eq_witness, p2witness_sqdiff]
    norm_num

theorem p2witness_scale : p2scale ⟨([1, 1] : List ℤ), [1, -1]⟩ = 2 := by
  show ([1, 1] : List ℤ).sum - ([1, -1] : List ℤ).sum = 2
  decide

/-- **The bit fires on P2**: the witness pair (O(1)+O(1), O(1)+O(-1)) is a landing
witness at scale 2. -/
theorem p2_bit_fires : ∃ v : P2Pair, p2Landing v ∧ p2scale v ≠ 0 := by
  refine ⟨⟨[1, 1], [1, -1]⟩, p2witness_landing, ?_⟩
  show ([1, 1] : List ℤ).sum - ([1, -1] : List ℤ).sum ≠ 0
  decide

/-- **The determination m* = 2 within the line-sum pair calculus instance P2PairCal**
(the witness bounds it by 2; the line-sum parity obstruction forces evenness;
principality gives the least positive scale): m* = 2. The derivation's Theorem P
extends this to ALL holomorphic pairs on P2 by Chern-lattice integrality, which is
NOT kernel-checked in this file. -/
theorem p2_mstar_eq_two :
    ∃ mstar : ℤ, 0 < mstar ∧ mstar ∈ ScaleSet P2PairCal ∧
      (∀ m ∈ ScaleSet P2PairCal, mstar ∣ m) ∧ mstar = 2 := by
  have h2mem : (2 : ℤ) ∈ ScaleSet P2PairCal := ⟨⟨[1, 1], [1, -1]⟩, p2witness_landing, p2witness_scale⟩
  obtain ⟨mstar, hstarpos, hstarmem, hstardiv⟩ :=
    scaleSet_principal P2PairCal ⟨2, h2mem, by norm_num⟩
  have hstar := hstarmem
  obtain ⟨v, hv, hvm⟩ := hstar
  have hpar : p2scale v % 2 = 0 := p2_scale_even v hv
  have hvm' : p2scale v = mstar := hvm
  obtain ⟨q, hq⟩ := hstardiv 2 h2mem
  have hle : mstar ≤ 2 := Int.le_of_dvd (by norm_num) ⟨q, hq⟩
  refine ⟨mstar, hstarpos, hstarmem, hstardiv, ?_⟩
  omega

/-! ## PART C: the universal pipeline packaging (for-all-N) -/

/-- One typed input world: abstract class layer, cycle layer, the canonical class
map, the input class alpha, and the codimension/dimension data. -/
structure HodgeWorld where
  Cl : Type
  Cyc : Type
  cl : Cyc → Cl
  alpha : Cl
  p : ℕ
  d : ℕ

/-- **The universal fold-process record** on a world. The `landing_cycle` field is
the committed landing chain (Theorem C + Serre generation + Thom-Porteous + GAGA of
the cycle-1 dossier), supplied as a labeled field in the repo's hypothesis-record
convention: an integrable pure pair at nonzero scale yields a cycle whose canonical
class is exactly alpha. The kernel content of THIS file is the packaging below, not
the classical chain. -/
structure FoldProcessOn (w : HodgeWorld) where
  PairWit : Type
  scale : PairWit → ℤ
  landing : PairWit → Prop
  landing_cycle : ∀ v : PairWit, landing v → scale v ≠ 0 →
    ∃ Z : w.Cyc, w.cl Z = w.alpha

/-- **THE FOR-ALL-N PACKAGING.** On ANY type of inputs with ANY family of
fold-process records: if the single universal bit fires on every input (each admits
a landing witness at nonzero scale), then the landing conclusion holds for EVERY
input simultaneously. This is the logical form of the collapse
HC ⟸ FS_forall (Theorem N(iii) of the derivation). -/
theorem forAllN_landing {Idx : Type} (W : Idx → HodgeWorld)
    (P : ∀ i, FoldProcessOn (W i))
    (hbit : ∀ i, ∃ v : (P i).PairWit, (P i).landing v ∧ (P i).scale v ≠ 0) :
    ∀ i, ∃ Z : (W i).Cyc, (W i).cl Z = (W i).alpha := by
  intro i
  obtain ⟨v, hv, hm⟩ := hbit i
  exact (P i).landing_cycle v hv hm

/-- **The bit is the exact content** (contrapositive companion): if some input has
no landing, then the universal bit fails somewhere. -/
theorem bit_exact_of_no_landing {Idx : Type} (W : Idx → HodgeWorld)
    (P : ∀ i, FoldProcessOn (W i)) (i : Idx)
    (hno : ¬∃ Z : (W i).Cyc, (W i).cl Z = (W i).alpha) :
    ¬∀ i, ∃ v : (P i).PairWit, (P i).landing v ∧ (P i).scale v ≠ 0 := by
  intro hbit
  exact hno (forAllN_landing W P hbit i)

/-! ## Capstones -/

/-- Capstone A: the P2 determination package (witness + parity + principality at
the instance + the typed class law). -/
theorem capstone_A :
    (∃ v : P2Pair, p2Landing v ∧ p2scale v ≠ 0) ∧
    (∀ v : P2Pair, p2Landing v → p2scale v % 2 = 0) ∧
    (∃ mstar : ℤ, 0 < mstar ∧ mstar ∈ ScaleSet P2PairCal ∧
      (∀ m ∈ ScaleSet P2PairCal, mstar ∣ m) ∧ mstar = 2) ∧
    (∀ v : P2Pair, p2Landing v → ∀ k, p2grades v k =
      ((p2scale v : ℤ) : ℚ) * p2Alpha k) :=
  ⟨p2_bit_fires, fun v hv => p2_scale_even v hv, p2_mstar_eq_two,
    fun v hv k => p2_witness_grades v hv k⟩

/-- Capstone B: the for-all-N packaging and its contrapositive companion. -/
theorem capstone_B :
    (∀ (Idx : Type) (W : Idx → HodgeWorld) (P : ∀ i, FoldProcessOn (W i)),
      (∀ i, ∃ v : (P i).PairWit, (P i).landing v ∧ (P i).scale v ≠ 0) →
        ∀ i, ∃ Z : (W i).Cyc, (W i).cl Z = (W i).alpha) ∧
    (∀ (Idx : Type) (W : Idx → HodgeWorld) (P : ∀ i, FoldProcessOn (W i)) (i : Idx),
      (¬∃ Z : (W i).Cyc, (W i).cl Z = (W i).alpha) →
        ¬∀ i, ∃ v : (P i).PairWit, (P i).landing v ∧ (P i).scale v ≠ 0) :=
  ⟨fun _ w p h => forAllN_landing w p h,
    fun _ w p i hno => bit_exact_of_no_landing w p i hno⟩

/-- Capstone C: the scale-group laws (closure under 0, +, negation, integer
multiples; principality when a positive scale exists). -/
theorem capstone_C :
    ∀ (W : Type) (C : FoldPairCalculus W),
      (0 : ℤ) ∈ ScaleSet C ∧
      (∀ m m', m ∈ ScaleSet C → m' ∈ ScaleSet C → m + m' ∈ ScaleSet C) ∧
      (∀ m, m ∈ ScaleSet C → -m ∈ ScaleSet C) ∧
      (∀ m, m ∈ ScaleSet C → ∀ k : ℤ, k * m ∈ ScaleSet C) ∧
      ((∃ m, m ∈ ScaleSet C ∧ 0 < m) →
        ∃ mstar : ℤ, 0 < mstar ∧ mstar ∈ ScaleSet C ∧
          ∀ m ∈ ScaleSet C, mstar ∣ m) :=
  fun _ C => ⟨mem_zero C, fun _ _ hm hm' => mem_add C hm hm',
    fun _ hm => mem_neg C hm, fun _ hm k => mem_zmul C hm k,
    fun h => scaleSet_principal C h⟩

#print axioms p2_pair_purity_identity
#print axioms int_sq_mod_two
#print axioms p2_scale_even
#print axioms p2_mstar_eq_two
#print axioms capstone_A
#print axioms capstone_B
#print axioms capstone_C

end GSTGraphV2OntologicalFoldForAllN
