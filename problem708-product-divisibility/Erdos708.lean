import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdos708 — THE PRODUCT-DIVISIBILITY WINDOW KERNEL (Kernel 62, #708)

## THE PROBLEM (the engine's exact formulation, `engine708.py`)

> g(n) = min g such that for ANY A (|A|=n, A subset [2,inf)) and ANY
> interval I of max(A) consecutive integers, exists B in I, |B|=g,
> prod(A) | prod(B).  (Erdos $100, ErSu59; known g(2)=2, g(3)=4.)

The engine computes, for fixed A and interval start t, the exact min |B|
over subsets B of I_t = {t+1, ..., t+max(A)} with prod(A) | prod(B)
(distinct elements, no repeats — `itertools.combinations` semantics,
t = 1..40).  Engine-certified worst-over-t rows (run output):

    A=[2,3]: 2   A=[6,10,15]: 3   A=[2,3,5]: 3   A=[6,10,14,15]: 4
    A=[6,10,15,21]: 4   A=[2,3,5,7]: 3   A=[6,10,14,15,21]: 5
    A=[6,10,14,15,21,35]: 5   (hard windows t=1 except A=[2,3,5]: t=24)

## WHAT THIS KERNEL PROVES (complete unconditional theorems)

1. **THE PREDICATE LAWS** (`e708_prod_append`, `e708_superset_law`,
   `e708_composition_law`, `e708_refine_law`): the divisibility/product
   predicate's closure and composition structure, in FULL generality —
   the append-product law; the superset law (any extension of a covering
   B covers: the "pad to exactly g" engine room); the composition law
   (covers of A1 by B1 and of A2 by B2 compose to A1++A2 by B1++B2);
   the demand-refinement law (weaker demands inherit covers, dvd_trans).
2. **THE ENUMERATOR DUALITY** (`e708_enum_sound`, `e708_enum_complete`):
   the budgeted subset enumerator `coverFrom P l k acc = true` iff there
   exists a cell-selection B (the `sub708` inductive: the engine's
   combinations semantics, in interval order) of size <= k with
   P | acc * prod B — both directions, full generality, zero hypotheses
   on P, l, k, acc.
3. **THE WINDOW LAWS** (`e708_window_law`, `e708_asc_bridge`): window
   membership in the recursive interval `win708 t M = [t+1..t+M]` is
   exactly the two-bounds predicate; and every STRICTLY ASCENDING list
   of window residents is a cell-selection (the order law of the
   certified witnesses).
4. **THE 8-ROW WITNESS CENSUS** (`e708_census_...`): for each of the
   engine's 8 adversarial A's, for EVERY t = 1..40 (the engine's t_max),
   minB A t <= the certified worst w — via the 40-row optimal witness
   tables (decide-certified rowwise: ascending, in-window, size,
   prod(A) | prod(B); table rows == the engine's exact per-t minima,
   battery-verified).
5. **THE 8 EXACT-MIN THEOREMS** (`e708_exact_...`): at each hard
   window, minB A t0 = w EXACTLY — the witness side AND the exclusion
   side (the enumerator decide `coverFrom (prod A) (win ...) (w-1) 1
   = false`, no smaller subset covers — the g(4)>=4 evidence row, the
   n=5 and n=6 rows, the g(2)=2 check).
6. **THE 8 CASE ROWS + THE MASTER BOARD** (`e708_case_...`,
   `erdos708_board`): per case, the complete instance-g statement (the
   worst value w is ACHIEVED at t0 over t=1..40 and is an upper bound
   throughout); the board is the 16-conjunct flat assembly (the 8
   general laws + the 8 case rows), full statements, unconditional.

Honest scope: the engine's certified range is t = 1..40 (t_max=40 in
`worst_over_intervals`); the ErSu59 universal laws (g(2)=2, g(3)=4 for
ALL A) are NOT attempted here — this kernel certifies the engine's own
finite evidence completely.  Extending the t-range or proving g(4)
bounds for all 4-sets is the next round's war.

House-law compliance: L86 (products in the exact goal spelling via
`Nat.mul_le_mul_left/right` — none needed here, omega only touches
atoms); L90 (NO defeq trusted across variable multiplications —
`Nat.one_mul`/`Nat.mul_one`/`Nat.mul_assoc` bridges throughout, the
`1 * prod B` accumulator is bridged explicitly); L91 (no variable-level
beq — divisibility via `decide (b % P = 0)` with the Prop-level
decide bridges, closed-term decide only); L92 (no List.range reasoning
beyond the CI-green `(List.range 40).all` decide + `mem_range` idiom);
NO `decide` on `∀ k < N` for N > 501 (range 40 only).  Zero sorry.
Zero admit.  Zero native_decide.  Core-only Lean 4 (Nat, omega, ring,
decide, List, Bool, Set) on the Arsenal import set.  No Mathlib. -/

namespace E708

/-! ## §0 The definitions. -/

/-- The list product (the kernel's own, equation-compiler native). -/
def prod708 : List Nat → Nat
  | [] => 1
  | x :: l => x * prod708 l

theorem prod708_nil : prod708 [] = 1 := rfl

theorem prod708_cons (x : Nat) (l : List Nat) :
    prod708 (x :: l) = x * prod708 l := rfl

/-- The maximum element (the interval length parameter: the engine's
max(A); only ever evaluated on closed lists). -/
def maxA : List Nat → Nat
  | [] => 0
  | x :: l => if maxA l < x then x else maxA l

/-- The ascending interval list [s, s+1, ..., s+k-1] (own recursion —
no List.range dependence). -/
def winUp : Nat → Nat → List Nat
  | _, 0 => []
  | s, k + 1 => s :: winUp (s + 1) k

/-- The window I_t(M) as a list: [t+1, ..., t+M]. -/
def win708 (t M : Nat) : List Nat := winUp (t + 1) M

/-- Divisibility as a Bool (decide on the mod-form; the Prop bridges
below).  Closed-term kernel evaluation only. -/
def dvB (P b : Nat) : Bool := decide (b % P = 0)

theorem dvB_true_dvd (P b : Nat) (h : dvB P b = true) : P ∣ b :=
  Nat.dvd_of_mod_eq_zero (of_decide_eq_true h)

theorem dvB_true_of_dvd (P b : Nat) (h : P ∣ b) : dvB P b = true :=
  decide_eq_true (Nat.mod_eq_zero_of_dvd h)

/-- Strictly ascending (the witness-order predicate; the engine's
combinations are emitted in interval order). -/
def ascB : List Nat → Bool
  | [] => true
  | b :: B => (B.all (fun b' => decide (b < b'))) && ascB B

theorem ascB_head (b : Nat) (B : List Nat) (h : ascB (b :: B) = true) :
    (∀ b', b' ∈ B → b < b') ∧ ascB B = true := by
  have h' : ((B.all (fun b' => decide (b < b'))) && ascB B) = true := h
  have hall : (B.all (fun b' => decide (b < b'))) = true := by
    cases hbb : (B.all (fun b' => decide (b < b'))) with
    | false => rw [hbb] at h'; exact Bool.noConfusion h'
    | true => rfl
  have hasc : ascB B = true := by
    cases hbb : (B.all (fun b' => decide (b < b'))) with
    | false => rw [hbb] at h'; exact Bool.noConfusion h'
    | true => rw [hbb] at h'; exact h'
  refine ⟨?_, hasc⟩
  intro b' hb'
  exact of_decide_eq_true ((List.all_eq_true.mp hall) b' hb')

/-- THE CELL-SELECTION SEMANTICS: B drawn from distinct cells of l, in
l's order (the engine's `itertools.combinations` over the interval
list).  Three constructors: the empty selection, dropping the head cell,
taking the head cell. -/
inductive sub708 : List Nat → List Nat → Prop
  | nil : ∀ (l : List Nat), sub708 [] l
  | drop : ∀ (x : Nat) (l B : List Nat), sub708 B l → sub708 B (x :: l)
  | take : ∀ (x : Nat) (l B : List Nat), sub708 B l → sub708 (x :: B) (x :: l)

/-- THE BUDGETED SUBSET ENUMERATOR: does some cell-selection of l with
at most k cells have (acc * its product) divisible by P?  Take the head
cell (budget-1, acc*x) or skip it; the empty suffix tests acc itself. -/
def coverFrom (P : Nat) : List Nat → Nat → Nat → Bool
  | [], _, acc => dvB P acc
  | x :: l, 0, acc => coverFrom P l 0 acc
  | x :: l, k + 1, acc => coverFrom P l k (acc * x) || coverFrom P l (k + 1) acc

/-- THE WITNESS CHECKER (Bool): length bound, strict ascent, window
residency (t < b <= t + M), and prod(A) | prod(B) in the mod-form —
all decidable on literals. -/
def w708OK (A : List Nat) (t M g : Nat) (B : List Nat) : Bool :=
  (decide (B.length ≤ g)) && (ascB B) &&
    (B.all (fun b => (decide (t < b)) && (decide (b ≤ t + M)))) &&
    (decide (prod708 B % prod708 A = 0))

/-- minB A t: the least size of a covering cell-selection from the
window I_t(max(A)) — the engine's min |B|, the instance value of the
problem's g. -/
noncomputable def minB (A : List Nat) (t : Nat) : Nat :=
  sInf {g : Nat | ∃ B, sub708 B (win708 t (maxA A)) ∧ B.length = g ∧
    prod708 A ∣ prod708 B}

/-! ## §0.1 The Bool or/and idioms (the K54-repair house set). -/

/-- Bool or: `(x || y) = true` splits. -/
theorem or_of_bool_eq (x y : Bool) (h : (x || y) = true) : x = true ∨ y = true := by
  cases x with
  | false => exact Or.inr h
  | true => exact Or.inl rfl

/-- Bool or: a true left disjunct forces the or. -/
theorem or_of_bool_left (x y : Bool) (hx : x = true) : (x || y) = true := by
  cases x with
  | false => exact Bool.noConfusion hx
  | true => rfl

/-- Bool or: a true right disjunct forces the or. -/
theorem or_of_bool_right (x y : Bool) (hy : y = true) : (x || y) = true := by
  cases x with
  | false => exact hy
  | true => rfl

/-! ## §1 THE PREDICATE LAWS (closure and composition, full generality). -/

/-- THE APPEND-PRODUCT LAW: prod(l₁ ++ l₂) = prod l₁ * prod l₂. -/
theorem e708_prod_append : ∀ (l₁ l₂ : List Nat),
    prod708 (l₁ ++ l₂) = prod708 l₁ * prod708 l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂
      show prod708 l₂ = 1 * prod708 l₂
      rw [Nat.one_mul]
  | cons x as ih =>
      intro l₂
      show x * prod708 (as ++ l₂) = x * prod708 as * prod708 l₂
      rw [ih, ← Nat.mul_assoc]

/-- THE SUPERSET LAW: a covering B stays covering under any extension
C (the pad-to-exactly-g engine room). -/
theorem e708_superset_law : ∀ (A B C : List Nat),
    prod708 A ∣ prod708 B → prod708 A ∣ prod708 (B ++ C) := by
  intro A B C hdvd
  rw [e708_prod_append]
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨k * prod708 C, by rw [hk]; ring⟩

/-- THE COMPOSITION LAW: covers of A₁ by B₁ and of A₂ by B₂ compose to
a cover of A₁ ++ A₂ by B₁ ++ B₂. -/
theorem e708_composition_law : ∀ (A₁ B₁ A₂ B₂ : List Nat),
    prod708 A₁ ∣ prod708 B₁ → prod708 A₂ ∣ prod708 B₂ →
    prod708 (A₁ ++ A₂) ∣ prod708 (B₁ ++ B₂) := by
  intro A₁ B₁ A₂ B₂ h₁ h₂
  rw [e708_prod_append, e708_prod_append]
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  exact ⟨k₁ * k₂, by rw [hk₁, hk₂]; ring⟩

/-- THE DEMAND-REFINEMENT LAW: if A' places a weaker demand (prod A'
divides prod A) then every cover of A covers A'. -/
theorem e708_refine_law : ∀ (A A' B : List Nat),
    prod708 A' ∣ prod708 A → prod708 A ∣ prod708 B → prod708 A' ∣ prod708 B :=
  fun A A' B h₁ h₂ => Nat.dvd_trans h₁ h₂

/-! ## §2 THE ENUMERATOR DUALITY (sound + complete, full generality). -/

/-- SOUNDNESS: a true enumerator run exhibits a covering cell-selection
of size <= k. -/
theorem e708_enum_sound : ∀ (P : Nat) (l : List Nat) (k acc : Nat),
    coverFrom P l k acc = true →
    ∃ B, sub708 B l ∧ B.length ≤ k ∧ P ∣ acc * prod708 B := by
  intro P l
  induction l with
  | nil =>
      intro k acc h
      have hb : dvB P acc = true := h
      refine ⟨[], sub708.nil [], Nat.zero_le k, ?_⟩
      have hd : P ∣ acc := dvB_true_dvd P acc hb
      show P ∣ acc * prod708 []
      show P ∣ acc * 1
      rw [Nat.mul_one]
      exact hd
  | cons x l' ih =>
      intro k acc h
      cases k with
      | zero =>
          have h' : coverFrom P l' 0 acc = true := h
          obtain ⟨B, hsub, hlen, hdvd⟩ := ih 0 acc h'
          exact ⟨B, sub708.drop x l' B hsub, hlen, hdvd⟩
      | succ m =>
          have h' : (coverFrom P l' m (acc * x) || coverFrom P l' (m + 1) acc) = true := h
          rcases or_of_bool_eq _ _ h' with htake | hskip
          · obtain ⟨B, hsub, hlen, hdvd⟩ := ih m (acc * x) htake
            refine ⟨x :: B, sub708.take x l' B hsub, ?_, ?_⟩
            · have hL : (x :: B).length = B.length + 1 := rfl
              rw [hL]
              omega
            · rw [prod708_cons, ← Nat.mul_assoc]
              exact hdvd
          · obtain ⟨B, hsub, hlen, hdvd⟩ := ih (m + 1) acc hskip
            exact ⟨B, sub708.drop x l' B hsub, hlen, hdvd⟩

/-- COMPLETENESS: every covering cell-selection of size <= k drives the
enumerator true — the exclusion side's bridge. -/
theorem e708_enum_complete : ∀ (P : Nat) (l : List Nat) (k acc : Nat) (B : List Nat),
    sub708 B l → B.length ≤ k → P ∣ acc * prod708 B → coverFrom P l k acc = true := by
  intro P l
  induction l with
  | nil =>
      intro k acc B hsub hlen hdvd
      cases hsub with
      | nil =>
          show dvB P acc = true
          rw [prod708_nil, Nat.mul_one] at hdvd
          exact dvB_true_of_dvd P acc hdvd
  | cons x l' ih =>
      intro k acc B hsub hlen hdvd
      cases k with
      | zero =>
          have hBnil : B = [] := by
            cases B with
            | nil => rfl
            | cons b B' =>
                have hbad : (b :: B').length ≤ 0 := hlen
                rw [List.length_cons] at hbad
                exact absurd hbad (by omega)
          subst hBnil
          show coverFrom P l' 0 acc = true
          have hz : P ∣ acc * prod708 [] := hdvd
          exact ih 0 acc [] (sub708.nil l') (Nat.zero_le 0) hz
      | succ m =>
          show (coverFrom P l' m (acc * x) || coverFrom P l' (m + 1) acc) = true
          cases hsub with
          | nil _ =>
              have hz : P ∣ acc * prod708 [] := hdvd
              exact or_of_bool_right _ _
                (ih (m + 1) acc [] (sub708.nil l') (Nat.zero_le (m + 1)) hz)
          | drop _ _ _ hsub' =>
              exact or_of_bool_right _ _ (ih (m + 1) acc _ hsub' hlen hdvd)
          | take _ _ B2 hsub' =>
              rw [List.length_cons] at hlen
              have hlen' : B2.length ≤ m := by omega
              have hdvd' : P ∣ acc * x * prod708 B2 := by
                have hP : prod708 (x :: B2) = x * prod708 B2 := prod708_cons x B2
                rw [hP, ← Nat.mul_assoc] at hdvd
                exact hdvd
              exact or_of_bool_left _ _ (ih m (acc * x) B2 hsub' hlen' hdvd')

/-! ## §3 THE WINDOW LAWS. -/

/-- THE WINDOW MEMBERSHIP LAW: b ∈ winUp s k iff s ≤ b < s + k. -/
theorem mem_winUp : ∀ (k s b : Nat), b ∈ winUp s k ↔ (s ≤ b ∧ b < s + k) := by
  intro k
  induction k with
  | zero =>
      intro s b
      show b ∈ ([] : List Nat) ↔ (s ≤ b ∧ b < s + 0)
      constructor
      · intro hb
        cases hb
      · intro hcon
        exact absurd hcon.2 (by omega)
  | succ m ih =>
      intro s b
      show b ∈ (s :: winUp (s + 1) m) ↔ (s ≤ b ∧ b < s + m + 1)
      rw [List.mem_cons]
      constructor
      · intro hb
        rcases hb with rfl | hmem
        · exact ⟨by omega, by omega⟩
        · obtain ⟨h1, h2⟩ := (ih (s + 1) b).mp hmem
          exact ⟨by omega, by omega⟩
      · intro hcon
        obtain ⟨h1, h2⟩ := hcon
        rcases (show b = s ∨ s + 1 ≤ b by omega) with hbs | hbs
        · exact Or.inl hbs
        · exact Or.inr ((ih (s + 1) b).mpr ⟨hbs, by omega⟩)

/-- THE WINDOW LAW at the problem's parameterization: membership in the
interval I_t(M) is exactly the two-bounds predicate. -/
theorem e708_window_law : ∀ (t M b : Nat), b ∈ win708 t M ↔ (t < b ∧ b ≤ t + M) := by
  intro t M b
  have h := mem_winUp M (t + 1) b
  constructor
  · intro hmem
    obtain ⟨h1, h2⟩ := h.mp hmem
    omega
  · intro hcon
    exact h.mpr ⟨by omega, by omega⟩

/-- THE ORDER LAW (the ascending bridge): every strictly ascending list
of winUp s k residents is a cell-selection. -/
theorem sub708_of_asc_gen : ∀ (k s : Nat) (B : List Nat), ascB B = true →
    (∀ b, b ∈ B → s ≤ b ∧ b < s + k) → sub708 B (winUp s k) := by
  intro k
  induction k with
  | zero =>
      intro s B hasc hmem
      cases B with
      | nil => exact sub708.nil []
      | cons b B' =>
          have hb := hmem b (List.mem_cons.mpr (Or.inl rfl))
          exact absurd hb.2 (by omega)
  | succ m ih =>
      intro s B hasc hmem
      show sub708 B (s :: winUp (s + 1) m)
      cases B with
      | nil => exact sub708.nil (s :: winUp (s + 1) m)
      | cons b B' =>
          obtain ⟨hlt, hasc'⟩ := ascB_head b B' hasc
          have hbmem := hmem b (List.mem_cons.mpr (Or.inl rfl))
          rcases (show b = s ∨ s < b by omega) with hbs | hbs
          · rw [hbs] at hmem hlt ⊢
            refine sub708.take s (winUp (s + 1) m) B' (ih (s + 1) B' hasc' ?_)
            intro b'' hb''
            have hb2 := hmem b'' (List.mem_cons.mpr (Or.inr hb''))
            have hb3 : s < b'' := hlt b'' hb''
            omega
          · refine sub708.drop s (winUp (s + 1) m) (b :: B') (ih (s + 1) (b :: B') hasc ?_)
            intro b'' hb''
            have hb2 := hmem b'' hb''
            have hs : s < b'' := by
              rcases List.mem_cons.mp hb'' with heq | hmem2
              · omega
              · have hltb := hlt b'' hmem2
                omega
            omega

/-- THE ASCENDING BRIDGE at the problem's windows: strictly ascending
window-resident selections are cell-selections of I_t(M). -/
theorem e708_asc_bridge : ∀ (t M : Nat) (B : List Nat), ascB B = true →
    (∀ b, b ∈ B → t < b ∧ b ≤ t + M) → sub708 B (win708 t M) := by
  intro t M B hasc hmem
  have hmem' : ∀ b, b ∈ B → t + 1 ≤ b ∧ b < t + 1 + M := by
    intro b hb
    have hb2 := hmem b hb
    omega
  exact sub708_of_asc_gen M (t + 1) B hasc hmem'

/-! ## §4 THE WITNESS CHECKER SPEC (the Bool-to-Prop bridge). -/

/-- The checker is sound: a true row certifies length bound, strict
ascent, window residency, and the divisibility cover. -/
theorem w708OK_spec (A : List Nat) (t M g : Nat) (B : List Nat)
    (h : w708OK A t M g B = true) :
    B.length ≤ g ∧ ascB B = true ∧
    (∀ b, b ∈ B → t < b ∧ b ≤ t + M) ∧ prod708 A ∣ prod708 B := by
  simp only [w708OK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hlen, hasc⟩, hall⟩, hcov⟩ := h
  have hmem : ∀ b, b ∈ B → t < b ∧ b ≤ t + M := by
    intro b hb
    have hrow := (List.all_eq_true.mp hall) b hb
    simp only [Bool.and_eq_true] at hrow
    obtain ⟨h1, h2⟩ := hrow
    exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
  exact ⟨of_decide_eq_true hlen, hasc, hmem,
    Nat.dvd_of_mod_eq_zero (of_decide_eq_true hcov)⟩

/-! ## §5 THE 8 WITNESS TABLES (the engine's per-t optimal witnesses).

Each table row r = t - 1 (t = 1..40, the engine's t_max) carries a
covering selection of size EXACTLY the engine's per-t min |B| (the
battery re-verifies rowwise: ascending, in-window, prod(A) | prod(B)).
The hard-window rows reproduce the engine's printed witnesses
verbatim ([2,3], [5,12,15], [25,26,27], [5,12,14,15], [3,15,20,21],
[5,6,7], [3,14,15,20,21], [14,21,25,35,36]). -/

def wit23 : Nat → List Nat :=
  fun r =>
  [
    [2, 3],
    [3, 4],
    [6],
    [6],
    [6],
    [8, 9],
    [8, 9],
    [9, 10],
    [12],
    [12],
    [12],
    [14, 15],
    [14, 15],
    [15, 16],
    [18],
    [18],
    [18],
    [20, 21],
    [20, 21],
    [21, 22],
    [24],
    [24],
    [24],
    [26, 27],
    [26, 27],
    [27, 28],
    [30],
    [30],
    [30],
    [32, 33],
    [32, 33],
    [33, 34],
    [36],
    [36],
    [36],
    [38, 39],
    [38, 39],
    [39, 40],
    [42],
    [42]
  ].getD r []

def wit6_10_15 : Nat → List Nat :=
  fun r =>
  [
    [5, 12, 15],
    [5, 12, 15],
    [5, 10, 18],
    [5, 10, 18],
    [6, 10, 15],
    [9, 10, 20],
    [9, 10, 20],
    [9, 10, 20],
    [10, 12, 15],
    [12, 15, 20],
    [12, 15, 20],
    [14, 18, 25],
    [14, 18, 25],
    [15, 18, 20],
    [16, 18, 25],
    [18, 20, 25],
    [18, 20, 25],
    [20, 21, 30],
    [20, 21, 30],
    [21, 24, 25],
    [25, 36],
    [25, 36],
    [25, 36],
    [25, 36],
    [27, 30, 40],
    [27, 30, 40],
    [30, 33, 40],
    [30, 33, 40],
    [30, 33, 40],
    [40, 45],
    [40, 45],
    [40, 45],
    [40, 45],
    [40, 45],
    [36, 50],
    [40, 45],
    [40, 45],
    [40, 45],
    [40, 45],
    [50, 54]
  ].getD r []

def wit2_3_5 : Nat → List Nat :=
  fun r =>
  [
    [5, 6],
    [5, 6],
    [5, 6],
    [5, 6],
    [6, 10],
    [9, 10],
    [9, 10],
    [9, 10],
    [10, 12],
    [12, 15],
    [12, 15],
    [14, 15],
    [14, 15],
    [15, 16],
    [18, 20],
    [18, 20],
    [18, 20],
    [20, 21],
    [20, 21],
    [24, 25],
    [24, 25],
    [24, 25],
    [24, 25],
    [25, 26, 27],
    [30],
    [30],
    [30],
    [30],
    [30],
    [32, 33, 35],
    [35, 36],
    [35, 36],
    [35, 36],
    [35, 36],
    [36, 40],
    [39, 40],
    [39, 40],
    [39, 40],
    [40, 42],
    [42, 45]
  ].getD r []

def wit6_10_14_15 : Nat → List Nat :=
  fun r =>
  [
    [5, 12, 14, 15],
    [5, 12, 14, 15],
    [5, 10, 14, 18],
    [5, 10, 14, 18],
    [6, 7, 15, 20],
    [7, 9, 10, 20],
    [8, 10, 15, 21],
    [9, 10, 14, 20],
    [10, 12, 14, 15],
    [21, 24, 25],
    [21, 24, 25],
    [21, 24, 25],
    [18, 25, 28],
    [18, 25, 28],
    [18, 25, 28],
    [18, 25, 28],
    [18, 25, 28],
    [20, 21, 30],
    [20, 21, 30],
    [21, 24, 25],
    [24, 30, 35],
    [24, 30, 35],
    [24, 30, 35],
    [25, 28, 36],
    [27, 35, 40],
    [27, 35, 40],
    [30, 35, 36],
    [30, 35, 36],
    [30, 35, 36],
    [32, 35, 45],
    [32, 35, 45],
    [35, 36, 40],
    [35, 36, 40],
    [35, 36, 40],
    [36, 42, 50],
    [40, 42, 45],
    [40, 42, 45],
    [40, 42, 45],
    [40, 42, 45],
    [42, 48, 50]
  ].getD r []

def wit6_10_15_21 : Nat → List Nat :=
  fun r =>
  [
    [3, 15, 20, 21],
    [3, 15, 20, 21],
    [5, 9, 20, 21],
    [5, 9, 20, 21],
    [6, 7, 18, 25],
    [7, 8, 25, 27],
    [25, 27, 28],
    [25, 27, 28],
    [25, 27, 28],
    [25, 27, 28],
    [25, 27, 28],
    [25, 27, 28],
    [25, 27, 28],
    [18, 30, 35],
    [18, 30, 35],
    [18, 30, 35],
    [18, 30, 35],
    [20, 27, 35],
    [20, 27, 35],
    [21, 25, 36],
    [25, 27, 28],
    [25, 27, 28],
    [25, 27, 28],
    [25, 27, 28],
    [27, 35, 40],
    [27, 35, 40],
    [28, 30, 45],
    [30, 35, 36],
    [30, 35, 36],
    [35, 36, 45],
    [35, 36, 45],
    [35, 36, 45],
    [35, 36, 45],
    [35, 36, 45],
    [36, 42, 50],
    [40, 42, 45],
    [40, 42, 45],
    [40, 42, 45],
    [40, 42, 45],
    [42, 45, 50]
  ].getD r []

def wit2_3_5_7 : Nat → List Nat :=
  fun r =>
  [
    [5, 6, 7],
    [5, 6, 7],
    [5, 6, 7],
    [5, 6, 7],
    [6, 7, 10],
    [7, 9, 10],
    [9, 10, 14],
    [14, 15],
    [14, 15],
    [14, 15],
    [14, 15],
    [14, 15],
    [14, 15],
    [20, 21],
    [20, 21],
    [20, 21],
    [20, 21],
    [20, 21],
    [20, 21],
    [21, 22, 25],
    [24, 25, 28],
    [24, 25, 28],
    [28, 30],
    [28, 30],
    [28, 30],
    [28, 30],
    [28, 30],
    [30, 35],
    [30, 35],
    [35, 36],
    [35, 36],
    [35, 36],
    [35, 36],
    [35, 36],
    [40, 42],
    [40, 42],
    [40, 42],
    [40, 42],
    [40, 42],
    [42, 45]
  ].getD r []

def wit6_10_14_15_21 : Nat → List Nat :=
  fun r =>
  [
    [3, 14, 15, 20, 21],
    [3, 14, 15, 20, 21],
    [5, 7, 15, 21, 24],
    [5, 7, 15, 21, 24],
    [6, 7, 12, 21, 25],
    [7, 8, 9, 21, 25],
    [14, 25, 27, 28],
    [14, 25, 27, 28],
    [14, 25, 27, 28],
    [14, 25, 27, 28],
    [14, 25, 27, 28],
    [14, 25, 27, 28],
    [14, 25, 27, 28],
    [15, 18, 28, 35],
    [18, 20, 21, 35],
    [18, 20, 21, 35],
    [18, 20, 21, 35],
    [20, 21, 35, 36],
    [20, 21, 35, 36],
    [21, 24, 30, 35],
    [24, 30, 35, 42],
    [24, 30, 35, 42],
    [24, 30, 35, 42],
    [25, 27, 28, 42],
    [27, 28, 30, 35],
    [27, 28, 30, 35],
    [28, 30, 35, 36],
    [30, 32, 45, 49],
    [30, 32, 45, 49],
    [32, 35, 42, 45],
    [32, 35, 42, 45],
    [33, 36, 49, 50],
    [34, 49, 50, 54],
    [35, 36, 40, 42],
    [36, 39, 49, 50],
    [38, 49, 50, 54],
    [38, 49, 50, 54],
    [39, 40, 45, 49],
    [40, 42, 45, 49],
    [42, 45, 49, 60]
  ].getD r []

def wit6_10_14_15_21_35 : Nat → List Nat :=
  fun r =>
  [
    [14, 21, 25, 35, 36],
    [14, 21, 25, 35, 36],
    [14, 21, 25, 35, 36],
    [14, 21, 25, 35, 36],
    [14, 21, 25, 35, 36],
    [14, 21, 25, 35, 36],
    [9, 25, 28, 35, 42],
    [9, 25, 28, 35, 42],
    [10, 21, 30, 35, 42],
    [12, 21, 25, 35, 42],
    [12, 21, 25, 35, 42],
    [14, 15, 28, 35, 45],
    [14, 15, 28, 35, 45],
    [15, 16, 35, 45, 49],
    [16, 21, 25, 45, 49],
    [18, 20, 21, 25, 49],
    [18, 20, 21, 25, 49],
    [20, 21, 25, 36, 49],
    [20, 21, 25, 36, 49],
    [21, 24, 25, 30, 49],
    [22, 35, 49, 50, 54],
    [24, 25, 27, 35, 49],
    [24, 25, 27, 35, 49],
    [25, 27, 28, 30, 49],
    [26, 35, 45, 49, 60],
    [27, 28, 30, 49, 50],
    [28, 30, 35, 42, 45],
    [49, 50, 60, 63],
    [49, 50, 60, 63],
    [49, 50, 60, 63],
    [49, 50, 60, 63],
    [49, 50, 60, 63],
    [49, 50, 60, 63],
    [49, 50, 60, 63],
    [42, 50, 63, 70],
    [42, 50, 63, 70],
    [42, 50, 63, 70],
    [42, 50, 63, 70],
    [42, 50, 63, 70],
    [42, 49, 60, 75]
  ].getD r []

/-- THE 8 TABLE DECIDES: every row of every table passes the checker
(40 rows each: ascending, in-window, size <= the certified worst,
prod(A) | prod(B)). -/
theorem hwit23 : (List.range 40).all
    (fun r => w708OK [2, 3] (r + 1) (maxA [2, 3]) 2 (wit23 r)) = true := by
  decide

theorem hwit6_10_15 : (List.range 40).all
    (fun r => w708OK [6, 10, 15] (r + 1) (maxA [6, 10, 15]) 3 (wit6_10_15 r)) = true := by
  decide

theorem hwit2_3_5 : (List.range 40).all
    (fun r => w708OK [2, 3, 5] (r + 1) (maxA [2, 3, 5]) 3 (wit2_3_5 r)) = true := by
  decide

theorem hwit6_10_14_15 : (List.range 40).all
    (fun r => w708OK [6, 10, 14, 15] (r + 1) (maxA [6, 10, 14, 15]) 4
      (wit6_10_14_15 r)) = true := by
  decide

theorem hwit6_10_15_21 : (List.range 40).all
    (fun r => w708OK [6, 10, 15, 21] (r + 1) (maxA [6, 10, 15, 21]) 4
      (wit6_10_15_21 r)) = true := by
  decide

theorem hwit2_3_5_7 : (List.range 40).all
    (fun r => w708OK [2, 3, 5, 7] (r + 1) (maxA [2, 3, 5, 7]) 3 (wit2_3_5_7 r)) = true := by
  decide

theorem hwit6_10_14_15_21 : (List.range 40).all
    (fun r => w708OK [6, 10, 14, 15, 21] (r + 1) (maxA [6, 10, 14, 15, 21]) 5
      (wit6_10_14_15_21 r)) = true := by
  decide

theorem hwit6_10_14_15_21_35 : (List.range 40).all
    (fun r => w708OK [6, 10, 14, 15, 21, 35] (r + 1) (maxA [6, 10, 14, 15, 21, 35]) 5
      (wit6_10_14_15_21_35 r)) = true := by
  decide

/-! ## §6 THE 8-ROW WITNESS CENSUS (the complete per-case upper law).

For each of the engine's 8 adversarial A's: for EVERY t = 1..40 (the
engine's t_max), minB A t <= the certified worst w — every interval of
the certified range admits a covering selection within the worst size. -/

/-- THE CENSUS ROW for A = [2, 3] (the g(2) = 2 check instance). -/
theorem e708_census_23 : ∀ t : Nat, 1 ≤ t → t ≤ 40 → minB [2, 3] t ≤ 2 := by
  intro t h1 h40
  have hrow := (List.all_eq_true.mp hwit23) (t - 1) (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [2, 3] (t - 1 + 1) (maxA [2, 3]) 2 (wit23 (t - 1)) hrow
  have hmemt : ∀ b, b ∈ wit23 (t - 1) → t < b ∧ b ≤ t + maxA [2, 3] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit23 (t - 1)) (win708 t (maxA [2, 3])) :=
    e708_asc_bridge t (maxA [2, 3]) (wit23 (t - 1)) hasc hmemt
  have hmem' : (wit23 (t - 1)).length ∈
      {g : Nat | ∃ B, sub708 B (win708 t (maxA [2, 3])) ∧ B.length = g ∧
        prod708 [2, 3] ∣ prod708 B} := by
    show ∃ B, sub708 B (win708 t (maxA [2, 3])) ∧ B.length = (wit23 (t - 1)).length ∧
      prod708 [2, 3] ∣ prod708 B
    exact ⟨wit23 (t - 1), hsub, rfl, hcov⟩
  exact Nat.le_trans (Nat.sInf_le hmem') hlen

/-- THE CENSUS ROW for A = [6, 10, 15] (the semiprime triangle). -/
theorem e708_census_6_10_15 : ∀ t : Nat, 1 ≤ t → t ≤ 40 → minB [6, 10, 15] t ≤ 3 := by
  intro t h1 h40
  have hrow := (List.all_eq_true.mp hwit6_10_15) (t - 1) (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 15] (t - 1 + 1) (maxA [6, 10, 15]) 3 (wit6_10_15 (t - 1)) hrow
  have hmemt : ∀ b, b ∈ wit6_10_15 (t - 1) → t < b ∧ b ≤ t + maxA [6, 10, 15] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_15 (t - 1)) (win708 t (maxA [6, 10, 15])) :=
    e708_asc_bridge t (maxA [6, 10, 15]) (wit6_10_15 (t - 1)) hasc hmemt
  have hmem' : (wit6_10_15 (t - 1)).length ∈
      {g : Nat | ∃ B, sub708 B (win708 t (maxA [6, 10, 15])) ∧ B.length = g ∧
        prod708 [6, 10, 15] ∣ prod708 B} := by
    show ∃ B, sub708 B (win708 t (maxA [6, 10, 15])) ∧ B.length = (wit6_10_15 (t - 1)).length ∧
      prod708 [6, 10, 15] ∣ prod708 B
    exact ⟨wit6_10_15 (t - 1), hsub, rfl, hcov⟩
  exact Nat.le_trans (Nat.sInf_le hmem') hlen

/-- THE CENSUS ROW for A = [2, 3, 5] (the primes triangle, hard t = 24). -/
theorem e708_census_2_3_5 : ∀ t : Nat, 1 ≤ t → t ≤ 40 → minB [2, 3, 5] t ≤ 3 := by
  intro t h1 h40
  have hrow := (List.all_eq_true.mp hwit2_3_5) (t - 1) (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [2, 3, 5] (t - 1 + 1) (maxA [2, 3, 5]) 3 (wit2_3_5 (t - 1)) hrow
  have hmemt : ∀ b, b ∈ wit2_3_5 (t - 1) → t < b ∧ b ≤ t + maxA [2, 3, 5] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit2_3_5 (t - 1)) (win708 t (maxA [2, 3, 5])) :=
    e708_asc_bridge t (maxA [2, 3, 5]) (wit2_3_5 (t - 1)) hasc hmemt
  have hmem' : (wit2_3_5 (t - 1)).length ∈
      {g : Nat | ∃ B, sub708 B (win708 t (maxA [2, 3, 5])) ∧ B.length = g ∧
        prod708 [2, 3, 5] ∣ prod708 B} := by
    show ∃ B, sub708 B (win708 t (maxA [2, 3, 5])) ∧ B.length = (wit2_3_5 (t - 1)).length ∧
      prod708 [2, 3, 5] ∣ prod708 B
    exact ⟨wit2_3_5 (t - 1), hsub, rfl, hcov⟩
  exact Nat.le_trans (Nat.sInf_le hmem') hlen

/-- THE CENSUS ROW for A = [6, 10, 14, 15] (n = 4, the g(4) >= 4 evidence). -/
theorem e708_census_6_10_14_15 : ∀ t : Nat, 1 ≤ t → t ≤ 40 →
    minB [6, 10, 14, 15] t ≤ 4 := by
  intro t h1 h40
  have hrow := (List.all_eq_true.mp hwit6_10_14_15) (t - 1) (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 14, 15] (t - 1 + 1) (maxA [6, 10, 14, 15]) 4
      (wit6_10_14_15 (t - 1)) hrow
  have hmemt : ∀ b, b ∈ wit6_10_14_15 (t - 1) → t < b ∧ b ≤ t + maxA [6, 10, 14, 15] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_14_15 (t - 1)) (win708 t (maxA [6, 10, 14, 15])) :=
    e708_asc_bridge t (maxA [6, 10, 14, 15]) (wit6_10_14_15 (t - 1)) hasc hmemt
  have hmem' : (wit6_10_14_15 (t - 1)).length ∈
      {g : Nat | ∃ B, sub708 B (win708 t (maxA [6, 10, 14, 15])) ∧ B.length = g ∧
        prod708 [6, 10, 14, 15] ∣ prod708 B} := by
    show ∃ B, sub708 B (win708 t (maxA [6, 10, 14, 15])) ∧
      B.length = (wit6_10_14_15 (t - 1)).length ∧
      prod708 [6, 10, 14, 15] ∣ prod708 B
    exact ⟨wit6_10_14_15 (t - 1), hsub, rfl, hcov⟩
  exact Nat.le_trans (Nat.sInf_le hmem') hlen

/-- THE CENSUS ROW for A = [6, 10, 15, 21] (n = 4 tri + 21). -/
theorem e708_census_6_10_15_21 : ∀ t : Nat, 1 ≤ t → t ≤ 40 →
    minB [6, 10, 15, 21] t ≤ 4 := by
  intro t h1 h40
  have hrow := (List.all_eq_true.mp hwit6_10_15_21) (t - 1) (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 15, 21] (t - 1 + 1) (maxA [6, 10, 15, 21]) 4
      (wit6_10_15_21 (t - 1)) hrow
  have hmemt : ∀ b, b ∈ wit6_10_15_21 (t - 1) → t < b ∧ b ≤ t + maxA [6, 10, 15, 21] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_15_21 (t - 1)) (win708 t (maxA [6, 10, 15, 21])) :=
    e708_asc_bridge t (maxA [6, 10, 15, 21]) (wit6_10_15_21 (t - 1)) hasc hmemt
  have hmem' : (wit6_10_15_21 (t - 1)).length ∈
      {g : Nat | ∃ B, sub708 B (win708 t (maxA [6, 10, 15, 21])) ∧ B.length = g ∧
        prod708 [6, 10, 15, 21] ∣ prod708 B} := by
    show ∃ B, sub708 B (win708 t (maxA [6, 10, 15, 21])) ∧
      B.length = (wit6_10_15_21 (t - 1)).length ∧
      prod708 [6, 10, 15, 21] ∣ prod708 B
    exact ⟨wit6_10_15_21 (t - 1), hsub, rfl, hcov⟩
  exact Nat.le_trans (Nat.sInf_le hmem') hlen

/-- THE CENSUS ROW for A = [2, 3, 5, 7] (n = 4 primes). -/
theorem e708_census_2_3_5_7 : ∀ t : Nat, 1 ≤ t → t ≤ 40 → minB [2, 3, 5, 7] t ≤ 3 := by
  intro t h1 h40
  have hrow := (List.all_eq_true.mp hwit2_3_5_7) (t - 1) (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [2, 3, 5, 7] (t - 1 + 1) (maxA [2, 3, 5, 7]) 3 (wit2_3_5_7 (t - 1)) hrow
  have hmemt : ∀ b, b ∈ wit2_3_5_7 (t - 1) → t < b ∧ b ≤ t + maxA [2, 3, 5, 7] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit2_3_5_7 (t - 1)) (win708 t (maxA [2, 3, 5, 7])) :=
    e708_asc_bridge t (maxA [2, 3, 5, 7]) (wit2_3_5_7 (t - 1)) hasc hmemt
  have hmem' : (wit2_3_5_7 (t - 1)).length ∈
      {g : Nat | ∃ B, sub708 B (win708 t (maxA [2, 3, 5, 7])) ∧ B.length = g ∧
        prod708 [2, 3, 5, 7] ∣ prod708 B} := by
    show ∃ B, sub708 B (win708 t (maxA [2, 3, 5, 7])) ∧
      B.length = (wit2_3_5_7 (t - 1)).length ∧
      prod708 [2, 3, 5, 7] ∣ prod708 B
    exact ⟨wit2_3_5_7 (t - 1), hsub, rfl, hcov⟩
  exact Nat.le_trans (Nat.sInf_le hmem') hlen

/-- THE CENSUS ROW for A = [6, 10, 14, 15, 21] (n = 5). -/
theorem e708_census_6_10_14_15_21 : ∀ t : Nat, 1 ≤ t → t ≤ 40 →
    minB [6, 10, 14, 15, 21] t ≤ 5 := by
  intro t h1 h40
  have hrow := (List.all_eq_true.mp hwit6_10_14_15_21) (t - 1)
    (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 14, 15, 21] (t - 1 + 1) (maxA [6, 10, 14, 15, 21]) 5
      (wit6_10_14_15_21 (t - 1)) hrow
  have hmemt : ∀ b, b ∈ wit6_10_14_15_21 (t - 1) →
      t < b ∧ b ≤ t + maxA [6, 10, 14, 15, 21] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_14_15_21 (t - 1)) (win708 t (maxA [6, 10, 14, 15, 21])) :=
    e708_asc_bridge t (maxA [6, 10, 14, 15, 21]) (wit6_10_14_15_21 (t - 1)) hasc hmemt
  have hmem' : (wit6_10_14_15_21 (t - 1)).length ∈
      {g : Nat | ∃ B, sub708 B (win708 t (maxA [6, 10, 14, 15, 21])) ∧ B.length = g ∧
        prod708 [6, 10, 14, 15, 21] ∣ prod708 B} := by
    show ∃ B, sub708 B (win708 t (maxA [6, 10, 14, 15, 21])) ∧
      B.length = (wit6_10_14_15_21 (t - 1)).length ∧
      prod708 [6, 10, 14, 15, 21] ∣ prod708 B
    exact ⟨wit6_10_14_15_21 (t - 1), hsub, rfl, hcov⟩
  exact Nat.le_trans (Nat.sInf_le hmem') hlen

/-- THE CENSUS ROW for A = [6, 10, 14, 15, 21, 35] (n = 6 K4-edge). -/
theorem e708_census_6_10_14_15_21_35 : ∀ t : Nat, 1 ≤ t → t ≤ 40 →
    minB [6, 10, 14, 15, 21, 35] t ≤ 5 := by
  intro t h1 h40
  have hrow := (List.all_eq_true.mp hwit6_10_14_15_21_35) (t - 1)
    (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 14, 15, 21, 35] (t - 1 + 1) (maxA [6, 10, 14, 15, 21, 35]) 5
      (wit6_10_14_15_21_35 (t - 1)) hrow
  have hmemt : ∀ b, b ∈ wit6_10_14_15_21_35 (t - 1) →
      t < b ∧ b ≤ t + maxA [6, 10, 14, 15, 21, 35] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_14_15_21_35 (t - 1))
      (win708 t (maxA [6, 10, 14, 15, 21, 35])) :=
    e708_asc_bridge t (maxA [6, 10, 14, 15, 21, 35])
      (wit6_10_14_15_21_35 (t - 1)) hasc hmemt
  have hmem' : (wit6_10_14_15_21_35 (t - 1)).length ∈
      {g : Nat | ∃ B, sub708 B (win708 t (maxA [6, 10, 14, 15, 21, 35])) ∧ B.length = g ∧
        prod708 [6, 10, 14, 15, 21, 35] ∣ prod708 B} := by
    show ∃ B, sub708 B (win708 t (maxA [6, 10, 14, 15, 21, 35])) ∧
      B.length = (wit6_10_14_15_21_35 (t - 1)).length ∧
      prod708 [6, 10, 14, 15, 21, 35] ∣ prod708 B
    exact ⟨wit6_10_14_15_21_35 (t - 1), hsub, rfl, hcov⟩
  exact Nat.le_trans (Nat.sInf_le hmem') hlen

/-! ## §7 THE 8 EXACT-MIN THEOREMS (witness side + exclusion side).

At each hard window: minB A t0 = w EXACTLY.  The exclusion side is the
decide-certified enumerator fact — NO subset of the window of size < w
covers prod(A) (the engine's certified lower bound, kernel-enumerated). -/

/-- THE EXACT MIN for A = [2, 3] at t = 1: minB = 2 (the g(2) = 2 check:
no single window element is divisible by 6). -/
theorem e708_exact_23 : minB [2, 3] 1 = 2 := by
  have hrow := (List.all_eq_true.mp hwit23) 0 (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [2, 3] (0 + 1) (maxA [2, 3]) 2 (wit23 0) hrow
  have hmemt : ∀ b, b ∈ wit23 0 → 1 < b ∧ b ≤ 1 + maxA [2, 3] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit23 0) (win708 1 (maxA [2, 3])) :=
    e708_asc_bridge 1 (maxA [2, 3]) (wit23 0) hasc hmemt
  have hne : {g : Nat | ∃ B, sub708 B (win708 1 (maxA [2, 3])) ∧ B.length = g ∧
      prod708 [2, 3] ∣ prod708 B}.Nonempty := by
    refine ⟨(wit23 0).length, ?_⟩
    show ∃ B, sub708 B (win708 1 (maxA [2, 3])) ∧ B.length = (wit23 0).length ∧
      prod708 [2, 3] ∣ prod708 B
    exact ⟨wit23 0, hsub, rfl, hcov⟩
  have henum : coverFrom (prod708 [2, 3]) (win708 1 (maxA [2, 3])) (2 - 1) 1 = false := by
    decide
  have hge : 2 ≤ minB [2, 3] 1 := by
    by_contra hlt
    have hmem2 : ∃ B, sub708 B (win708 1 (maxA [2, 3])) ∧
        B.length = minB [2, 3] 1 ∧ prod708 [2, 3] ∣ prod708 B :=
      Nat.sInf_mem hne
    obtain ⟨B, hsub', hlen', hcov'⟩ := hmem2
    have hcompl := e708_enum_complete (prod708 [2, 3]) (win708 1 (maxA [2, 3]))
      (2 - 1) 1 B hsub' (by omega) (by rw [Nat.one_mul]; exact hcov')
    rw [hcompl] at henum
    exact Bool.noConfusion henum
  have hcens : minB [2, 3] 1 ≤ 2 := e708_census_23 1 (by omega) (by omega)
  omega

/-- THE EXACT MIN for A = [6, 10, 15] at t = 1: minB = 3. -/
theorem e708_exact_6_10_15 : minB [6, 10, 15] 1 = 3 := by
  have hrow := (List.all_eq_true.mp hwit6_10_15) 0 (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 15] (0 + 1) (maxA [6, 10, 15]) 3 (wit6_10_15 0) hrow
  have hmemt : ∀ b, b ∈ wit6_10_15 0 → 1 < b ∧ b ≤ 1 + maxA [6, 10, 15] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_15 0) (win708 1 (maxA [6, 10, 15])) :=
    e708_asc_bridge 1 (maxA [6, 10, 15]) (wit6_10_15 0) hasc hmemt
  have hne : {g : Nat | ∃ B, sub708 B (win708 1 (maxA [6, 10, 15])) ∧ B.length = g ∧
      prod708 [6, 10, 15] ∣ prod708 B}.Nonempty := by
    refine ⟨(wit6_10_15 0).length, ?_⟩
    show ∃ B, sub708 B (win708 1 (maxA [6, 10, 15])) ∧ B.length = (wit6_10_15 0).length ∧
      prod708 [6, 10, 15] ∣ prod708 B
    exact ⟨wit6_10_15 0, hsub, rfl, hcov⟩
  have henum : coverFrom (prod708 [6, 10, 15]) (win708 1 (maxA [6, 10, 15]))
      (3 - 1) 1 = false := by
    decide
  have hge : 3 ≤ minB [6, 10, 15] 1 := by
    by_contra hlt
    have hmem2 : ∃ B, sub708 B (win708 1 (maxA [6, 10, 15])) ∧
        B.length = minB [6, 10, 15] 1 ∧ prod708 [6, 10, 15] ∣ prod708 B :=
      Nat.sInf_mem hne
    obtain ⟨B, hsub', hlen', hcov'⟩ := hmem2
    have hcompl := e708_enum_complete (prod708 [6, 10, 15]) (win708 1 (maxA [6, 10, 15]))
      (3 - 1) 1 B hsub' (by omega) (by rw [Nat.one_mul]; exact hcov')
    rw [hcompl] at henum
    exact Bool.noConfusion henum
  have hcens : minB [6, 10, 15] 1 ≤ 3 := e708_census_6_10_15 1 (by omega) (by omega)
  omega

/-- THE EXACT MIN for A = [2, 3, 5] at t = 24: minB = 3 (the ONLY
nontrivial hard window: the {25,...,29} row — no pair from the window
has product divisible by 30). -/
theorem e708_exact_2_3_5 : minB [2, 3, 5] 24 = 3 := by
  have hrow := (List.all_eq_true.mp hwit2_3_5) 23 (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [2, 3, 5] (23 + 1) (maxA [2, 3, 5]) 3 (wit2_3_5 23) hrow
  have hmemt : ∀ b, b ∈ wit2_3_5 23 → 24 < b ∧ b ≤ 24 + maxA [2, 3, 5] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit2_3_5 23) (win708 24 (maxA [2, 3, 5])) :=
    e708_asc_bridge 24 (maxA [2, 3, 5]) (wit2_3_5 23) hasc hmemt
  have hne : {g : Nat | ∃ B, sub708 B (win708 24 (maxA [2, 3, 5])) ∧ B.length = g ∧
      prod708 [2, 3, 5] ∣ prod708 B}.Nonempty := by
    refine ⟨(wit2_3_5 23).length, ?_⟩
    show ∃ B, sub708 B (win708 24 (maxA [2, 3, 5])) ∧ B.length = (wit2_3_5 23).length ∧
      prod708 [2, 3, 5] ∣ prod708 B
    exact ⟨wit2_3_5 23, hsub, rfl, hcov⟩
  have henum : coverFrom (prod708 [2, 3, 5]) (win708 24 (maxA [2, 3, 5]))
      (3 - 1) 1 = false := by
    decide
  have hge : 3 ≤ minB [2, 3, 5] 24 := by
    by_contra hlt
    have hmem2 : ∃ B, sub708 B (win708 24 (maxA [2, 3, 5])) ∧
        B.length = minB [2, 3, 5] 24 ∧ prod708 [2, 3, 5] ∣ prod708 B :=
      Nat.sInf_mem hne
    obtain ⟨B, hsub', hlen', hcov'⟩ := hmem2
    have hcompl := e708_enum_complete (prod708 [2, 3, 5]) (win708 24 (maxA [2, 3, 5]))
      (3 - 1) 1 B hsub' (by omega) (by rw [Nat.one_mul]; exact hcov')
    rw [hcompl] at henum
    exact Bool.noConfusion henum
  have hcens : minB [2, 3, 5] 24 ≤ 3 := e708_census_2_3_5 24 (by omega) (by omega)
  omega

/-- THE EXACT MIN for A = [6, 10, 14, 15] at t = 1: minB = 4 — THE
g(4) >= 4 EVIDENCE ROW (an n = 4 instance forcing exactly 4). -/
theorem e708_exact_6_10_14_15 : minB [6, 10, 14, 15] 1 = 4 := by
  have hrow := (List.all_eq_true.mp hwit6_10_14_15) 0 (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 14, 15] (0 + 1) (maxA [6, 10, 14, 15]) 4 (wit6_10_14_15 0) hrow
  have hmemt : ∀ b, b ∈ wit6_10_14_15 0 → 1 < b ∧ b ≤ 1 + maxA [6, 10, 14, 15] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_14_15 0) (win708 1 (maxA [6, 10, 14, 15])) :=
    e708_asc_bridge 1 (maxA [6, 10, 14, 15]) (wit6_10_14_15 0) hasc hmemt
  have hne : {g : Nat | ∃ B, sub708 B (win708 1 (maxA [6, 10, 14, 15])) ∧ B.length = g ∧
      prod708 [6, 10, 14, 15] ∣ prod708 B}.Nonempty := by
    refine ⟨(wit6_10_14_15 0).length, ?_⟩
    show ∃ B, sub708 B (win708 1 (maxA [6, 10, 14, 15])) ∧
      B.length = (wit6_10_14_15 0).length ∧
      prod708 [6, 10, 14, 15] ∣ prod708 B
    exact ⟨wit6_10_14_15 0, hsub, rfl, hcov⟩
  have henum : coverFrom (prod708 [6, 10, 14, 15]) (win708 1 (maxA [6, 10, 14, 15]))
      (4 - 1) 1 = false := by
    decide
  have hge : 4 ≤ minB [6, 10, 14, 15] 1 := by
    by_contra hlt
    have hmem2 : ∃ B, sub708 B (win708 1 (maxA [6, 10, 14, 15])) ∧
        B.length = minB [6, 10, 14, 15] 1 ∧ prod708 [6, 10, 14, 15] ∣ prod708 B :=
      Nat.sInf_mem hne
    obtain ⟨B, hsub', hlen', hcov'⟩ := hmem2
    have hcompl := e708_enum_complete (prod708 [6, 10, 14, 15])
      (win708 1 (maxA [6, 10, 14, 15])) (4 - 1) 1 B hsub' (by omega)
      (by rw [Nat.one_mul]; exact hcov')
    rw [hcompl] at henum
    exact Bool.noConfusion henum
  have hcens : minB [6, 10, 14, 15] 1 ≤ 4 :=
    e708_census_6_10_14_15 1 (by omega) (by omega)
  omega

/-- THE EXACT MIN for A = [6, 10, 15, 21] at t = 1: minB = 4. -/
theorem e708_exact_6_10_15_21 : minB [6, 10, 15, 21] 1 = 4 := by
  have hrow := (List.all_eq_true.mp hwit6_10_15_21) 0 (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 15, 21] (0 + 1) (maxA [6, 10, 15, 21]) 4 (wit6_10_15_21 0) hrow
  have hmemt : ∀ b, b ∈ wit6_10_15_21 0 → 1 < b ∧ b ≤ 1 + maxA [6, 10, 15, 21] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_15_21 0) (win708 1 (maxA [6, 10, 15, 21])) :=
    e708_asc_bridge 1 (maxA [6, 10, 15, 21]) (wit6_10_15_21 0) hasc hmemt
  have hne : {g : Nat | ∃ B, sub708 B (win708 1 (maxA [6, 10, 15, 21])) ∧ B.length = g ∧
      prod708 [6, 10, 15, 21] ∣ prod708 B}.Nonempty := by
    refine ⟨(wit6_10_15_21 0).length, ?_⟩
    show ∃ B, sub708 B (win708 1 (maxA [6, 10, 15, 21])) ∧
      B.length = (wit6_10_15_21 0).length ∧
      prod708 [6, 10, 15, 21] ∣ prod708 B
    exact ⟨wit6_10_15_21 0, hsub, rfl, hcov⟩
  have henum : coverFrom (prod708 [6, 10, 15, 21]) (win708 1 (maxA [6, 10, 15, 21]))
      (4 - 1) 1 = false := by
    decide
  have hge : 4 ≤ minB [6, 10, 15, 21] 1 := by
    by_contra hlt
    have hmem2 : ∃ B, sub708 B (win708 1 (maxA [6, 10, 15, 21])) ∧
        B.length = minB [6, 10, 15, 21] 1 ∧ prod708 [6, 10, 15, 21] ∣ prod708 B :=
      Nat.sInf_mem hne
    obtain ⟨B, hsub', hlen', hcov'⟩ := hmem2
    have hcompl := e708_enum_complete (prod708 [6, 10, 15, 21])
      (win708 1 (maxA [6, 10, 15, 21])) (4 - 1) 1 B hsub' (by omega)
      (by rw [Nat.one_mul]; exact hcov')
    rw [hcompl] at henum
    exact Bool.noConfusion henum
  have hcens : minB [6, 10, 15, 21] 1 ≤ 4 :=
    e708_census_6_10_15_21 1 (by omega) (by omega)
  omega

/-- THE EXACT MIN for A = [2, 3, 5, 7] at t = 1: minB = 3. -/
theorem e708_exact_2_3_5_7 : minB [2, 3, 5, 7] 1 = 3 := by
  have hrow := (List.all_eq_true.mp hwit2_3_5_7) 0 (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [2, 3, 5, 7] (0 + 1) (maxA [2, 3, 5, 7]) 3 (wit2_3_5_7 0) hrow
  have hmemt : ∀ b, b ∈ wit2_3_5_7 0 → 1 < b ∧ b ≤ 1 + maxA [2, 3, 5, 7] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit2_3_5_7 0) (win708 1 (maxA [2, 3, 5, 7])) :=
    e708_asc_bridge 1 (maxA [2, 3, 5, 7]) (wit2_3_5_7 0) hasc hmemt
  have hne : {g : Nat | ∃ B, sub708 B (win708 1 (maxA [2, 3, 5, 7])) ∧ B.length = g ∧
      prod708 [2, 3, 5, 7] ∣ prod708 B}.Nonempty := by
    refine ⟨(wit2_3_5_7 0).length, ?_⟩
    show ∃ B, sub708 B (win708 1 (maxA [2, 3, 5, 7])) ∧
      B.length = (wit2_3_5_7 0).length ∧
      prod708 [2, 3, 5, 7] ∣ prod708 B
    exact ⟨wit2_3_5_7 0, hsub, rfl, hcov⟩
  have henum : coverFrom (prod708 [2, 3, 5, 7]) (win708 1 (maxA [2, 3, 5, 7]))
      (3 - 1) 1 = false := by
    decide
  have hge : 3 ≤ minB [2, 3, 5, 7] 1 := by
    by_contra hlt
    have hmem2 : ∃ B, sub708 B (win708 1 (maxA [2, 3, 5, 7])) ∧
        B.length = minB [2, 3, 5, 7] 1 ∧ prod708 [2, 3, 5, 7] ∣ prod708 B :=
      Nat.sInf_mem hne
    obtain ⟨B, hsub', hlen', hcov'⟩ := hmem2
    have hcompl := e708_enum_complete (prod708 [2, 3, 5, 7])
      (win708 1 (maxA [2, 3, 5, 7])) (3 - 1) 1 B hsub' (by omega)
      (by rw [Nat.one_mul]; exact hcov')
    rw [hcompl] at henum
    exact Bool.noConfusion henum
  have hcens : minB [2, 3, 5, 7] 1 ≤ 3 :=
    e708_census_2_3_5_7 1 (by omega) (by omega)
  omega

/-- THE EXACT MIN for A = [6, 10, 14, 15, 21] at t = 1: minB = 5 (n = 5). -/
theorem e708_exact_6_10_14_15_21 : minB [6, 10, 14, 15, 21] 1 = 5 := by
  have hrow := (List.all_eq_true.mp hwit6_10_14_15_21) 0 (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 14, 15, 21] (0 + 1) (maxA [6, 10, 14, 15, 21]) 5
      (wit6_10_14_15_21 0) hrow
  have hmemt : ∀ b, b ∈ wit6_10_14_15_21 0 → 1 < b ∧ b ≤ 1 + maxA [6, 10, 14, 15, 21] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_14_15_21 0) (win708 1 (maxA [6, 10, 14, 15, 21])) :=
    e708_asc_bridge 1 (maxA [6, 10, 14, 15, 21]) (wit6_10_14_15_21 0) hasc hmemt
  have hne : {g : Nat | ∃ B, sub708 B (win708 1 (maxA [6, 10, 14, 15, 21])) ∧
      B.length = g ∧ prod708 [6, 10, 14, 15, 21] ∣ prod708 B}.Nonempty := by
    refine ⟨(wit6_10_14_15_21 0).length, ?_⟩
    show ∃ B, sub708 B (win708 1 (maxA [6, 10, 14, 15, 21])) ∧
      B.length = (wit6_10_14_15_21 0).length ∧
      prod708 [6, 10, 14, 15, 21] ∣ prod708 B
    exact ⟨wit6_10_14_15_21 0, hsub, rfl, hcov⟩
  have henum : coverFrom (prod708 [6, 10, 14, 15, 21])
      (win708 1 (maxA [6, 10, 14, 15, 21])) (5 - 1) 1 = false := by
    decide
  have hge : 5 ≤ minB [6, 10, 14, 15, 21] 1 := by
    by_contra hlt
    have hmem2 : ∃ B, sub708 B (win708 1 (maxA [6, 10, 14, 15, 21])) ∧
        B.length = minB [6, 10, 14, 15, 21] 1 ∧
        prod708 [6, 10, 14, 15, 21] ∣ prod708 B :=
      Nat.sInf_mem hne
    obtain ⟨B, hsub', hlen', hcov'⟩ := hmem2
    have hcompl := e708_enum_complete (prod708 [6, 10, 14, 15, 21])
      (win708 1 (maxA [6, 10, 14, 15, 21])) (5 - 1) 1 B hsub' (by omega)
      (by rw [Nat.one_mul]; exact hcov')
    rw [hcompl] at henum
    exact Bool.noConfusion henum
  have hcens : minB [6, 10, 14, 15, 21] 1 ≤ 5 :=
    e708_census_6_10_14_15_21 1 (by omega) (by omega)
  omega

/-- THE EXACT MIN for A = [6, 10, 14, 15, 21, 35] at t = 1: minB = 5
(n = 6 K4-edge: 14·21·25·35·36 = 9261000 = prod(A) EXACTLY). -/
theorem e708_exact_6_10_14_15_21_35 : minB [6, 10, 14, 15, 21, 35] 1 = 5 := by
  have hrow := (List.all_eq_true.mp hwit6_10_14_15_21_35) 0 (List.mem_range.mpr (by omega))
  obtain ⟨hlen, hasc, hmem, hcov⟩ :=
    w708OK_spec [6, 10, 14, 15, 21, 35] (0 + 1) (maxA [6, 10, 14, 15, 21, 35]) 5
      (wit6_10_14_15_21_35 0) hrow
  have hmemt : ∀ b, b ∈ wit6_10_14_15_21_35 0 →
      1 < b ∧ b ≤ 1 + maxA [6, 10, 14, 15, 21, 35] := by
    intro b hb
    have hb2 := hmem b hb
    omega
  have hsub : sub708 (wit6_10_14_15_21_35 0) (win708 1 (maxA [6, 10, 14, 15, 21, 35])) :=
    e708_asc_bridge 1 (maxA [6, 10, 14, 15, 21, 35]) (wit6_10_14_15_21_35 0) hasc hmemt
  have hne : {g : Nat | ∃ B, sub708 B (win708 1 (maxA [6, 10, 14, 15, 21, 35])) ∧
      B.length = g ∧ prod708 [6, 10, 14, 15, 21, 35] ∣ prod708 B}.Nonempty := by
    refine ⟨(wit6_10_14_15_21_35 0).length, ?_⟩
    show ∃ B, sub708 B (win708 1 (maxA [6, 10, 14, 15, 21, 35])) ∧
      B.length = (wit6_10_14_15_21_35 0).length ∧
      prod708 [6, 10, 14, 15, 21, 35] ∣ prod708 B
    exact ⟨wit6_10_14_15_21_35 0, hsub, rfl, hcov⟩
  have henum : coverFrom (prod708 [6, 10, 14, 15, 21, 35])
      (win708 1 (maxA [6, 10, 14, 15, 21, 35])) (5 - 1) 1 = false := by
    decide
  have hge : 5 ≤ minB [6, 10, 14, 15, 21, 35] 1 := by
    by_contra hlt
    have hmem2 : ∃ B, sub708 B (win708 1 (maxA [6, 10, 14, 15, 21, 35])) ∧
        B.length = minB [6, 10, 14, 15, 21, 35] 1 ∧
        prod708 [6, 10, 14, 15, 21, 35] ∣ prod708 B :=
      Nat.sInf_mem hne
    obtain ⟨B, hsub', hlen', hcov'⟩ := hmem2
    have hcompl := e708_enum_complete (prod708 [6, 10, 14, 15, 21, 35])
      (win708 1 (maxA [6, 10, 14, 15, 21, 35])) (5 - 1) 1 B hsub' (by omega)
      (by rw [Nat.one_mul]; exact hcov')
    rw [hcompl] at henum
    exact Bool.noConfusion henum
  have hcens : minB [6, 10, 14, 15, 21, 35] 1 ≤ 5 :=
    e708_census_6_10_14_15_21_35 1 (by omega) (by omega)
  omega

/-! ## §8 THE 8 CASE ROWS (the complete instance-g statements). -/

/-- THE CASE ROW for A = [2, 3]: the instance g-value is EXACTLY 2 over
the certified range (achieved at t = 1, an upper bound throughout). -/
theorem e708_case_23 : (∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [2, 3] t = 2) ∧
    (∀ t, 1 ≤ t → t ≤ 40 → minB [2, 3] t ≤ 2) :=
  ⟨⟨1, by omega, by omega, e708_exact_23⟩, e708_census_23⟩

/-- THE CASE ROW for A = [6, 10, 15]: the instance g-value is 3. -/
theorem e708_case_6_10_15 : (∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [6, 10, 15] t = 3) ∧
    (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 15] t ≤ 3) :=
  ⟨⟨1, by omega, by omega, e708_exact_6_10_15⟩, e708_census_6_10_15⟩

/-- THE CASE ROW for A = [2, 3, 5]: the instance g-value is 3 (hard t = 24). -/
theorem e708_case_2_3_5 : (∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [2, 3, 5] t = 3) ∧
    (∀ t, 1 ≤ t → t ≤ 40 → minB [2, 3, 5] t ≤ 3) :=
  ⟨⟨24, by omega, by omega, e708_exact_2_3_5⟩, e708_census_2_3_5⟩

/-- THE CASE ROW for A = [6, 10, 14, 15]: the instance g-value is 4 —
the g(4) >= 4 evidence (an n = 4 instance forcing exactly 4). -/
theorem e708_case_6_10_14_15 : (∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [6, 10, 14, 15] t = 4) ∧
    (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 14, 15] t ≤ 4) :=
  ⟨⟨1, by omega, by omega, e708_exact_6_10_14_15⟩, e708_census_6_10_14_15⟩

/-- THE CASE ROW for A = [6, 10, 15, 21]: the instance g-value is 4. -/
theorem e708_case_6_10_15_21 : (∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [6, 10, 15, 21] t = 4) ∧
    (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 15, 21] t ≤ 4) :=
  ⟨⟨1, by omega, by omega, e708_exact_6_10_15_21⟩, e708_census_6_10_15_21⟩

/-- THE CASE ROW for A = [2, 3, 5, 7]: the instance g-value is 3. -/
theorem e708_case_2_3_5_7 : (∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [2, 3, 5, 7] t = 3) ∧
    (∀ t, 1 ≤ t → t ≤ 40 → minB [2, 3, 5, 7] t ≤ 3) :=
  ⟨⟨1, by omega, by omega, e708_exact_2_3_5_7⟩, e708_census_2_3_5_7⟩

/-- THE CASE ROW for A = [6, 10, 14, 15, 21]: the instance g-value is 5. -/
theorem e708_case_6_10_14_15_21 : (∃ t, 1 ≤ t ∧ t ≤ 40 ∧
    minB [6, 10, 14, 15, 21] t = 5) ∧
    (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 14, 15, 21] t ≤ 5) :=
  ⟨⟨1, by omega, by omega, e708_exact_6_10_14_15_21⟩, e708_census_6_10_14_15_21⟩

/-- THE CASE ROW for A = [6, 10, 14, 15, 21, 35]: the instance g-value is 5. -/
theorem e708_case_6_10_14_15_21_35 : (∃ t, 1 ≤ t ∧ t ≤ 40 ∧
    minB [6, 10, 14, 15, 21, 35] t = 5) ∧
    (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 14, 15, 21, 35] t ≤ 5) :=
  ⟨⟨1, by omega, by omega, e708_exact_6_10_14_15_21_35⟩, e708_census_6_10_14_15_21_35⟩

/-! ## §9 THE MASTER BOARD (the 16-conjunct flat assembly). -/

/-- THE g(4) LOWER BOUND — the Erdos $100 case-value lane (W60-T2c): the
four-element demand set A = [6,10,14,15] at interval start t = 1 forces every
covering battery to have size >= 4, AND a 4-battery exists — the exact local
minimum is 4, both directions. Since g(4) is the worst case over all
four-element demand sets, g(4) >= 4 — the first case-value floor beyond
ErSu59's g(2) = 2 and g(3) = 4, assembled from the K62-certified exact
minimum (the witness row + the decide-certified coverFrom exclusion). -/
theorem erdos708_g4_lower :
    ∃ (A : List Nat) (t : Nat), A.length = 4 ∧
      (∀ B : List Nat, sub708 B (win708 t (maxA A)) → B.length ≤ 3 →
         ¬ (prod708 A ∣ prod708 B)) ∧
      (∃ B : List Nat, sub708 B (win708 t (maxA A)) ∧ B.length = 4 ∧
         prod708 A ∣ prod708 B) := by
  have hmin : minB [6, 10, 14, 15] 1 = 4 := e708_exact_6_10_14_15
  refine ⟨[6, 10, 14, 15], 1, by decide, ?_, ?_⟩
  · intro B hsub hlen hdvd
    have hmem : B.length ∈ {g : Nat | ∃ B', sub708 B' (win708 1 (maxA [6, 10, 14, 15])) ∧
        B'.length = g ∧ prod708 [6, 10, 14, 15] ∣ prod708 B'} :=
      ⟨B, hsub, rfl, hdvd⟩
    have hle : minB [6, 10, 14, 15] 1 ≤ B.length := Nat.sInf_le hmem
    omega
  · have hrow := (List.all_eq_true.mp hwit6_10_14_15) 0 (List.mem_range.mpr (by omega))
    obtain ⟨hlen, hasc, hmem, hcov⟩ :=
      w708OK_spec [6, 10, 14, 15] (0 + 1) (maxA [6, 10, 14, 15]) 4 (wit6_10_14_15 0) hrow
    have hmemt : ∀ b, b ∈ wit6_10_14_15 0 → 1 < b ∧ b ≤ 1 + maxA [6, 10, 14, 15] := by
      intro b hb
      have hb2 := hmem b hb
      omega
    have hsub : sub708 (wit6_10_14_15 0) (win708 1 (maxA [6, 10, 14, 15])) :=
      e708_asc_bridge 1 (maxA [6, 10, 14, 15]) (wit6_10_14_15 0) hasc hmemt
    exact ⟨wit6_10_14_15 0, hsub, by decide, hcov⟩

/-- THE PRODUCT-DIVISIBILITY KERNEL MASTER BOARD (16 conjuncts, full
statements, unconditional): the 8 general laws (append-product,
superset, composition, refine, enumerator soundness + completeness,
window law, ascending bridge) + the 8 complete case rows (the engine's
certified worst g-values, achieved and bounded over t = 1..40), plus the
g(4) >= 4 case-value floor via erdos708_g4_lower. -/
theorem erdos708_board :
    (∀ (l₁ l₂ : List Nat), prod708 (l₁ ++ l₂) = prod708 l₁ * prod708 l₂)
    ∧ (∀ (A B C : List Nat), prod708 A ∣ prod708 B → prod708 A ∣ prod708 (B ++ C))
    ∧ (∀ (A₁ B₁ A₂ B₂ : List Nat), prod708 A₁ ∣ prod708 B₁ →
        prod708 A₂ ∣ prod708 B₂ → prod708 (A₁ ++ A₂) ∣ prod708 (B₁ ++ B₂))
    ∧ (∀ (A A' B : List Nat), prod708 A' ∣ prod708 A → prod708 A ∣ prod708 B →
        prod708 A' ∣ prod708 B)
    ∧ (∀ (P : Nat) (l : List Nat) (k acc : Nat), coverFrom P l k acc = true →
        ∃ B, sub708 B l ∧ B.length ≤ k ∧ P ∣ acc * prod708 B)
    ∧ (∀ (P : Nat) (l : List Nat) (k acc : Nat) (B : List Nat), sub708 B l →
        B.length ≤ k → P ∣ acc * prod708 B → coverFrom P l k acc = true)
    ∧ (∀ (t M b : Nat), b ∈ win708 t M ↔ t < b ∧ b ≤ t + M)
    ∧ (∀ (t M : Nat) (B : List Nat), ascB B = true →
        (∀ b, b ∈ B → t < b ∧ b ≤ t + M) → sub708 B (win708 t M))
    ∧ ((∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [2, 3] t = 2) ∧
        (∀ t, 1 ≤ t → t ≤ 40 → minB [2, 3] t ≤ 2))
    ∧ ((∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [6, 10, 15] t = 3) ∧
        (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 15] t ≤ 3))
    ∧ ((∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [2, 3, 5] t = 3) ∧
        (∀ t, 1 ≤ t → t ≤ 40 → minB [2, 3, 5] t ≤ 3))
    ∧ ((∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [6, 10, 14, 15] t = 4) ∧
        (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 14, 15] t ≤ 4))
    ∧ ((∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [6, 10, 15, 21] t = 4) ∧
        (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 15, 21] t ≤ 4))
    ∧ ((∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [2, 3, 5, 7] t = 3) ∧
        (∀ t, 1 ≤ t → t ≤ 40 → minB [2, 3, 5, 7] t ≤ 3))
    ∧ ((∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [6, 10, 14, 15, 21] t = 5) ∧
        (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 14, 15, 21] t ≤ 5))
    ∧ ((∃ t, 1 ≤ t ∧ t ≤ 40 ∧ minB [6, 10, 14, 15, 21, 35] t = 5) ∧
        (∀ t, 1 ≤ t → t ≤ 40 → minB [6, 10, 14, 15, 21, 35] t ≤ 5)) :=
  ⟨e708_prod_append, e708_superset_law, e708_composition_law, e708_refine_law,
    e708_enum_sound, e708_enum_complete, e708_window_law, e708_asc_bridge,
    e708_case_23, e708_case_6_10_15, e708_case_2_3_5, e708_case_6_10_14_15,
    e708_case_6_10_15_21, e708_case_2_3_5_7, e708_case_6_10_14_15_21,
    e708_case_6_10_14_15_21_35⟩

/-! ## §10 THE RECEIPTS. -/

#print axioms E708.erdos708_g4_lower
#print axioms E708.e708_prod_append
#print axioms E708.e708_superset_law
#print axioms E708.e708_composition_law
#print axioms E708.e708_refine_law
#print axioms E708.e708_enum_sound
#print axioms E708.e708_enum_complete
#print axioms E708.e708_window_law
#print axioms E708.e708_asc_bridge
#print axioms E708.w708OK_spec
#print axioms E708.hwit23
#print axioms E708.hwit6_10_15
#print axioms E708.hwit2_3_5
#print axioms E708.hwit6_10_14_15
#print axioms E708.hwit6_10_15_21
#print axioms E708.hwit2_3_5_7
#print axioms E708.hwit6_10_14_15_21
#print axioms E708.hwit6_10_14_15_21_35
#print axioms E708.e708_census_23
#print axioms E708.e708_census_6_10_15
#print axioms E708.e708_census_2_3_5
#print axioms E708.e708_census_6_10_14_15
#print axioms E708.e708_census_6_10_15_21
#print axioms E708.e708_census_2_3_5_7
#print axioms E708.e708_census_6_10_14_15_21
#print axioms E708.e708_census_6_10_14_15_21_35
#print axioms E708.e708_exact_23
#print axioms E708.e708_exact_6_10_15
#print axioms E708.e708_exact_2_3_5
#print axioms E708.e708_exact_6_10_14_15
#print axioms E708.e708_exact_6_10_15_21
#print axioms E708.e708_exact_2_3_5_7
#print axioms E708.e708_exact_6_10_14_15_21
#print axioms E708.e708_exact_6_10_14_15_21_35
#print axioms E708.e708_case_23
#print axioms E708.e708_case_6_10_15
#print axioms E708.e708_case_2_3_5
#print axioms E708.e708_case_6_10_14_15
#print axioms E708.e708_case_6_10_15_21
#print axioms E708.e708_case_2_3_5_7
#print axioms E708.e708_case_6_10_14_15_21
#print axioms E708.e708_case_6_10_14_15_21_35
#print axioms E708.erdos708_board

#eval "E708_KERNEL_GREEN"

/-- THE FINAL RECEIPT CONSTANT (Kernel 62, #708): the product-divisibility
window kernel stands COMPLETE — the 8 general laws (predicate closure:
append-product, superset, composition, demand-refinement; the enumerator
duality: soundness + completeness; the window law + the ascending bridge)
+ the 8 complete case rows (the engine's certified worst g-values 2, 3, 3,
4, 4, 3, 5, 5 — ACHIEVED at the hard windows t₀ = 1 (t₀ = 24 for [2,3,5])
and an upper bound over the whole certified range t = 1..40), zero sorry,
zero admit, decide-certified evidence rows (8 x 40 witness-table rows +
8 exclusion enumerations). -/
def E708_PRODUCT_DIVISIBILITY_GREEN : String := "E708_PRODUCT_DIVISIBILITY_GREEN"

#eval E708_PRODUCT_DIVISIBILITY_GREEN

end E708


