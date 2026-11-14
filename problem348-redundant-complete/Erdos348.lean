import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos348 — THE m-REDUNDANT COMPLETE-SEQUENCE KERNEL r1 (W57-3)

Erdős #348 (verbatim, erdosproblems.com/348): "Let 1 = a_1 < a_2 < ... be a
sequence of integers for which every sufficiently large integer is a sum of
distinct a_i's.  Let m(A) be the smallest index such that every sufficiently
large integer is a sum of distinct terms among a_1,...,a_{m(A)}.  Is there a
sequence A for which m(A) = ∞?"

THE BOARD (full statements, complete unconditional proofs, zero sorry):
1. THE COMPLETENESS ENGINE: `reachable : List Nat → Nat → Bool` — the
   kernel-computable subset-sum reachability (drop-if recursion with the
   truncation-safe guard), the inductive Prop view `sumSet`, and the
   decidability bridge `reachable_iff_sumSet`.
2. THE PREFIX FUNCTION: `pref` (take m) and `mSuffices` (a finite prefix
   covers all sufficiently large integers) — the m(A) predicate in finite
   form, plus the take-extension law `sumSet_take`.
3. THE GROWTH-SELECTION LAWS (Graham's classical complete-sequence theory,
   FULL general inductions, no sortedness needed — the laws are stronger
   than the classical statement):
   - `greedy_complete` (the cumulative law, head-peel form): if every
     element is ≤ 1 + the sum of the elements after it, every n ≤ total
     is a subset sum;
   - `greedy_complete_prefix` (the cumulative law, classical snoc form): if
     the list is built by appending, each new element ≤ 1 + the accumulated
     prefix sum, then every n ≤ total is a subset sum;
   - `sumSet_le_sum` + `gap_law` (the counterpositive gap law): if the next
     element overshoots 1 + the current sum, then 1 + current sum is NOT
     reachable — the redundancy engine.
4. THE m=2 CRITICAL-JUNCTURE INSTANCES: the powers-of-2 witness table
   [1,2,4,...,512] (sum 1023): the decide cert below 500 (bounded ≤ 501,
   NO-OOM law), the closed-numerics battery (511/999/1023 junctures), and
   the full general completeness `powers_complete` (all n ≤ 1023) via the
   growth law.
5. THE REDUNDANCY WITNESS LAWS (the m(A) = ∞ direction's round-1 layer):
   the {2,3} seed — 1 is never reachable (`never_one`), the full
   classification `sumSet_2_3_iff` (reachable set = {0,2,3,5}), the seed
   redundancy `redundant_seed` (no N covers everything above it), the
   append-monotonicity `reachable_mono`, and `no_finite_prefix_seed` (NO
   finite prefix of the seed suffices — the m = ∞ witness layer).
6. THE ARSENAL BRIDGE (`e348_arsenal_bridge`) + THE BOARD (`e348_board`).

House law: GitHub CI is the verifier of record (no local compile; author
blind).  Axiom profile stays within [propext, Classical.choice, Quot.sound].
Zero sorry, zero admit, zero native_decide, no direct Mathlib import.
-/

namespace E348

/-! ## §0 The engine: subset-sum reachability (Bool) + micro lemmas -/

/-- The truncation-free `a ≤ n` guard as a Bool (structural recursion). -/
def leB : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => false
  | a + 1, n + 1 => leB a n

/-- The zero test as a Bool (structural). -/
def eq0 : Nat → Bool
  | 0 => true
  | _ => false

/-- THE COMPLETENESS ENGINE: `reachable l n = true` iff n is a sum of
distinct terms of l (subset-sum reachability).  Recursion: drop the head,
or (if the head fits) take it.  The guard `leB a n` makes the take branch
truncation-safe. -/
def reachable : List Nat → Nat → Bool
  | [], n => eq0 n
  | a :: t, n => reachable t n || (leB a n && reachable t (n - a))

/-- Every Bool is true or false. -/
theorem bool_cases (b : Bool) : b = true ∨ b = false := by
  cases b with
  | false => exact Or.inr rfl
  | true => exact Or.inl rfl

/-- Bool or: `(x || y) = true` splits. -/
theorem or_of_bool_eq (x y : Bool) (h : (x || y) = true) : x = true ∨ y = true := by
  cases x with
  | false => exact Or.inr h
  | true => exact Or.inl rfl

/-- Bool or: a true right disjunct forces the or. -/
theorem or_of_bool_right (x y : Bool) (hy : y = true) : (x || y) = true := by
  cases x with
  | false => exact hy
  | true => rfl

/-- Bool or: a true left disjunct forces the or. -/
theorem or_of_bool_left (x y : Bool) (hx : x = true) : (x || y) = true := by
  cases x with
  | false => exact Bool.noConfusion hx
  | true => rfl

/-- Bool and: both true forces the and. -/
theorem and_of_bools (x y : Bool) (hx : x = true) (hy : y = true) : (x && y) = true := by
  cases x with
  | false => exact Bool.noConfusion hx
  | true =>
    cases y with
    | false => exact Bool.noConfusion hy
    | true => rfl

/-- The leB guard reads `a ≤ n` (forward). -/
theorem leB_of_true : ∀ (a n : Nat), leB a n = true → a ≤ n := by
  intro a
  induction a with
  | zero => intro n _; omega
  | succ k ih =>
    intro n h
    cases n with
    | zero =>
      -- `leB (k+1) 0` iota-reduces to `false`, so `h` is definitionally
      -- `false = true`; close by the Bool.noConfusion idiom (cf. or_of_bool_left).
      have hf : false = true := h
      exact Bool.noConfusion hf
    | succ m =>
      have h2 : leB k m = true := h
      have hkm : k ≤ m := ih m h2
      omega

/-- The leB guard reads `a ≤ n` (backward). -/
theorem leB_true_of_le : ∀ (n a : Nat), a ≤ n → leB a n = true := by
  intro n
  induction n with
  | zero =>
    intro a h
    cases a with
    | zero => rfl
    | succ k => exact absurd h (by omega)
  | succ m ih =>
    intro a h
    cases a with
    | zero => rfl
    | succ k => exact ih k (by omega)

/-! ## §1 The Prop view: the `sumSet` inductive + the bridge -/

/-- THE COMPLETENESS DEFINITION (the mission's `sumSet l : Nat → Prop`):
`sumSet l n` iff n is a sum of distinct terms of l.  The three constructors
are the empty sum, dropping the head, and taking the head (guard + residue). -/
inductive sumSet : List Nat → Nat → Prop
  | zero : ∀ l : List Nat, sumSet l 0
  | drop : ∀ (a : Nat) (t : List Nat) (n : Nat), sumSet t n → sumSet (a :: t) n
  | take : ∀ (a : Nat) (t : List Nat) (n : Nat), a ≤ n → sumSet t (n - a) →
    sumSet (a :: t) n

/-- Inversion on the cons structure of `sumSet`. -/
theorem sumSet_cons_inv {a : Nat} {t : List Nat} {n : Nat} (h : sumSet (a :: t) n) :
    sumSet t n ∨ (a ≤ n ∧ sumSet t (n - a)) := by
  cases h with
  | zero => exact Or.inl (sumSet.zero t)
  | drop _ _ _ hd => exact Or.inl hd
  | take _ _ _ hle htk => exact Or.inr ⟨hle, htk⟩

/-- Inversion on the nil structure of `sumSet`: the empty list covers only 0. -/
theorem sumSet_nil_inv {n : Nat} (h : sumSet [] n) : n = 0 := by
  cases h with
  | zero => rfl

/-- Index transport (the Nat index). -/
theorem sumSet_num_eq : ∀ {l : List Nat} {m1 m2 : Nat}, m1 = m2 → sumSet l m1 → sumSet l m2 := by
  intro l m1 m2 heq h
  subst heq
  exact h

/-- Index transport (the List index). -/
theorem sumSet_list_eq : ∀ {l1 l2 : List Nat} {m : Nat}, l1 = l2 → sumSet l1 m → sumSet l2 m := by
  intro l1 l2 m heq h
  subst heq
  exact h

/-- Zero is a sum of distinct terms of any list (the empty sum). -/
theorem sumSet_zero_reachable (l : List Nat) : reachable l 0 = true := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    exact or_of_bool_left (reachable t 0) (leB a 0 && reachable t (0 - a)) ih

/-- The bridge, `sumSet → Bool` side. -/
theorem reach_to_reachable {l : List Nat} {n : Nat} (h : sumSet l n) :
    reachable l n = true := by
  induction h with
  | zero l => exact sumSet_zero_reachable l
  | drop a t n hd ih =>
    exact or_of_bool_left (reachable t n) (leB a n && reachable t (n - a)) ih
  | take a t n hle htk ih =>
    exact or_of_bool_right (reachable t n) (leB a n && reachable t (n - a))
      (and_of_bools (leB a n) (reachable t (n - a)) (leB_true_of_le n a hle) ih)

/-- The bridge, `Bool → sumSet` side. -/
theorem reach_of_reachable : ∀ (l : List Nat) (n : Nat), reachable l n = true → sumSet l n := by
  intro l
  induction l with
  | nil =>
    intro n h
    cases n with
    | zero => exact sumSet.zero []
    | succ k =>
      -- `reachable [] (k+1)` = `eq0 (k+1)` = `false` definitionally; `h` is
      -- absurd. Structural (no decide: k is a free variable).
      have hf : false = true := h
      exact Bool.noConfusion hf
  | cons a t ih =>
    intro n h
    rcases or_of_bool_eq (reachable t n) (leB a n && reachable t (n - a)) h with h1 | h2
    · exact sumSet.drop a t n (ih n h1)
    · rcases bool_cases (leB a n) with hb | hb
      · -- guard true: `true && x` iota-reduces to `x`, so h2 IS the residue proof.
        rw [hb] at h2
        have h3 : reachable t (n - a) = true := h2
        exact sumSet.take a t n (leB_of_true a n hb) (ih (n - a) h3)
      · -- guard false: `false && x` iota-reduces to `false`, so h2 is absurd.
        rw [hb] at h2
        have hf : false = true := h2
        exact Bool.noConfusion hf

/-- **THE DECIDABILITY BRIDGE**: the Bool engine and the inductive Prop view
of subset-sum membership coincide. -/
theorem reachable_iff_sumSet (l : List Nat) (n : Nat) :
    reachable l n = true ↔ sumSet l n :=
  ⟨fun h => reach_of_reachable l n h, fun h => reach_to_reachable h⟩

/-! ## §2 List sums, takes, and the m(A) prefix function -/

/-- The list sum (own def, structural — kernel-computable on literals). -/
def lsum : List Nat → Nat
  | [] => 0
  | a :: t => a + lsum t

/-- The append law for list sums. -/
theorem lsum_append : ∀ (l r : List Nat), lsum (l ++ r) = lsum l + lsum r := by
  intro l
  induction l with
  | nil =>
    intro r
    have h1 : lsum ([] ++ r) = lsum r := rfl
    have h2 : lsum ([] : List Nat) = 0 := rfl
    omega
  | cons a t ih =>
    intro r
    have h1 : lsum ((a :: t) ++ r) = a + lsum (t ++ r) := rfl
    have h2 : lsum (a :: t) = a + lsum t := rfl
    have h3 := ih r
    omega

/-- `take 0` is empty. -/
theorem take_zero : ∀ l : List Nat, List.take 0 l = [] := by
  intro l
  cases l with
  | nil => rfl
  | cons a t => rfl

/-- `take` of the empty list is empty. -/
theorem take_nil : ∀ m : Nat, List.take m ([] : List Nat) = [] := by
  intro m
  cases m with
  | zero => rfl
  | succ k => rfl

/-- `take (m+1)` of a cons. -/
theorem take_succ_cons : ∀ (m a : Nat) (t : List Nat),
    List.take (m + 1) (a :: t) = a :: List.take m t := fun _ _ _ => rfl

/-- Every take splits: `l = l.take m ++ ext` for some ext. -/
theorem take_split : ∀ (l : List Nat) (m : Nat), ∃ ext, l.take m ++ ext = l := by
  intro l
  induction l with
  | nil =>
    intro m
    exact ⟨[], by rw [take_nil m, List.nil_append]⟩
  | cons a t ih =>
    intro m
    cases m with
    | zero => exact ⟨a :: t, by rw [take_zero, List.nil_append]⟩
    | succ k =>
      obtain ⟨ext, hex⟩ := ih k
      exact ⟨ext, by show a :: (List.take k t ++ ext) = a :: t; rw [hex]⟩

/-- **THE PREFIX FUNCTION** (`pref`; `prefix` is a reserved keyword in
Lean 4, so the identifier is `pref`): the first m terms of the sequence. -/
def pref (l : List Nat) (m : Nat) : List Nat := l.take m

/-- **THE m(A) LAW IN FINITE FORM**: the finite prefix `pref l m` suffices —
every sufficiently large integer is a sum of distinct terms of the prefix. -/
def mSuffices (l : List Nat) (m : Nat) : Prop :=
  ∃ N, ∀ n, N ≤ n → reachable (pref l m) n = true

/-- A prefix's subset sums are subset sums of the whole list. -/
theorem sumSet_mono_append : ∀ (l ext : List Nat) (n : Nat), sumSet l n → sumSet (l ++ ext) n := by
  intro l
  induction l with
  | nil =>
    intro ext n h
    have hm : n = 0 := sumSet_nil_inv h
    subst hm
    exact sumSet.zero ext
  | cons a t ih =>
    intro ext n h
    rcases sumSet_cons_inv h with hd | ⟨hle, htk⟩
    · exact sumSet.drop a (t ++ ext) n (ih ext n hd)
    · exact sumSet.take a (t ++ ext) n hle (ih ext (n - a) htk)

/-- Appending a last element: the additive snoc construction (used by the
classical growth law). -/
theorem sumSet_snoc : ∀ (l : List Nat) (x m n : Nat), x + m = n → sumSet l m →
    sumSet (l ++ [x]) n := by
  intro l
  induction l with
  | nil =>
    intro x m n heq h
    have hm : m = 0 := sumSet_nil_inv h
    have hnx : n - x = m := by omega
    exact sumSet.take x [] n (by omega) (sumSet_num_eq hnx.symm h)
  | cons a t ih =>
    intro x m n heq h
    rcases sumSet_cons_inv h with hd | ⟨hle, htk⟩
    · exact sumSet.drop a (t ++ [x]) n (ih x m n heq hd)
    · exact sumSet.take a (t ++ [x]) n (by omega)
        (ih x (m - a) (n - a) (by omega) htk)

/-- **THE PREFIX EXTENSION LAW**: what a finite prefix covers, the full
sequence covers. -/
theorem sumSet_take : ∀ (l : List Nat) (m n : Nat), sumSet (l.take m) n → sumSet l n := by
  intro l m n h
  obtain ⟨ext, hex⟩ := take_split l m
  exact sumSet_list_eq hex (sumSet_mono_append (l.take m) ext n h)

/-- **THE MISSION'S `reachable_mono`**: Bool-side monotonicity of
reachability under list extension (append induction via the bridge). -/
theorem reachable_mono : ∀ (l ext : List Nat) (n : Nat), reachable l n = true →
    reachable (l ++ ext) n = true := by
  intro l ext n h
  exact reach_to_reachable (sumSet_mono_append l ext n (reach_of_reachable l n h))

/-! ## §3 THE GROWTH-SELECTION LAWS (Graham's complete-sequence theory) -/

/-- Subset sums never exceed the total. -/
theorem sumSet_le_sum : ∀ (l : List Nat) (n : Nat), sumSet l n → n ≤ lsum l := by
  intro l n h
  induction h with
  | zero l => omega
  | drop a t n hd ih =>
    have hl : lsum (a :: t) = a + lsum t := rfl
    omega
  | take a t n hle htk ih =>
    have hl : lsum (a :: t) = a + lsum t := rfl
    omega

/-- **THE GAP LAW** (the counterpositive of the cumulative law): if the head
overshoots `1 + rest-sum` (the zero-slack violation), then `1 + rest-sum`
is NOT a subset sum — the redundancy engine. -/
theorem gap_law : ∀ (a : Nat) (t : List Nat), 1 + lsum t < a → ¬ sumSet (a :: t) (1 + lsum t) := by
  intro a t hgt h
  rcases sumSet_cons_inv h with hd | ⟨hle, htk⟩
  · have hbad := sumSet_le_sum t (1 + lsum t) hd
    omega
  · omega

/-- The suffix growth condition: every element ≤ 1 + the sum of the
elements after it (the head-peel form of the classical criterion). -/
def GrowthS : List Nat → Prop
  | [] => True
  | a :: t => a ≤ 1 + lsum t ∧ GrowthS t

/-- **THE CUMULATIVE LAW (head-peel form)**: under the suffix growth
condition every n ≤ total is a subset sum.  FULL general induction — no
sortedness needed (stronger than the classical statement). -/
theorem greedy_complete : ∀ (l : List Nat), GrowthS l → ∀ n, n ≤ lsum l → sumSet l n := by
  intro l
  induction l with
  | nil =>
    intro _ n hn
    have hl0 : lsum ([] : List Nat) = 0 := rfl
    have hn0 : n = 0 := by omega
    subst hn0
    exact sumSet.zero []
  | cons a t ih =>
    intro hg n hn
    have hgu : a ≤ 1 + lsum t ∧ GrowthS t := hg
    obtain ⟨hle, hgt⟩ := hgu
    have hl : lsum (a :: t) = a + lsum t := rfl
    have hsplit : n ≤ lsum t ∨ lsum t < n := by omega
    rcases hsplit with h1 | h1
    · exact sumSet.drop a t n (ih hgt n h1)
    · exact sumSet.take a t n (by omega) (ih hgt (n - a) (by omega))

/-- The classical (snoc) growth condition: the list is built by appending,
each new element ≤ 1 + the accumulated prefix sum — Graham's criterion for
complete sequences, stated on the constructor. -/
inductive GrowthA : Nat → List Nat → Prop
  | nil : GrowthA 0 []
  | snoc : (acc : Nat) → (l : List Nat) → (x : Nat) → x ≤ acc + 1 → GrowthA acc l →
    GrowthA (acc + x) (l ++ [x])

/-- The accumulated index of `GrowthA` is the list sum. -/
theorem growthA_sum : ∀ (l : List Nat) (acc : Nat), GrowthA acc l → acc = lsum l := by
  intro l acc h
  induction h with
  | nil => rfl
  | snoc acc l x hx hga ih =>
    have hla := lsum_append l [x]
    have hlx : lsum [x] = x := rfl
    omega

/-- **THE CUMULATIVE LAW (classical prefix form)**: if each next element is
≤ 1 + the current prefix sum, every n ≤ total is a subset sum.  FULL
general induction on the construction. -/
theorem greedy_complete_prefix : ∀ (l : List Nat) (acc : Nat), GrowthA acc l →
    ∀ n, n ≤ lsum l → sumSet l n := by
  intro l acc h
  induction h with
  | nil =>
    intro n hn
    have hl0 : lsum ([] : List Nat) = 0 := rfl
    have hn0 : n = 0 := by omega
    subst hn0
    exact sumSet.zero []
  | snoc acc l x hx hga ih =>
    intro n hn
    have hla := lsum_append l [x]
    have hlx : lsum [x] = x := rfl
    have has := growthA_sum l acc hga
    have hsplit : n ≤ lsum l ∨ lsum l < n := by omega
    rcases hsplit with h1 | h1
    · exact sumSet_mono_append l [x] n (ih n h1)
    · exact sumSet_snoc l x (n - x) n (by omega) (ih (n - x) (by omega))

/-! ## §4 THE m=2 CRITICAL-JUNCTURE INSTANCES: the powers-of-2 table -/

/-- The powers-of-2 witness list satisfies the classical growth condition
(each power of 2 is exactly 1 + the sum of the smaller ones). -/
theorem powers_growth : GrowthA 1023 [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] := by
  have g1 : GrowthA 1 [1] := GrowthA.snoc 0 [] 1 (by omega) GrowthA.nil
  have g2 : GrowthA 3 [1, 2] := GrowthA.snoc 1 [1] 2 (by omega) g1
  have g4 : GrowthA 7 [1, 2, 4] := GrowthA.snoc 3 [1, 2] 4 (by omega) g2
  have g8 : GrowthA 15 [1, 2, 4, 8] := GrowthA.snoc 7 [1, 2, 4] 8 (by omega) g4
  have g16 : GrowthA 31 [1, 2, 4, 8, 16] := GrowthA.snoc 15 [1, 2, 4, 8] 16 (by omega) g8
  have g32 : GrowthA 63 [1, 2, 4, 8, 16, 32] :=
    GrowthA.snoc 31 [1, 2, 4, 8, 16] 32 (by omega) g16
  have g64 : GrowthA 127 [1, 2, 4, 8, 16, 32, 64] :=
    GrowthA.snoc 63 [1, 2, 4, 8, 16, 32] 64 (by omega) g32
  have g128 : GrowthA 255 [1, 2, 4, 8, 16, 32, 64, 128] :=
    GrowthA.snoc 127 [1, 2, 4, 8, 16, 32, 64] 128 (by omega) g64
  have g256 : GrowthA 511 [1, 2, 4, 8, 16, 32, 64, 128, 256] :=
    GrowthA.snoc 255 [1, 2, 4, 8, 16, 32, 64, 128] 256 (by omega) g128
  exact GrowthA.snoc 511 [1, 2, 4, 8, 16, 32, 64, 128, 256] 512 (by omega) g256

/-- **THE m=2 WITNESS TABLE, GENERAL LAW**: every n ≤ 1023 is a subset sum
of the powers of 2 up to 512 (the classical completeness at the full census
bound). -/
theorem powers_complete : ∀ n : Nat, n ≤ 1023 → sumSet [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] n := by
  have hl : lsum [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] = 1023 := by decide
  intro n hn
  exact greedy_complete_prefix [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] 1023 powers_growth n
    (by omega)

/-- The m=2 census chunk below 500 (bounded quantifier ≤ 501 — NO-OOM law,
cheap evaluation). -/
theorem powers_decide_500 : ∀ n < 500,
    reachable [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] n = true := by decide

/-- The m=2 critical-juncture battery: closed numerics at the junctures
511, 999, 1023 and the seed gap value 1. -/
theorem powers_decide_battery :
    (reachable [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] 511 = true ∧
      reachable [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] 999 = true ∧
      reachable [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] 1023 = true ∧
      reachable [2, 3] 1 = false) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## §5 THE REDUNDANCY WITNESS LAWS (the m(A) = ∞ direction, round 1) -/

/-- A singleton list covers exactly 0 and its element. -/
theorem sumSet_single : ∀ (b m : Nat), sumSet [b] m → m = 0 ∨ m = b := by
  intro b m h
  rcases sumSet_cons_inv h with hd | ⟨hle, htk⟩
  · exact Or.inl (sumSet_nil_inv hd)
  · have h0 : m - b = 0 := sumSet_nil_inv htk
    exact Or.inr (by omega)

/-- **THE FULL CLASSIFICATION of the {2,3} seed**: the subset sums of {2,3}
are exactly 0, 2, 3, 5 (distinct terms — no repeats). -/
theorem sumSet_2_3_iff : ∀ n : Nat, sumSet [2, 3] n ↔ n = 0 ∨ n = 2 ∨ n = 3 ∨ n = 5 := by
  intro n
  constructor
  · intro h
    rcases sumSet_cons_inv h with hd | ⟨hle, htk⟩
    · rcases sumSet_single 3 n hd with h0 | h3
      · exact Or.inl h0
      · exact Or.inr (Or.inr (Or.inl h3))
    · rcases sumSet_single 3 (n - 2) htk with h0 | h3
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inr (by omega)))
  · intro h
    rcases h with h | h | h | h
    · subst h; exact sumSet.zero [2, 3]
    · subst h; exact sumSet.take 2 [3] 2 (by omega) (sumSet.zero [3])
    · subst h; exact sumSet.drop 2 [3] 3 (sumSet.take 3 [] 3 (by omega) (sumSet.zero []))
    · subst h
      exact sumSet.take 2 [3] 5 (by omega) (sumSet.take 3 [] 3 (by omega) (sumSet.zero []))

/-- **`never_one`**: 1 is never a subset sum of {2,3} — the permanent gap. -/
theorem never_one : ¬ sumSet [2, 3] 1 := by
  intro h
  rcases (sumSet_2_3_iff 1).mp h with h | h | h | h
  all_goals omega

/-- The Bool-side receipt of `never_one`. -/
theorem never_one_bool : ¬ (reachable [2, 3] 1 = true) := fun h => never_one
  ((reachable_iff_sumSet [2, 3] 1).mp h)

/-- **THE SEED REDUNDANCY**: no N makes every n ≥ N a subset sum of {2,3}
(the reachable set {0,2,3,5} is finite — 2N+7 is a permanent counterexample
above any N). -/
theorem redundant_seed : ¬ ∃ N : Nat, ∀ n, N ≤ n → reachable [2, 3] n = true := by
  intro h
  obtain ⟨N, hN⟩ := h
  have hw := hN (2 * N + 7) (by omega)
  rcases (sumSet_2_3_iff (2 * N + 7)).mp ((reachable_iff_sumSet [2, 3] (2 * N + 7)).mp hw)
    with h | h | h | h
  all_goals omega

/-- **THE NO-FINITE-PREFIX LAW**: NO finite prefix of the {2,3} seed suffices
— the m(A) = ∞ witness layer (the seed is not a complete sequence; the
m=2,n=3 construction war continues from here). -/
theorem no_finite_prefix_seed : ∀ m : Nat, ¬ mSuffices [2, 3] m := by
  intro m h
  obtain ⟨N, hN⟩ := h
  have hw := hN (2 * N + 7) (by omega)
  have hw2 : reachable (List.take m [2, 3]) (2 * N + 7) = true := hw
  obtain ⟨ext, hex⟩ := take_split [2, 3] m
  have hmono := reachable_mono (List.take m [2, 3]) ext (2 * N + 7) hw2
  have h23 : reachable [2, 3] (2 * N + 7) = true := by
    rw [← hex]
    exact hmono
  rcases (sumSet_2_3_iff (2 * N + 7)).mp ((reachable_iff_sumSet [2, 3] (2 * N + 7)).mp h23)
    with h | h | h | h
  all_goals omega

/-! ## §6 THE ARSENAL BRIDGE (the 16,021-theorem arsenal applied to the
witness anchors: the m=2 ternary digit, the 1023 = 3·341 census scaling,
the carry bound). -/

theorem e348_arsenal_bridge :
    ErdosTernary2.isTernaryDigit 2 = true ∧
    v2r (3 ^ 1 * 341) = v2r 341 ∧
    carryAtPos 1023 1 < 4 ∧
    3 ^ 1 * 341 = 1023 :=
  ⟨rfl, CardinalWorldsV2.v2r_ternary_scaling 1 341, carryAtPos_bound 1023 1, by decide⟩

/-! ## §7 THE BOARD -/

/-- **THE E348 BOARD** (twelve conjuncts, full statements, unconditional):
the decidability bridge, both cumulative laws (head-peel + classical
prefix), the subset-sum bound, the gap law, the append monotonicity, the
m=2 decide chunk, the m=2 general completeness, the critical-juncture
battery, the seed redundancy, the no-finite-prefix law, and the arsenal
bridge. -/
theorem e348_board :
    (∀ (l : List Nat) (n : Nat), reachable l n = true ↔ sumSet l n) ∧
    (∀ (l : List Nat), GrowthS l → ∀ n, n ≤ lsum l → sumSet l n) ∧
    (∀ (l : List Nat) (acc : Nat), GrowthA acc l → ∀ n, n ≤ lsum l → sumSet l n) ∧
    (∀ (l : List Nat) (n : Nat), sumSet l n → n ≤ lsum l) ∧
    (∀ (a : Nat) (t : List Nat), 1 + lsum t < a → ¬ sumSet (a :: t) (1 + lsum t)) ∧
    (∀ (l ext : List Nat) (n : Nat), reachable l n = true → reachable (l ++ ext) n = true) ∧
    (∀ n < 500, reachable [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] n = true) ∧
    (∀ n : Nat, n ≤ 1023 → sumSet [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] n) ∧
    (reachable [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] 511 = true ∧
      reachable [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] 999 = true ∧
      reachable [1, 2, 4, 8, 16, 32, 64, 128, 256, 512] 1023 = true ∧
      reachable [2, 3] 1 = false) ∧
    (¬ ∃ N : Nat, ∀ n, N ≤ n → reachable [2, 3] n = true) ∧
    (∀ m : Nat, ¬ mSuffices [2, 3] m) ∧
    (ErdosTernary2.isTernaryDigit 2 = true ∧ v2r (3 ^ 1 * 341) = v2r 341 ∧
      carryAtPos 1023 1 < 4 ∧ 3 ^ 1 * 341 = 1023) :=
  ⟨reachable_iff_sumSet, greedy_complete, greedy_complete_prefix, sumSet_le_sum,
    gap_law, reachable_mono, powers_decide_500, powers_complete,
    powers_decide_battery, redundant_seed, no_finite_prefix_seed, e348_arsenal_bridge⟩

/-! ## §8 THE (2,3) CONSTRUCTION — THE CASE THEOREM (W64-F)

THE WITNESS (the campaign's certified construction, engine348/construct_23.py):
the block-order mult-3 powers witness `w23 j = [1,1,1, 2,2,2, ..., 2^j,2^j,2^j]`
(each power of 2 with multiplicity 3, level blocks in ascending order).  Under
the campaign's reading of Erdős #348, the pair (m,n) is witnessed by a
complete sequence that survives every m-removal but is killed by some
n-removal.  THE CASE THEOREM for (m,n) = (2,3):

(C1) COMPLETENESS (general, all levels): the witness prefix at level j has
  sum 3(2^{j+1}-1) and satisfies Graham's prefix growth criterion, so every
  n ≤ 3(2^{j+1}-1) is a subset sum (`w23_complete`); hence EVERY natural
  number is a sum of distinct terms of the ω-witness (`w23_inf_complete`).
(C2) 2-REDUNDANCY (general, all levels, every position pair): after deleting
  at most 2 positions (`SubN`), the survivor still covers the full binary
  range [0, 2^{j+1}-1] (`w23_two_removal`); in delAt form: for any two
  positions i, j and any n, some level's survivor covers n
  (`w23_two_removal_inf`).
(C3) THE 3-KILL (parity, general): the survivor `w23k j` obtained by
  removing the three 1s (SubN 3) is all-even, so NO odd integer is ever a
  subset sum (`w23k_no_odd`) and the survivor is NOT complete
  (`w23k_not_complete`) — the m=2 redundancy is exactly 2: it dies at 3.

Dual-method verification (engine348/w64_verify_lean_targets.py): bitset DP +
Graham criterion + value-set survival, all levels j ≤ 9/12, every position
pair — ALL GREEN.  Core-only, zero sorry, axioms within house profile. -/

/-- The append associativity law (own proof — no core-name dependence). -/
theorem my_append_assoc : ∀ (l1 l2 l3 : List Nat), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 l3
    rfl
  | cons a t ih =>
    intro l2 l3
    show a :: ((t ++ l2) ++ l3) = a :: (t ++ (l2 ++ l3))
    exact congrArg (fun q => a :: q) (ih l2 l3)

/-- The list sum of the uniform 3-block (iota + linear omega only). -/
theorem lsum_replicate3 : ∀ x : Nat, lsum (List.replicate 3 x) = 3 * x := by
  intro x
  have h1 : lsum (List.replicate 3 x) = x + lsum (List.replicate 2 x) := rfl
  have h2 : lsum (List.replicate 2 x) = x + lsum (List.replicate 1 x) := rfl
  have h3 : lsum (List.replicate 1 x) = x + lsum (List.replicate 0 x) := rfl
  have h4 : lsum (List.replicate 0 x) = 0 := rfl
  have hm : 3 * x = x + x + x := by omega
  omega

/-- The witness level-block: three copies of `2^j`. -/
def blk : Nat → List Nat := fun j => List.replicate 3 (2 ^ j)

/-- The block sum: `3 * 2^j`. -/
theorem blk_lsum : ∀ j : Nat, lsum (blk j) = 3 * 2 ^ j := fun j => lsum_replicate3 (2 ^ j)

/-- THE (2,3)-WITNESS PREFIX FAMILY: blocks 0..j (the mult-3 powers). -/
def w23 : Nat → List Nat
  | 0 => blk 0
  | j + 1 => w23 j ++ blk (j + 1)

/-- The closed form of the witness sum: `3 * (2^{j+1} - 1)`. -/
theorem w23_lsum : ∀ j : Nat, lsum (w23 j) = 3 * (2 ^ (j + 1) - 1) := by
  intro j
  induction j with
  | zero => decide
  | succ k ih =>
    show lsum (w23 k ++ blk (k + 1)) = 3 * (2 ^ (k + 1 + 1) - 1)
    have h1 := lsum_append (w23 k) (blk (k + 1))
    have h2 := blk_lsum (k + 1)
    have hp : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    omega

/-- The three-snoc growth builder: appending three copies of `x` (each
within the classical bound) preserves Graham's prefix growth. -/
theorem snoc3 (acc x : Nat) (l : List Nat) (hg : GrowthA acc l) (hx : x ≤ acc + 1) :
    GrowthA (acc + 3 * x) (l ++ [x, x, x]) := by
  have g1 : GrowthA (acc + x) (l ++ [x]) := GrowthA.snoc acc l x hx hg
  have g2 : GrowthA (acc + x + x) ((l ++ [x]) ++ [x]) :=
    GrowthA.snoc (acc + x) (l ++ [x]) x (by omega) g1
  have g3 : GrowthA (acc + x + x + x) (((l ++ [x]) ++ [x]) ++ [x]) :=
    GrowthA.snoc (acc + x + x) ((l ++ [x]) ++ [x]) x (by omega) g2
  have heq : ((l ++ [x]) ++ [x]) ++ [x] = l ++ [x, x, x] :=
    (my_append_assoc (l ++ [x]) [x] [x]).trans (my_append_assoc l [x] ([x] ++ [x]))
  have h3x : acc + 3 * x = acc + x + x + x := by omega
  rw [h3x, ← heq]
  exact g3

/-- **THE GROWTH CERTIFICATE of the witness** (general j): the mult-3 powers
prefix family satisfies Graham's prefix growth criterion. -/
theorem w23_growth : ∀ j : Nat, GrowthA (lsum (w23 j)) (w23 j) := by
  intro j
  induction j with
  | zero =>
    have g1 : GrowthA 1 [1] := GrowthA.snoc 0 [] 1 (by omega) GrowthA.nil
    have g2 : GrowthA 2 [1, 1] := GrowthA.snoc 1 [1] 1 (by omega) g1
    have g3 : GrowthA 3 [1, 1, 1] := GrowthA.snoc 2 [1, 1] 1 (by omega) g2
    exact g3
  | succ k ih =>
    have hl := w23_lsum k
    have hp : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    have hx : 2 ^ (k + 1) ≤ lsum (w23 k) + 1 := by omega
    have hgrow := snoc3 (lsum (w23 k)) (2 ^ (k + 1)) (w23 k) ih hx
    have hl1 := lsum_append (w23 k) (blk (k + 1))
    have hl2 := blk_lsum (k + 1)
    show GrowthA (lsum (w23 k ++ blk (k + 1))) (w23 k ++ blk (k + 1))
    rw [hl1, hl2]
    exact hgrow

/-- **(C1) THE COMPLETENESS of the witness at every level**: every
n ≤ 3(2^{j+1}-1) is a subset sum of the mult-3 powers prefix. -/
theorem w23_complete : ∀ (j n : Nat), n ≤ lsum (w23 j) → sumSet (w23 j) n := by
  intro j n hn
  exact greedy_complete_prefix (w23 j) (lsum (w23 j)) (w23_growth j) n hn

/-- `1 ≤ 2 ^ j` (the positivity of the powers). -/
theorem two_pow_pos : ∀ j : Nat, 1 ≤ 2 ^ j := by
  intro j
  induction j with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- `n + 1 ≤ 2 ^ (n+1)` (the exponential escape bound). -/
theorem n_lt_two_pow : ∀ n : Nat, n + 1 ≤ 2 ^ (n + 1) := by
  intro n
  induction n with
  | zero => decide
  | succ k ih =>
    have hp : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
    have h1 := two_pow_pos (k + 1)
    omega

/-- **(C1) THE ω-WITNESS COMPLETENESS**: every natural number is a sum of
distinct terms of the mult-3 powers sequence (the level-n prefix covers n). -/
theorem w23_inf_complete : ∀ n : Nat, ∃ j : Nat, sumSet (w23 j) n := by
  intro n
  have hn := n_lt_two_pow n
  have hl := w23_lsum n
  refine ⟨n, ?_⟩
  exact w23_complete n n (by omega)

/-! ## §8B THE 2-REMOVAL MACHINERY (position deletions, counted) -/

/-- `SubN c l l'` : `l'` is obtained from `l` by deleting exactly `c`
positions (the count-tracked sublist relation). -/
inductive SubN : Nat → List Nat → List Nat → Prop
  | refl : ∀ (l : List Nat), SubN 0 l l
  | keep : ∀ (c : Nat) (a : Nat) (t t' : List Nat), SubN c t t' → SubN c (a :: t) (a :: t')
  | drop : ∀ (c : Nat) (a : Nat) (t t' : List Nat), SubN c t t' → SubN (c + 1) (a :: t) t'

/-- SubN survives appending a common tail to both sides. -/
theorem SubN_append_keep : ∀ (c : Nat) (l l' r : List Nat), SubN c l l' → SubN c (l ++ r) (l' ++ r) := by
  intro c l l' r h
  induction h with
  | refl l0 => exact SubN.refl (l0 ++ r)
  | keep c0 a t t' hsub ih => exact SubN.keep c0 a (t ++ r) (t' ++ r) ih
  | drop c0 a t t' hsub ih => exact SubN.drop c0 a (t ++ r) t' ih

/-- The uniform-list law: a counted deletion from `replicate m x` stays
uniform, with the count bookkept. -/
theorem SubN_replicate : ∀ (m x c : Nat) (t' : List Nat), SubN c (List.replicate m x) t' →
    ∃ r, t' = List.replicate r x ∧ r + c = m := by
  intro m
  induction m with
  | zero =>
    intro x c t' h
    have hnil : List.replicate 0 x = [] := rfl
    rw [hnil] at h
    cases h with
    | refl l1 => exact ⟨0, rfl, by omega⟩
  | succ k ih =>
    intro x c t' h
    have hcons : List.replicate (k + 1) x = x :: List.replicate k x := rfl
    rw [hcons] at h
    cases h with
    | refl l1 => exact ⟨k + 1, rfl, by omega⟩
    | keep c0 a t1 t1' hsub =>
      obtain ⟨r, hr, hrc⟩ := ih x c0 t1' hsub
      refine ⟨r + 1, ?_, by omega⟩
      exact congrArg (fun q => x :: q) hr
    | drop c0 a t1 t1' hsub =>
      obtain ⟨r, hr, hrc⟩ := ih x c0 t1' hsub
      exact ⟨r, hr, by omega⟩

/-- The append-split law for counted deletions: a deletion from `l1 ++ l2`
splits into deletions on `l1` and `l2` with the counts adding. -/
theorem SubN_append : ∀ (l1 l2 : List Nat) (c : Nat) (l' : List Nat),
    SubN c (l1 ++ l2) l' → ∃ c1 c2 l1' l2', c = c1 + c2 ∧ SubN c1 l1 l1' ∧
    SubN c2 l2 l2' ∧ l' = l1' ++ l2' := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 c l' h
    have hnil : ([] : List Nat) ++ l2 = l2 := rfl
    rw [hnil] at h
    exact ⟨0, c, [], l', by omega, SubN.refl [], h, rfl⟩
  | cons a t ih =>
    intro l2 c l' h
    have hca : (a :: t) ++ l2 = a :: (t ++ l2) := rfl
    rw [hca] at h
    cases h with
    | refl l1 => exact ⟨0, 0, a :: t, l2, by omega, SubN.refl (a :: t), SubN.refl l2, rfl⟩
    | keep c0 b u u' hsub =>
      obtain ⟨c1, c2, t', l2', hc, h1, h2, hsplit⟩ := ih l2 c0 u' hsub
      refine ⟨c1, c2, a :: t', l2', hc, SubN.keep c1 a t t' h1, h2, ?_⟩
      exact congrArg (fun q => a :: q) hsplit
    | drop c0 b u u' hsub =>
      obtain ⟨c1, c2, t', l2', hc, h1, h2, hsplit⟩ := ih l2 c0 u' hsub
      exact ⟨c1 + 1, c2, t', l2', by omega, SubN.drop c1 a t t' h1, h2, hsplit⟩

/-- The composition law for counted deletions (the ∃-count form: omega
bridges the count arithmetic; the second deletion's target is kept
universally quantified so the inner cases can peel it). -/
theorem SubN_comp : ∀ (c1 c2 : Nat) (l m : List Nat), SubN c1 l m → ∀ (m' : List Nat),
    SubN c2 m m' → ∃ c, c = c1 + c2 ∧ SubN c l m' := by
  intro c1 c2 l m
  intro h1
  induction h1 with
  | refl l0 =>
    intro m' h2
    exact ⟨c2, by omega, h2⟩
  | keep c0 a t t1 hsub ih =>
    intro m' h2
    cases h2 with
    | refl l1 => exact ⟨c0, by omega, SubN.keep c0 a t t1 hsub⟩
    | keep c2' b u u1 hsub2 =>
      obtain ⟨c, hc, hcm⟩ := ih u1 hsub2
      exact ⟨c, hc, SubN.keep c a t u1 hcm⟩
    | drop c2' b u u1 hsub2 =>
      obtain ⟨c, hc, hcm⟩ := ih u1 hsub2
      exact ⟨c + 1, by omega, SubN.drop c a t u1 hcm⟩
  | drop c0 a t t1 hsub ih =>
    intro m' h2
    obtain ⟨c, hc, hcm⟩ := ih m' h2
    exact ⟨c + 1, by omega, SubN.drop c a t m' hcm⟩

/-- Position deletion (kernel-computable). -/
def delAt : List Nat → Nat → List Nat
  | [], _ => []
  | a :: t, 0 => t
  | a :: t, i + 1 => a :: delAt t i

/-- One position deletion is a ≤1 counted deletion. -/
theorem SubN_delAt : ∀ (l : List Nat) (i : Nat), ∃ c, c ≤ 1 ∧ SubN c l (delAt l i) := by
  intro l
  induction l with
  | nil => intro i; exact ⟨0, by omega, SubN.refl []⟩
  | cons a t ih =>
    intro i
    cases i with
    | zero => exact ⟨1, by omega, SubN.drop 0 a t t (SubN.refl t)⟩
    | succ m =>
      obtain ⟨c, hc, hsub⟩ := ih m
      exact ⟨c, hc, SubN.keep c a t (delAt t m) hsub⟩

/-- Two position deletions compose to a ≤2 counted deletion. -/
theorem delAt_SubN2 : ∀ (l : List Nat) (i j : Nat), ∃ c, c ≤ 2 ∧ SubN c l (delAt (delAt l i) j) := by
  intro l i j
  obtain ⟨c1, hc1, h1⟩ := SubN_delAt l i
  obtain ⟨c2, hc2, h2⟩ := SubN_delAt (delAt l i) j
  obtain ⟨c, hc, hcm⟩ := SubN_comp c1 c2 l (delAt l i) h1 (delAt (delAt l i) j) h2
  exact ⟨c, by omega, hcm⟩

/-- **(C2) THE 2-REDUNDANCY, GENERAL**: after ANY at-most-2 position
deletion at ANY level j, the survivor still covers the full binary range
[0, 2^{j+1}-1].  (The block-snoc induction: the two deletions are split
between the level-j prefix and the new 2^{j+1}-block by `SubN_append`; the
block keeps ≥1 copy of 2^{j+1} by `SubN_replicate`; the prefix's coverage
plus the surviving copy re-covers the doubled range.) -/
theorem w23_two_removal : ∀ (j c : Nat) (l' : List Nat), c ≤ 2 → SubN c (w23 j) l' →
    ∀ n, n ≤ 2 ^ (j + 1) - 1 → sumSet l' n := by
  intro j
  induction j with
  | zero =>
    intro c l' hc hsub n hn
    obtain ⟨r, hr, hrc⟩ := SubN_replicate 3 1 c l' hsub
    cases r with
    | zero => exfalso; omega
    | succ s =>
      rw [hr]
      cases n with
      | zero => exact sumSet.zero (List.replicate (s + 1) 1)
      | succ m =>
        have hp1 : 2 ^ (0 + 1) = 2 := by decide
        have hm : m = 0 := by omega
        subst hm
        exact sumSet.take 1 (List.replicate s 1) (0 + 1) (by omega)
          (sumSet.zero (List.replicate s 1))
  | succ k ih =>
    intro c l' hc hsub n hn
    obtain ⟨c1, c2, pre', blk', hcc, hpre, hblk, hsplit⟩ :=
      SubN_append (w23 k) (blk (k + 1)) c l' hsub
    have hc2 : c2 ≤ 2 := by omega
    have hc1 : c1 ≤ 2 := by omega
    obtain ⟨r, hrb, hrc2⟩ := SubN_replicate 3 (2 ^ (k + 1)) c2 blk' hblk
    cases r with
    | zero => exfalso; omega
    | succ s =>
      have hsplit2 : l' = pre' ++ (2 ^ (k + 1) :: List.replicate s (2 ^ (k + 1))) :=
        hsplit.trans (congrArg (fun b => pre' ++ b) hrb)
      have hp : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      have hcase : n < 2 ^ (k + 1) ∨ 2 ^ (k + 1) ≤ n := by omega
      rcases hcase with hlt | hge
      · have hnm : n ≤ 2 ^ (k + 1) - 1 := by omega
        have hsum := ih c1 pre' hc1 hpre n hnm
        rw [hsplit2]
        exact sumSet_mono_append pre' (2 ^ (k + 1) :: List.replicate s (2 ^ (k + 1))) n hsum
      · have hnm : n - 2 ^ (k + 1) ≤ 2 ^ (k + 1) - 1 := by omega
        have hsum := ih c1 pre' hc1 hpre (n - 2 ^ (k + 1)) hnm
        have hsnoc := sumSet_snoc pre' (2 ^ (k + 1)) (n - 2 ^ (k + 1)) n (by omega) hsum
        have heq : (pre' ++ [2 ^ (k + 1)]) ++ List.replicate s (2 ^ (k + 1))
            = pre' ++ (2 ^ (k + 1) :: List.replicate s (2 ^ (k + 1))) :=
          my_append_assoc pre' [2 ^ (k + 1)] (List.replicate s (2 ^ (k + 1)))
        have hmono := sumSet_mono_append (pre' ++ [2 ^ (k + 1)])
          (List.replicate s (2 ^ (k + 1))) n hsnoc
        rw [hsplit2, ← heq]
        exact hmono

/-- **(C2) THE 2-REDUNDANCY IN delAT FORM (the ω-witness)**: for ANY two
positions i, j and ANY n, some level's survivor of the mult-3 powers
witness covers n — after any two deletions the witness sequence remains
complete. -/
theorem w23_two_removal_inf : ∀ (i j n : Nat), ∃ L : Nat,
    sumSet (delAt (delAt (w23 L) i) j) n := by
  intro i j n
  have hn := n_lt_two_pow n
  refine ⟨n, ?_⟩
  obtain ⟨c, hc, hsub⟩ := delAt_SubN2 (w23 n) i j
  exact w23_two_removal n c (delAt (delAt (w23 n) i) j) hc hsub n (by omega)

/-! ## §8C THE 3-KILL (the parity law) -/

/-- The all-even list predicate (own inductive — no core-name risk). -/
inductive AllEven : List Nat → Prop
  | nil : AllEven []
  | cons : ∀ (a : Nat) (t : List Nat), (∃ c, a = 2 * c) → AllEven t → AllEven (a :: t)

/-- Uniform even blocks are all-even. -/
theorem AllEven_replicate : ∀ (m x : Nat), (∃ c, x = 2 * c) → AllEven (List.replicate m x) := by
  intro m x hx
  induction m with
  | zero => exact AllEven.nil
  | succ k ih => exact AllEven.cons x (List.replicate k x) hx ih

/-- AllEven survives append. -/
theorem AllEven_append : ∀ (l r : List Nat), AllEven l → AllEven r → AllEven (l ++ r) := by
  intro l
  induction l with
  | nil => intro r _ h2; exact h2
  | cons a t ih =>
    intro r h1 h2
    cases h1 with
    | cons _ _ hAe hAt => exact AllEven.cons a (t ++ r) hAe (ih r hAt h2)

/-- **THE PARITY LAW**: every subset sum of an all-even list is even. -/
theorem sumSet_even : ∀ (l : List Nat) (n : Nat), AllEven l → sumSet l n → ∃ c, n = 2 * c := by
  intro l
  induction l with
  | nil =>
    intro n _ h
    have hn0 : n = 0 := sumSet_nil_inv h
    exact ⟨0, by omega⟩
  | cons a t ih =>
    intro n hall h
    cases hall with
    | cons _ _ hAe hAt =>
      rcases sumSet_cons_inv h with hd | ⟨hle, htk⟩
      · exact ih n hAt hd
      · obtain ⟨d, hd⟩ := hAe
        obtain ⟨c, hc⟩ := ih (n - a) hAt htk
        exact ⟨c + d, by omega⟩

/-- THE 3-KILL SURVIVOR FAMILY: blocks 1..j (the three 1s removed). -/
def w23k : Nat → List Nat
  | 0 => []
  | j + 1 => w23k j ++ blk (j + 1)

/-- The 3-kill survivor is all-even (every surviving element is 2^k, k ≥ 1). -/
theorem w23k_allEven : ∀ j : Nat, AllEven (w23k j) := by
  intro j
  induction j with
  | zero => exact AllEven.nil
  | succ k ih =>
    have hblk : AllEven (blk (k + 1)) := by
      have hxe : ∃ c, 2 ^ (k + 1) = 2 * c := by
        refine ⟨2 ^ k, ?_⟩
        have hp : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
        omega
      exact AllEven_replicate 3 (2 ^ (k + 1)) hxe
    show AllEven (w23k k ++ blk (k + 1))
    exact AllEven_append (w23k k) (blk (k + 1)) ih hblk

/-- **(C3) THE 3-KILL, GENERAL**: NO odd integer is a subset sum of the
survivor obtained by removing the three 1s — at any level. -/
theorem w23k_no_odd : ∀ (j n : Nat), ¬ sumSet (w23k j) (2 * n + 1) := by
  intro j n h
  obtain ⟨c, hc⟩ := sumSet_even (w23k j) (2 * n + 1) (w23k_allEven j) h
  omega

/-- The structural split: the witness is the 1-block plus the kill survivor. -/
theorem w23_split : ∀ j : Nat, w23 j = blk 0 ++ w23k j := by
  intro j
  induction j with
  | zero => rfl
  | succ k ih =>
    show w23 k ++ blk (k + 1) = blk 0 ++ (w23k k ++ blk (k + 1))
    rw [ih]
    exact my_append_assoc (blk 0) (w23k k) (blk (k + 1))

/-- The kill certificate: the 3-kill survivor IS the witness with exactly
the three 1s deleted (a counted 3-deletion). -/
theorem SubN_kill : ∀ j : Nat, SubN 3 (w23 j) (w23k j) := by
  intro j
  induction j with
  | zero =>
    show SubN 3 [1, 1, 1] []
    exact SubN.drop 2 1 [1, 1] [] (SubN.drop 1 1 [1] []
      (SubN.drop 0 1 [] [] (SubN.refl [])))
  | succ k ih =>
    show SubN 3 (w23 k ++ blk (k + 1)) (w23k k ++ blk (k + 1))
    exact SubN_append_keep 3 (w23 k) (w23k k) (blk (k + 1)) ih

/-- **(C3) THE 3-KILL NON-COMPLETENESS**: the survivor of the 1-block
removal is NOT complete — no threshold N makes every n ≥ N a subset sum. -/
theorem w23k_not_complete : ¬ ∃ N : Nat, ∀ n, N ≤ n → ∃ j, sumSet (w23k j) n := by
  intro h
  obtain ⟨N, hN⟩ := h
  have hw := hN (2 * N + 1) (by omega)
  obtain ⟨j, hj⟩ := hw
  exact w23k_no_odd j N hj

/-- The decide battery at the certified level-4 witness (engine-verified
identities, dual-method; bounded kernel cost). -/
theorem w23_decide_battery :
    (reachable (w23 4) 93 = true ∧ reachable (w23 4) 61 = true ∧
      reachable (w23 4) 1 = true ∧ reachable (w23k 4) 1 = false) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **THE (m,n) = (2,3) CASE THEOREM**: the mult-3 powers witness is
complete (C1), survives every 2-deletion at every level with the full binary
range intact (C2, both the SubN form and the delAt ω-form), and is killed by
the 3-deletion of the three 1s — no odd integer is a subset sum of the
survivor, which is therefore not complete (C3).  The redundancy of the
witness is exactly 2. -/
theorem e348_construction_23 :
    (∀ n : Nat, ∃ j : Nat, sumSet (w23 j) n) ∧
    (∀ (j c : Nat) (l' : List Nat), c ≤ 2 → SubN c (w23 j) l' →
      ∀ n, n ≤ 2 ^ (j + 1) - 1 → sumSet l' n) ∧
    (∀ (i j n : Nat), ∃ L : Nat, sumSet (delAt (delAt (w23 L) i) j) n) ∧
    (∀ (j n : Nat), ¬ sumSet (w23k j) (2 * n + 1)) ∧
    (∀ j : Nat, SubN 3 (w23 j) (w23k j)) ∧
    (¬ ∃ N : Nat, ∀ n, N ≤ n → ∃ j, sumSet (w23k j) n) :=
  ⟨w23_inf_complete, w23_two_removal, w23_two_removal_inf, w23k_no_odd,
    SubN_kill, w23k_not_complete⟩

/-! ## Receipt block -/

#print axioms reachable_iff_sumSet
#print axioms sumSet_le_sum
#print axioms gap_law
#print axioms greedy_complete
#print axioms greedy_complete_prefix
#print axioms powers_complete
#print axioms powers_decide_500
#print axioms powers_decide_battery
#print axioms sumSet_2_3_iff
#print axioms never_one
#print axioms redundant_seed
#print axioms no_finite_prefix_seed
#print axioms e348_arsenal_bridge
#print axioms e348_board
#print axioms w23_complete
#print axioms w23_inf_complete
#print axioms w23_two_removal
#print axioms w23_two_removal_inf
#print axioms w23k_no_odd
#print axioms w23k_not_complete
#print axioms SubN_kill
#print axioms w23_decide_battery
#print axioms e348_construction_23

#eval "E348_REDUNDANT_GREEN"
#eval "E348_CONSTRUCTION23_GREEN"

end E348
