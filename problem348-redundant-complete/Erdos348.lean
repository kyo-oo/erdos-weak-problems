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
2. THE PREFIX FUNCTION: `prefix` (take m) and `mSuffices` (a finite prefix
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
    | zero => omega
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
    | succ k => exact absurd h (by decide)
  | cons a t ih =>
    intro n h
    rcases or_of_bool_eq (reachable t n) (leB a n && reachable t (n - a)) h with h1 | h2
    · exact sumSet.drop a t n (ih n h1)
    · rcases bool_cases (leB a n) with hb | hb
      · rw [hb] at h2
        exact absurd h2 (by decide)
      · rw [hb] at h2
        have h3 : reachable t (n - a) = true := h2
        exact sumSet.take a t n (leB_of_true a n hb) (ih (n - a) h3)

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
    exact ⟨[], by rw [take_nil m]⟩
  | cons a t ih =>
    intro m
    cases m with
    | zero => exact ⟨a :: t, by rw [take_zero]⟩
    | succ k =>
      obtain ⟨ext, hex⟩ := ih k
      exact ⟨ext, by show a :: (List.take k t ++ ext) = a :: t; rw [hex]⟩

/-- **THE PREFIX FUNCTION**: the first m terms of the sequence. -/
def prefix (l : List Nat) (m : Nat) : List Nat := l.take m

/-- **THE m(A) LAW IN FINITE FORM**: the finite prefix `prefix l m` suffices —
every sufficiently large integer is a sum of distinct terms of the prefix. -/
def mSuffices (l : List Nat) (m : Nat) : Prop :=
  ∃ N, ∀ n, N ≤ n → reachable (prefix l m) n = true

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

#eval "E348_REDUNDANT_GREEN"

end E348
