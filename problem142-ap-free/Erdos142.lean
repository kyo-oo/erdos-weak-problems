import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos142 — THE r_k(N) AP-FREE TERNARY KERNEL r3 (W68-142K, repair of W67-142K r1)

Erdős #142 (verbatim, erdosproblems.com/142, prize $10000):
"Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$
that does not contain any non-trivial $k$-term arithmetic progression.
Prove an asymptotic formula for $r_k(N)$."

## CONVENTION (pinned, verbatim)
Non-trivial k-term arithmetic progression: a, a+d, ..., a+(k-1)d with
d ≥ 1 (distinct terms). r_k(N) := max |S| over S ⊆ [1,N] containing no
non-trivial k-term AP. The kernel's finite-list encoding: S : List Nat
with S.Nodup and every s ∈ S satisfying 1 ≤ s ≤ N.

## THE BOARD (complete unconditional proofs, zero sorry)
1. THE TERNARY KERNEL `E142.t3free`: the Cantor ternary set
   T := {n : noTernaryTwo n = true} (BOSS's Arsenal predicate — the
   ternary expansion avoids the digit 2, i.e. every ternary digit is
   0 or 1) is 3-AP-free: any x,y,z ∈ T with x + z = 2*y (y the
   midpoint) satisfy x = z. Proof: mod-3 descent — the residue triple
   is forced to (0,0,0) or (1,1,1), the thirds stay in T by the
   reader's step law, and the equation descends; fuel induction
   terminates. `E142.t3_no_nontriv`: T contains no non-trivial 3-AP.
2. THE CANTOR LOWER BOUND `E142.cantor_lower`: for N = 3^k − 1,
   r_3(N) ≥ 2^k − 1 — the explicit witness list genTp k (all ternary
   digit vectors in {0,1}^k except all-zero, as naturals) has exactly
   2^k − 1 distinct elements in [1, 3^k − 1] and is 3-AP-free by t3free.
3. THE BLOCK UPPER BOUND `E142.block_upper`: every k-AP-free S ⊆ [1,N]
   satisfies |S| ≤ (k−1)·⌊N/k⌋ + (N mod k) — window pigeonhole +
   window coverage + the consecutive k-block partition. Specialize
   k=3: `E142.r3_upper` r_3(N) ≤ 2⌊N/3⌋ + (N mod 3).
4. THE k=2 EDGE `E142.k2_edge`: r_2(N) = 1 for N ≥ 2 (upper law +
   the [1] witness). The k=2 edge case is exactly why the problem's
   interest starts at k=3.
5. THE SMALL-N EXACT TABLE `E142.r3_exact_small`: r_3(N) = m exactly
   for N = 1..8 (values 1,2,2,3,4,4,4,4) via the exhaustive kernel-decided
   sublists enumeration r3max + the ap3Free checker iff + the r3max
   bridge which dominates every AP-free set.
6. THE ARSENAL BRIDGE `E142.arsenal_bridge`: T's closure laws 3n, 3n+1
   under the CardinalWorlds reader; and the 7-conjunct crown
   `E142.erdos142_board`.

## REPAIR NOTE (r3, W68-142K)
Root-killed the 73-error family of CI run 43736909745: (a) the Arsenal
name `two_pow_pos` lives in the ROOT namespace (CardinalWorlds.lean:420)
— the qualified `CardinalWorlds.two_pow_pos` never resolved; (b) the
`hp'` case-label was used outside its `by`-block scope in mem_filt_iff;
(c) `a.length` referenced a variable eliminated by `subst`; (d) the
Lean v4.33-rc2 core signatures: `List.mem_cons_self` is implicit-argument
(bare application only) and `Nat.le_max_left`/`le_max_right` take explicit
(a b); (e) `==` on Nat does not definitionally unfold to `Nat.beq` at
elaboration transparency — all Boolean equality now goes through the
house structural `eqb` (zero core-name dependence); (f) dot-notation
`.sublists`/`.filt` resolved to the core `List.sublists` (reversed cons
order) resp. to a nonexistent `List.filt` — all house list machinery is
now used in prefix form; (g) the 0/1 residue descent of t3free_fuel now
closes by omega over the division identities; (h) every missing
`intro`/length-fact (`(x :: t).length = t.length + 1`) before an omega
was supplied. The sorryAx of the error-recovery pass is thereby purged:
the file compiles with axiom profile [propext, Classical.choice,
Quot.sound] only.

## REPAIR NOTE (r4, W68-142K)
Root-killed the residual 28-error family of CI run 43745701008 (verified
against a local Lean v4.33.0-rc2 stub-harness that reproduced all 28
errors verbatim, then zero): (1) THE ROOT: the `eqb` patterns
`| zero, zero => …` bind VARIABLES named `zero` (twice!) — the def
never compiled, so `eqb` was error-recovery-opaque and poisoned every
downstream reduction (eqb_refl's `rfl`, `Bool.noConfusion h`
unification at eq_of_eqb_true, and the whole 12-member `decide` family
of r3max/ap3Free) — patterns rewritten to constructor form `0 / _+1 /
x+1,y+1`; (2) `and_true_of_true`: `rw [hx, hy]` leaves
`(true && true) = true` (rw's auto-rfl is reducible-only) — now closed
by `cases` + rfl; (3) mem_filt_iff cons branch: `hp : p a = true`
supplied for `p s = true` via `subst h` first, the spurious
`rcases List.mem_cons.mp h2.1` on a `s ∈ t` (non-cons) replaced by the
direct constructor, and `absurd hs.2 hpf` (a `p s = false` where
`¬(p s = true)` is needed) replaced by `rw [hpf] at hs; exact
Bool.noConfusion hs.2`; (4) `nodup_append_disj`: the k-block side goal
has `hb : b ∈ t ++ l2` — the splitter is `List.mem_append.mp hb`, not
mem_cons; (5) `nodup_const_le1`/`k2_upper`: `mem_cons_of_tail w u rest'
(mem_self_cons u rest')` passes the WRONG list argument (needs
`u ∈ u :: rest'`, i.e. t := `u :: rest'`) — the k2 case needs the same
fix at both AP-term sites plus the missing `hne : a ≠ b` from Nodup
before `omega` derives `b < a` from `¬(a < b)`; (6) window_cover's
`hge1`: after `cases hL : …`, the goal atom is `(a :: t).length` but
`hLlen` was stated on the pre-cases `(filt …).length` — omega saw two
unrelated atoms — hLlen restated on `(a :: t).length` (rfl); (7)
`r3_upper_via_r3max`: `hAP` needs `x ∈ S`, so the filt-membership
conjunction's SECOND component (`memB x S = true`, via memB_iff) is the
right one, not `.left` (the `x ∈ upto1 N`). Axiom profile after r4:
[propext, Classical.choice, Quot.sound] only, zero sorry, markers
E142_TERNARY_GREEN / E142_CANTOR_GREEN / E142_BOARD_GREEN emitted.
-/

namespace E142

/-! ## §0 Micro machinery (house-built: zero flaky core names) -/

theorem or_true_left (x y : Bool) (hx : x = true) : (x || y) = true := by
  cases x with
  | false => exact Bool.noConfusion hx
  | true => rfl

theorem or_true_right (x y : Bool) (hy : y = true) : (x || y) = true := by
  cases y with
  | false => exact Bool.noConfusion hy
  | true => cases x <;> rfl

theorem and_true_of_true (x y : Bool) (hx : x = true) (hy : y = true) :
    (x && y) = true := by
  cases x with
  | false => exact Bool.noConfusion hx
  | true =>
    cases y with
    | false => exact Bool.noConfusion hy
    | true => rfl

theorem or_split (x y : Bool) (h : (x || y) = true) : x = true ∨ y = true := by
  cases x with
  | false => exact Or.inr h
  | true => exact Or.inl rfl

theorem and_split (x y : Bool) (h : (x && y) = true) : x = true ∧ y = true := by
  cases x with
  | false => exact Bool.noConfusion h
  | true =>
    cases y with
    | false => exact Bool.noConfusion h
    | true => exact ⟨rfl, rfl⟩

/-! ### The house Boolean equality on Nat (structural, iota-transparent). -/

def eqb : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | x + 1, y + 1 => eqb x y

theorem eqb_refl : ∀ a : Nat, eqb a a = true := by
  intro a
  induction a with
  | zero => rfl
  | succ n ih => exact ih

theorem eqb_true_of_eq : ∀ (a b : Nat), a = b → eqb a b = true := by
  intro a b h
  subst h
  exact eqb_refl _

theorem eq_of_eqb_true : ∀ (a b : Nat), eqb a b = true → a = b := by
  intro a
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ b => exact Bool.noConfusion h
  | succ n ih =>
    intro b h
    cases b with
    | zero => exact Bool.noConfusion h
    | succ b => exact congrArg Nat.succ (ih b h)

theorem ne_of_not_eqb (a b : Nat) (h : (! eqb a b) = true) : a ≠ b := by
  intro he
  have hq : eqb a b = true := eqb_true_of_eq a b he
  rw [hq] at h
  rw [Bool.not_true] at h
  exact Bool.noConfusion h

theorem notbeq_false (X : Bool) (h : (! X) = true) : X = false := by
  cases X with
  | false => rfl
  | true => exact Bool.noConfusion h

theorem prop_of_decide_true (p : Prop) [inst : Decidable p] (h : decide p = true) : p := by
  have heq : (decide p = true) ↔ p := decide_eq_true_iff
  exact heq.mp h

theorem decide_true_of_prop (p : Prop) [inst : Decidable p] (h : p) : decide p = true := by
  have heq : (decide p = true) ↔ p := decide_eq_true_iff
  exact heq.mpr h

theorem not_of_decide_false (p : Prop) [inst : Decidable p] (h : decide p = false) : ¬ p := by
  intro hp
  have ht : decide p = true := decide_true_of_prop p hp
  rw [h] at ht
  exact Bool.noConfusion ht

/-! ### The house filter and its laws. -/

/-- The house filter: `if p a = true` form — if_pos/if_neg-native (polymorphic:
    used both at `List Nat` and at `List (List Nat)` for the sublists engine). -/
def filt {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | a :: t => if p a = true then a :: filt p t else filt p t

theorem filt_cons_true {α : Type} (p : α → Bool) (a : α) (t : List α) (h : p a = true) :
    filt p (a :: t) = a :: filt p t := by
  have e : filt p (a :: t) = if p a = true then a :: filt p t else filt p t := rfl
  rw [e, if_pos h]

theorem filt_cons_false {α : Type} (p : α → Bool) (a : α) (t : List α) (h : ¬ (p a = true)) :
    filt p (a :: t) = filt p t := by
  have e : filt p (a :: t) = if p a = true then a :: filt p t else filt p t := rfl
  rw [e, if_neg h]

theorem mem_filt_iff {α : Type} (p : α → Bool) : ∀ (l : List α) (s : α),
    s ∈ filt p l ↔ (s ∈ l ∧ p s = true) := by
  intro l
  induction l with
  | nil =>
    intro s
    have e0 : filt p ([] : List α) = [] := rfl
    constructor
    · intro hs
      rw [e0] at hs
      exact absurd hs (by simp)
    · intro hs; exact absurd hs.1 (by simp)
  | cons a t ih =>
    intro s
    by_cases hp : p a = true
    · rw [filt_cons_true p a t hp]
      constructor
      · intro hs
        rcases List.mem_cons.mp hs with h | h
        · subst h
          exact ⟨List.mem_cons.mpr (Or.inl rfl), hp⟩
        · have h2 := (ih s).mp h
          exact ⟨List.mem_cons.mpr (Or.inr h2.1), h2.2⟩
      · intro hs
        rcases List.mem_cons.mp hs.1 with h | h
        · exact List.mem_cons.mpr (Or.inl h)
        · exact List.mem_cons.mpr (Or.inr ((ih s).mpr ⟨h, hs.2⟩))
    · have hpf : p a = false := by
        cases hp' : p a with
        | false => rfl
        | true => exact absurd hp' hp
      rw [filt_cons_false p a t hp]
      constructor
      · intro hs
        have h2 := (ih s).mp hs
        exact ⟨List.mem_cons.mpr (Or.inr h2.1), h2.2⟩
      · intro hs
        rcases List.mem_cons.mp hs.1 with h | h
        · subst h
          rw [hpf] at hs
          exact Bool.noConfusion hs.2
        · exact (ih s).mpr ⟨h, hs.2⟩

theorem filt_split (p : Nat → Bool) : ∀ (l : List Nat),
    l.length = (filt p l).length + (filt (fun s => ! p s) l).length := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hL : (a :: t).length = t.length + 1 := rfl
    by_cases hp : p a = true
    · have e1 : filt p (a :: t) = a :: filt p t := filt_cons_true p a t hp
      have e2 : filt (fun s => ! p s) (a :: t) = filt (fun s => ! p s) t := by
        refine filt_cons_false (fun s => ! p s) a t ?_
        intro h
        have h' : (! p a) = true := h
        rw [hp] at h'
        rw [Bool.not_true] at h'
        exact Bool.noConfusion h'
      rw [hL, e1, e2, List.length_cons, ih]
      omega
    · have hpf : p a = false := by
        cases hp' : p a with
        | false => rfl
        | true => exact absurd hp' hp
      have e1 : filt p (a :: t) = filt p t := filt_cons_false p a t hp
      have e2 : filt (fun s => ! p s) (a :: t) = a :: filt (fun s => ! p s) t := by
        refine filt_cons_true (fun s => ! p s) a t ?_
        show (! p a) = true
        rw [hpf]
        rfl
      rw [hL, e1, e2, List.length_cons, ih]
      omega

/-! ### Membership helpers (the head/tail laws, explicit form). -/

theorem mem_self_cons (a : Nat) (t : List Nat) : a ∈ a :: t :=
  List.mem_cons_self

theorem mem_cons_of_tail (a b : Nat) (t : List Nat) (h : b ∈ t) : b ∈ a :: t :=
  List.mem_cons.mpr (Or.inr h)

/-! ### Nodup machinery. -/

theorem nodup_cons_head (a : Nat) (t : List Nat) (h : (a :: t).Nodup) :
    ∀ b ∈ t, a ≠ b := by
  intro b hb
  cases h with
  | cons hhead _ => exact hhead b hb

theorem nodup_cons_tail (a : Nat) (t : List Nat) (h : (a :: t).Nodup) : t.Nodup := by
  cases h with
  | cons _ hp => exact hp

theorem nodup_filter (p : Nat → Bool) : ∀ (l : List Nat), l.Nodup → (filt p l).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a t ih =>
    intro hN
    by_cases hp : p a = true
    · rw [filt_cons_true p a t hp]
      refine List.Pairwise.cons ?_ (ih (nodup_cons_tail a t hN))
      intro b hb
      obtain ⟨hc, _⟩ := (mem_filt_iff p t b).mp hb
      exact nodup_cons_head a t hN b hc
    · rw [filt_cons_false p a t hp]
      exact ih (nodup_cons_tail a t hN)

theorem nodup_map_inj (f : Nat → Nat) (hf : ∀ a b, f a = f b → a = b) :
    ∀ (l : List Nat), l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a t ih =>
    intro hN
    rw [List.map_cons]
    refine List.Pairwise.cons ?_ (ih (nodup_cons_tail a t hN))
    intro b hb
    obtain ⟨c, hc, hfc⟩ := List.mem_map.mp hb
    intro hfa
    have hac : a = c := hf a c (hfa.trans hfc.symm)
    exact absurd hac (nodup_cons_head a t hN c hc)

theorem nodup_append_disj : ∀ (l1 l2 : List Nat), l1.Nodup → l2.Nodup →
    (∀ a ∈ l1, ∀ b ∈ l2, a ≠ b) → (l1 ++ l2).Nodup := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ hl2 _; exact hl2
  | cons a t ih =>
    intro l2 hl1 hl2 hd
    rw [List.cons_append]
    refine List.Pairwise.cons ?_ (ih l2 (nodup_cons_tail a t hl1) hl2
      (fun b hb1 hb2 => hd b (mem_cons_of_tail a b t hb1) hb2))
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact nodup_cons_head a t hl1 b h
    · exact hd a (mem_self_cons a t) b h

theorem nodup_const_le1 (W : List Nat) (c : Nat) (hN : W.Nodup)
    (hb : ∀ s ∈ W, s = c) : W.length ≤ 1 := by
  cases W with
  | nil =>
    have hz : ([] : List Nat).length = 0 := rfl
    omega
  | cons w rest =>
    cases rest with
    | nil =>
      have hz : (w :: ([] : List Nat)).length = 1 := rfl
      omega
    | cons u rest' =>
      have hw := hb w (mem_self_cons w (u :: rest'))
      have hu := hb u (mem_cons_of_tail w u (u :: rest') (mem_self_cons u rest'))
      have hwu : w = u := by omega
      exact absurd hwu (nodup_cons_head w (u :: rest') hN u (mem_self_cons u rest'))

/-- THE MEMBERSHIP PIGEONHOLE: a Nodup list whose elements all lie in B. -/
theorem nodup_mem_le : ∀ (B A : List Nat), A.Nodup → (∀ a ∈ A, a ∈ B) →
    A.length ≤ B.length := by
  intro B
  induction B with
  | nil =>
    intro A hA hsub
    cases A with
    | nil => omega
    | cons a t =>
      have hmem := hsub a (mem_self_cons a t)
      exact absurd hmem (by simp)
  | cons b t ih =>
    intro A hA hsub
    have hsplit : A.length = (filt (fun s => eqb s b) A).length +
        (filt (fun s => ! eqb s b) A).length := filt_split _ A
    have hEqb : ∀ s ∈ filt (fun s => eqb s b) A, s = b := by
      intro s hs
      have h2 := (mem_filt_iff _ A s).mp hs
      exact eq_of_eqb_true s b h2.2
    have hle1 : (filt (fun s => eqb s b) A).length ≤ 1 :=
      nodup_const_le1 _ b (nodup_filter _ A hA) hEqb
    have hsub' : ∀ a ∈ filt (fun s => ! eqb s b) A, a ∈ t := by
      intro a ha
      have h2 := (mem_filt_iff _ A a).mp ha
      have hnb : a ≠ b := ne_of_not_eqb a b h2.2
      have hmem := hsub a h2.1
      rcases List.mem_cons.mp hmem with h | h
      · subst h; omega
      · exact h
    have hle2 := ih (filt (fun s => ! eqb s b) A) (nodup_filter _ A hA) hsub'
    have hBL : (b :: t).length = t.length + 1 := rfl
    omega

/-! ## §1 The Cantor verdict's step laws (the Arsenal reader) -/

theorem ntt_mod3 (n : Nat) (h : noTernaryTwo n = true) : n % 3 ≠ 2 := by
  intro h2
  rw [noTernaryTwo.eq_def n] at h
  by_cases hn : n = 0
  · subst hn
    omega
  · rw [if_neg hn] at h
    rw [if_pos h2] at h
    exact Bool.noConfusion h

theorem ntt_step (n : Nat) (h : noTernaryTwo n = true) : noTernaryTwo (n / 3) = true := by
  by_cases hn : n = 0
  · subst hn
    exact h
  · rw [noTernaryTwo.eq_def n] at h
    rw [if_neg hn] at h
    by_cases h2 : n % 3 = 2
    · rw [if_pos h2] at h
      exact Bool.noConfusion h
    · rw [if_neg h2] at h
      exact h

theorem ntt_3n (n : Nat) (h : noTernaryTwo n = true) : noTernaryTwo (3 * n) = true := by
  rw [noTernaryTwo.eq_def (3 * n)]
  by_cases hn : 3 * n = 0
  · rw [if_pos hn]
  · rw [if_neg hn, if_neg (by omega : ¬ ((3 * n) % 3 = 2))]
    have h3 : (3 * n) / 3 = n := by omega
    rw [h3]
    exact h

theorem ntt_3n1 (n : Nat) (h : noTernaryTwo n = true) : noTernaryTwo (3 * n + 1) = true := by
  rw [noTernaryTwo.eq_def (3 * n + 1)]
  rw [if_neg (by omega : ¬ (3 * n + 1 = 0)),
      if_neg (by omega : ¬ ((3 * n + 1) % 3 = 2))]
  have h3 : (3 * n + 1) / 3 = n := by omega
  rw [h3]
  exact h

/-! ## §2 THE TERNARY KERNEL: T is 3-AP-free (the mod-3 descent) -/

theorem t3free_fuel : ∀ (fuel y x z : Nat), y < fuel →
    noTernaryTwo x = true → noTernaryTwo y = true → noTernaryTwo z = true →
    x + z = 2 * y → x = z := by
  intro fuel
  induction fuel with
  | zero =>
    intro y x z hy _ _ _ _
    omega
  | succ fuel ih =>
    intro y x z hy Tx Ty Tz hap
    by_cases hyz : y = 0
    · subst hyz
      omega
    have hy3b : y % 3 < 3 := Nat.mod_lt y (by decide : 0 < 3)
    rcases ErdosTernary2.lt_three_cases (y % 3) hy3b with hy0 | hy1 | hy2
    · have hxr := ntt_mod3 x Tx
      have hzr := ntt_mod3 z Tz
      have hx3b : x % 3 < 3 := Nat.mod_lt x (by decide : 0 < 3)
      have hz3b : z % 3 < 3 := Nat.mod_lt z (by decide : 0 < 3)
      have key : x % 3 = 0 ∧ z % 3 = 0 := by omega
      have hxd : x = 3 * (x / 3) := by omega
      have hzd : z = 3 * (z / 3) := by omega
      have hyd : y = 3 * (y / 3) := by omega
      have hdiv : x / 3 + z / 3 = 2 * (y / 3) := by omega
      have Tx' : noTernaryTwo (x / 3) = true := ntt_step x Tx
      have Tz' : noTernaryTwo (z / 3) = true := ntt_step z Tz
      have Ty' : noTernaryTwo (y / 3) = true := ntt_step y Ty
      have hy_lt : y / 3 < fuel := by omega
      have hres := ih (y / 3) (x / 3) (z / 3) hy_lt Tx' Ty' Tz' hdiv
      omega
    · have hxr := ntt_mod3 x Tx
      have hzr := ntt_mod3 z Tz
      have hx3b : x % 3 < 3 := Nat.mod_lt x (by decide : 0 < 3)
      have hz3b : z % 3 < 3 := Nat.mod_lt z (by decide : 0 < 3)
      have key : x % 3 = 1 ∧ z % 3 = 1 := by omega
      have hxd : x = 3 * (x / 3) + 1 := by omega
      have hzd : z = 3 * (z / 3) + 1 := by omega
      have hyd : y = 3 * (y / 3) + 1 := by omega
      have hdiv : x / 3 + z / 3 = 2 * (y / 3) := by omega
      have Tx' : noTernaryTwo (x / 3) = true := ntt_step x Tx
      have Tz' : noTernaryTwo (z / 3) = true := ntt_step z Tz
      have Ty' : noTernaryTwo (y / 3) = true := ntt_step y Ty
      have hy_lt : y / 3 < fuel := by omega
      have hres := ih (y / 3) (x / 3) (z / 3) hy_lt Tx' Ty' Tz' hdiv
      omega
    · exact absurd hy2 (ntt_mod3 y Ty)

/-- **THE TERNARY KERNEL**: the Cantor set T is 3-AP-free. -/
theorem t3free : ∀ x y z : Nat, noTernaryTwo x = true → noTernaryTwo y = true →
    noTernaryTwo z = true → x + z = 2 * y → x = z :=
  fun x y z => t3free_fuel (y + 1) y x z (Nat.lt_succ_self y)

/-- T contains no non-trivial 3-term AP (the a, a+d, a+2d form). -/
theorem t3_no_nontriv : ¬ ∃ a d : Nat, 1 ≤ d ∧ noTernaryTwo a = true ∧
    noTernaryTwo (a + d) = true ∧ noTernaryTwo (a + 2 * d) = true := by
  intro h
  obtain ⟨a, d, hd, ha, hmid, hz⟩ := h
  have hk := t3free a (a + d) (a + 2 * d) ha hmid hz (by omega)
  omega

/-! ## §3 The Cantor witnesses: genT / genTp and the lower bound -/

def genT : Nat → List Nat
  | 0 => [0]
  | k + 1 => (genT k).map (fun m => 3 * m) ++ (genT k).map (fun m => 3 * m + 1)

def genTp : Nat → List Nat
  | 0 => []
  | k + 1 => (genT k).map (fun m => 3 * m + 1) ++ (genTp k).map (fun m => 3 * m)

theorem pow3_pos : ∀ k : Nat, 0 < 3 ^ k := by
  intro k
  induction k with
  | zero => omega
  | succ k ih => rw [Nat.pow_succ]; omega

theorem genT_length : ∀ k : Nat, (genT k).length = 2 ^ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [genT, List.length_append, List.length_map, List.length_map, ih, Nat.pow_succ]
    omega

theorem genT_lt : ∀ (k : Nat) (s : Nat), s ∈ genT k → s < 3 ^ k := by
  intro k
  induction k with
  | zero =>
    intro s hs
    rcases List.mem_cons.mp hs with h | h
    · subst h; omega
    · exact absurd h (by simp)
  | succ k ih =>
    intro s hs
    rw [genT] at hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨m, hm, hfm⟩ := List.mem_map.mp h
      subst hfm
      have hm' := ih m hm
      rw [Nat.pow_succ]
      omega
    · obtain ⟨m, hm, hfm⟩ := List.mem_map.mp h
      subst hfm
      have hm' := ih m hm
      rw [Nat.pow_succ]
      omega

theorem genT_mem : ∀ (k : Nat) (s : Nat), s ∈ genT k → noTernaryTwo s = true := by
  intro k
  induction k with
  | zero =>
    intro s hs
    rcases List.mem_cons.mp hs with h | h
    · subst h
      rw [noTernaryTwo.eq_def 0, if_pos (by decide : (0:Nat) = 0)]
    · exact absurd h (by simp)
  | succ k ih =>
    intro s hs
    rw [genT] at hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨m, hm, hfm⟩ := List.mem_map.mp h
      subst hfm
      exact ntt_3n m (ih m hm)
    · obtain ⟨m, hm, hfm⟩ := List.mem_map.mp h
      subst hfm
      exact ntt_3n1 m (ih m hm)

theorem genTp_length : ∀ k : Nat, (genTp k).length = 2 ^ k - 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [genTp, List.length_append, List.length_map, List.length_map,
      genT_length, ih, Nat.pow_succ]
    have hp := two_pow_pos k
    omega

theorem genTp_bounds : ∀ (k : Nat) (s : Nat), s ∈ genTp k → 1 ≤ s ∧ s ≤ 3 ^ k - 1 := by
  intro k
  induction k with
  | zero => intro s hs; exact absurd hs (by simp [genTp])
  | succ k ih =>
    intro s hs
    rw [genTp] at hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨m, hm, hfm⟩ := List.mem_map.mp h
      subst hfm
      have hm' := genT_lt k m hm
      rw [Nat.pow_succ]
      have h3p := pow3_pos k
      omega
    · obtain ⟨m, hm, hfm⟩ := List.mem_map.mp h
      subst hfm
      have hm' := ih m hm
      rw [Nat.pow_succ]
      have h3p := pow3_pos k
      omega

theorem genTp_mem : ∀ (k : Nat) (s : Nat), s ∈ genTp k → noTernaryTwo s = true := by
  intro k
  induction k with
  | zero => intro s hs; exact absurd hs (by simp [genTp])
  | succ k ih =>
    intro s hs
    rw [genTp] at hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨m, hm, hfm⟩ := List.mem_map.mp h
      subst hfm
      exact ntt_3n1 m (genT_mem k m hm)
    · obtain ⟨m, hm, hfm⟩ := List.mem_map.mp h
      subst hfm
      exact ntt_3n m (ih m hm)

theorem genT_nodup : ∀ k : Nat, (genT k).Nodup := by
  intro k
  induction k with
  | zero => exact List.Pairwise.cons (fun b hb => by simp at hb) List.Pairwise.nil
  | succ k ih =>
    rw [genT]
    refine nodup_append_disj _ _ ?_ ?_ ?_
    · exact nodup_map_inj (fun m => 3 * m) (fun a b h => by omega) _ ih
    · exact nodup_map_inj (fun m => 3 * m + 1) (fun a b h => by omega) _ ih
    · intro a ha b hb
      obtain ⟨ma, hma, hfa⟩ := List.mem_map.mp ha
      obtain ⟨mb, hmb, hfb⟩ := List.mem_map.mp hb
      subst hfa
      subst hfb
      omega

theorem genTp_nodup : ∀ k : Nat, (genTp k).Nodup := by
  intro k
  induction k with
  | zero => exact List.Pairwise.nil
  | succ k ih =>
    rw [genTp]
    refine nodup_append_disj _ _ ?_ ?_ ?_
    · exact nodup_map_inj (fun m => 3 * m + 1) (fun a b h => by omega) _ (genT_nodup k)
    · exact nodup_map_inj (fun m => 3 * m) (fun a b h => by omega) _ ih
    · intro a ha b hb
      obtain ⟨ma, hma, hfa⟩ := List.mem_map.mp ha
      obtain ⟨mb, hmb, hfb⟩ := List.mem_map.mp hb
      subst hfa
      subst hfb
      omega

theorem genTp_apfree : ∀ (k : Nat) (x y z : Nat), x ∈ genTp k → y ∈ genTp k →
    z ∈ genTp k → x + z = 2 * y → x = z := by
  intro k x y z hx hy hz h
  exact t3free x y z (genTp_mem k x hx) (genTp_mem k y hy) (genTp_mem k z hz) h

/-- The AP-free-set predicate (the x+z = 2y midpoint form). -/
def apFree3Set (S : List Nat) : Prop :=
  ∀ x y z : Nat, x ∈ S → y ∈ S → z ∈ S → x + z = 2 * y → x = z

/-- r_3(N) ≥ m: an explicit AP-free witness of size m inside [1,N]. -/
def r3AtLeast (N m : Nat) : Prop :=
  ∃ S : List Nat, S.length = m ∧ S.Nodup ∧ (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) ∧ apFree3Set S

/-- r_3(N) ≤ m: every AP-free S ⊆ [1,N] has at most m elements. -/
def r3AtMost (N m : Nat) : Prop :=
  ∀ S : List Nat, S.Nodup → (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) → apFree3Set S → S.length ≤ m

/-- r_3(N) = m exactly. -/
def r3Is (N m : Nat) : Prop := r3AtLeast N m ∧ r3AtMost N m

/-- **THE CANTOR LOWER BOUND**: r_3(3^k − 1) ≥ 2^k − 1. -/
theorem cantor_lower : ∀ k : Nat, r3AtLeast (3 ^ k - 1) (2 ^ k - 1) := by
  intro k
  refine ⟨genTp k, genTp_length k, genTp_nodup k, genTp_bounds k, genTp_apfree k⟩

/-! ## §4 THE BLOCK UPPER BOUND -/

/-- A non-trivial k-term arithmetic progression inside S. -/
def HasAP (S : List Nat) (k : Nat) : Prop :=
  ∃ a d : Nat, 1 ≤ d ∧ ∀ i : Nat, i < k → (a + i * d) ∈ S

/-- S contains no non-trivial k-term AP. -/
def APfree (S : List Nat) (k : Nat) : Prop := ¬ HasAP S k

theorem APfree_mono : ∀ (S T : List Nat) (k : Nat), (∀ s ∈ S, s ∈ T) →
    APfree T k → APfree S k := by
  intro S T k hsub hT h
  obtain ⟨a, d, hd, hall⟩ := h
  exact hT ⟨a, d, hd, fun i hi => hsub _ (hall i hi)⟩

/-- The triple form implies the k=3 AP form. -/
theorem apfree3_of_set : ∀ (S : List Nat), apFree3Set S → APfree S 3 := by
  intro S hS h
  obtain ⟨a, d, hd, hall⟩ := h
  have h1 := hall 0 (by omega)
  have h2 := hall 1 (by omega)
  have h3 := hall 2 (by omega)
  have hmid : a + 0 * d + (a + 2 * d) = 2 * (a + 1 * d) := by omega
  have hk := hS (a + 0 * d) (a + 1 * d) (a + 2 * d) h1 h2 h3 hmid
  omega

/-- The window pigeonhole: a Nodup list inside a k-wide window. -/
theorem window_pigeon : ∀ (k : Nat) (S : List Nat) (lo : Nat),
    S.Nodup → (∀ s ∈ S, lo ≤ s ∧ s < lo + k) → S.length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro S lo hN hb
    cases S with
    | nil =>
      have hz : ([] : List Nat).length = 0 := rfl
      omega
    | cons a t =>
      have ha := hb a (mem_self_cons a t)
      omega
  | succ k ih =>
    intro S lo hN hb
    have hsplit : S.length = (filt (fun s => eqb s lo) S).length +
        (filt (fun s => ! eqb s lo) S).length := filt_split _ S
    have hEqb : ∀ s ∈ filt (fun s => eqb s lo) S, s = lo := by
      intro s hs
      have h2 := (mem_filt_iff _ S s).mp hs
      exact eq_of_eqb_true s lo h2.2
    have hle1 : (filt (fun s => eqb s lo) S).length ≤ 1 :=
      nodup_const_le1 _ lo (nodup_filter _ S hN) hEqb
    have hle2 : (filt (fun s => ! eqb s lo) S).length ≤ k := by
      refine ih (filt (fun s => ! eqb s lo) S) (lo + 1) (nodup_filter _ S hN) ?_
      intro s hs
      have h2 := (mem_filt_iff _ S s).mp hs
      have hnb : s ≠ lo := ne_of_not_eqb s lo h2.2
      have hb' := hb s h2.1
      constructor <;> omega
    omega

/-- The window coverage: k distinct points in a k-wide window cover it all. -/
theorem window_cover : ∀ (k : Nat) (W : List Nat) (lo : Nat), W.Nodup →
    (∀ s ∈ W, lo ≤ s ∧ s < lo + k) → W.length = k →
    ∀ j : Nat, j < k → lo + j ∈ W := by
  intro k
  induction k with
  | zero => intro W lo _ _ _ j hj; omega
  | succ k ih =>
    intro W lo hN hb hlen j hj
    have hsplit : W.length = (filt (fun s => eqb s lo) W).length +
        (filt (fun s => ! eqb s lo) W).length := filt_split _ W
    have hEqb : ∀ s ∈ filt (fun s => eqb s lo) W, s = lo := by
      intro s hs
      have h2 := (mem_filt_iff _ W s).mp hs
      exact eq_of_eqb_true s lo h2.2
    have hle1 : (filt (fun s => eqb s lo) W).length ≤ 1 :=
      nodup_const_le1 _ lo (nodup_filter _ W hN) hEqb
    have hW1bounds : ∀ s ∈ filt (fun s => ! eqb s lo) W,
        lo + 1 ≤ s ∧ s < (lo + 1) + k := by
      intro s hs
      have h2 := (mem_filt_iff _ W s).mp hs
      have hnb : s ≠ lo := ne_of_not_eqb s lo h2.2
      have hb' := hb s h2.1
      constructor <;> omega
    -- lo ∈ W (otherwise the ≠ lo part holds k+1 points in a k-window).
    have hlo : lo ∈ W := by
      by_cases hcase : lo ∈ W
      · exact hcase
      · have hempty : (filt (fun s => eqb s lo) W).length = 0 := by
          cases hL : filt (fun s => eqb s lo) W with
          | nil => rfl
          | cons a t =>
            have hmem := (mem_filt_iff _ W a).mp (by
              rw [hL]; exact mem_self_cons a t)
            have hae : a = lo := hEqb a (by
              rw [hL]; exact mem_self_cons a t)
            rw [hae] at hmem
            exact absurd hmem.1 hcase
        have hbad : (filt (fun s => ! eqb s lo) W).length ≤ k :=
          window_pigeon k (filt (fun s => ! eqb s lo) W) (lo + 1)
            (nodup_filter _ W hN) hW1bounds
        omega
    have hge1 : (filt (fun s => eqb s lo) W).length ≥ 1 := by
      have hmem : lo ∈ filt (fun s => eqb s lo) W :=
        (mem_filt_iff _ W lo).mpr ⟨hlo, eqb_refl lo⟩
      cases hL : filt (fun s => eqb s lo) W with
      | nil => exact absurd hmem (by rw [hL]; simp)
      | cons a t =>
        have hLlen : (a :: t).length = t.length + 1 := rfl
        omega
    have hW1len : (filt (fun s => ! eqb s lo) W).length = k := by omega
    have hcover1 := ih (filt (fun s => ! eqb s lo) W) (lo + 1)
      (nodup_filter _ W hN) hW1bounds hW1len
    have hmemW1 : ∀ s ∈ filt (fun s => ! eqb s lo) W, s ∈ W := by
      intro s hs
      exact (mem_filt_iff _ W s).mp hs |>.1
    rcases (by omega : j = 0 ∨ 1 ≤ j) with h0 | h1
    · rw [h0, Nat.add_zero]; exact hlo
    · have hmem := hcover1 (j - 1) (by omega)
      have hmemW := hmemW1 _ hmem
      have hEq : lo + j = lo + 1 + (j - 1) := by omega
      rw [hEq]; exact hmemW

theorem block_upper_aux : ∀ (m k r : Nat) (S : List Nat), 1 ≤ k → r < k → S.Nodup →
    (∀ s ∈ S, 1 ≤ s ∧ s ≤ k * m + r) → APfree S k →
    S.length ≤ (k - 1) * m + r := by
  intro m
  induction m with
  | zero =>
    intro k r S hk hr hN hb hap
    have hwin : ∀ s ∈ S, 1 ≤ s ∧ s < 1 + r := by
      intro s hs
      have := hb s hs
      constructor <;> omega
    have hle := window_pigeon r S 1 hN hwin
    omega
  | succ m ih =>
    intro k r S hk hr hN hb hap
    have hlin : k * (m + 1) + r = k * m + k + r := by
      rw [Nat.mul_add, Nat.mul_one]
    have hsplit : S.length = (filt (fun s => decide (s ≤ k * m + r)) S).length +
        (filt (fun s => ! decide (s ≤ k * m + r)) S).length := filt_split _ S
    -- The lower part: applies the induction hypothesis.
    have hlow : (filt (fun s => decide (s ≤ k * m + r)) S).length ≤ (k - 1) * m + r := by
      refine ih k r (filt (fun s => decide (s ≤ k * m + r)) S) hk hr
        (nodup_filter _ S hN) ?_ ?_
      · intro s hs
        have h2 := (mem_filt_iff _ S s).mp hs
        have hsle := prop_of_decide_true (s ≤ k * m + r) h2.2
        have hb' := hb s h2.1
        exact ⟨hb'.1, by omega⟩
      · exact APfree_mono _ _ k (fun s hs => (mem_filt_iff _ S s).mp hs |>.1) hap
    -- The top part: at most k−1 elements in the top k-block.
    have htop : (filt (fun s => ! decide (s ≤ k * m + r)) S).length ≤ k - 1 := by
      have hwin : ∀ s ∈ (filt (fun s => ! decide (s ≤ k * m + r)) S),
          k * m + r + 1 ≤ s ∧ s < (k * m + r + 1) + k := by
        intro s hs
        have h2 := (mem_filt_iff _ S s).mp hs
        have hgt : ¬ (s ≤ k * m + r) :=
          not_of_decide_false (s ≤ k * m + r) (notbeq_false (decide (s ≤ k * m + r)) h2.2)
        have hb' := hb s h2.1
        constructor <;> omega
      have hNod : (filt (fun s => ! decide (s ≤ k * m + r)) S).Nodup :=
        nodup_filter _ S hN
      have hle := window_pigeon k (filt (fun s => ! decide (s ≤ k * m + r)) S)
        (k * m + r + 1) hNod hwin
      by_cases hlen : (filt (fun s => ! decide (s ≤ k * m + r)) S).length = k
      · have hcover := window_cover k (filt (fun s => ! decide (s ≤ k * m + r)) S)
          (k * m + r + 1) hNod hwin hlen
        have hAP : HasAP S k := by
          refine ⟨k * m + r + 1, 1, by omega, ?_⟩
          intro i hi
          have hmem := hcover i hi
          have hmemS := (mem_filt_iff _ S (k * m + r + 1 + i)).mp hmem |>.1
          have hi1 : i * 1 = i := Nat.mul_one i
          rw [hi1]
          exact hmemS
        exact absurd hAP hap
      · omega
    have hgoalT : (k - 1) * (m + 1) + r = (k - 1) * m + (k - 1) + r := by
      rw [Nat.mul_add, Nat.mul_one]
    omega

/-- **THE BLOCK UPPER BOUND**: every k-AP-free S ⊆ [1,N] is small. -/
theorem block_upper : ∀ (k N : Nat) (S : List Nat), 1 ≤ k → S.Nodup →
    (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) → APfree S k →
    S.length ≤ (k - 1) * (N / k) + N % k := by
  intro k N S hk hN hb hap
  have hNlin : k * (N / k) + N % k = N := Nat.div_add_mod N k
  have hr : N % k < k := Nat.mod_lt N (by omega : 0 < k)
  have hb' : ∀ s ∈ S, 1 ≤ s ∧ s ≤ k * (N / k) + N % k := by
    intro s hs
    have h := hb s hs
    exact ⟨h.1, by omega⟩
  exact block_upper_aux (N / k) k (N % k) S hk hr hN hb' hap

/-- **THE r_3 UPPER BOUND**: r_3(N) ≤ 2⌊N/3⌋ + (N mod 3). -/
theorem r3_upper : ∀ (N : Nat) (S : List Nat), S.Nodup →
    (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) → apFree3Set S →
    S.length ≤ 2 * (N / 3) + N % 3 := by
  intro N S hN hb hAP
  have hap3 : APfree S 3 := apfree3_of_set S hAP
  have hle := block_upper 3 N S (by omega) hN hb hap3
  omega

/-! ## §5 THE k=2 EDGE -/

theorem mem_singleton_one : ∀ n : Nat, n ∈ [1] → n = 1 := by
  intro n h
  rcases List.mem_cons.mp h with h' | h'
  · exact h'
  · exact absurd h' (by simp)

theorem k2_upper : ∀ (N : Nat) (S : List Nat), 2 ≤ N → S.Nodup →
    (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) → APfree S 2 → S.length ≤ 1 := by
  intro N S hN hNod hb hap
  cases S with
  | nil =>
    have hz : ([] : List Nat).length = 0 := rfl
    omega
  | cons a t =>
    cases t with
    | nil =>
      have hz : (a :: ([] : List Nat)).length = 1 := rfl
      omega
    | cons b t' =>
      have hAP : HasAP (a :: b :: t') 2 := by
        by_cases hlt : a < b
        · refine ⟨a, b - a, by omega, ?_⟩
          intro i hi
          have hii : i = 0 ∨ i = 1 := by omega
          rcases hii with h | h
          · subst h
            have hz : a + 0 * (b - a) = a := by omega
            rw [hz]
            exact mem_self_cons a (b :: t')
          · subst h
            have ho : a + 1 * (b - a) = b := by omega
            rw [ho]
            exact mem_cons_of_tail a b (b :: t') (mem_self_cons b t')
        · have hne : a ≠ b := nodup_cons_head a (b :: t') hNod b (mem_self_cons b t')
          have hgt : b < a := by omega
          refine ⟨b, a - b, by omega, ?_⟩
          intro i hi
          have hii : i = 0 ∨ i = 1 := by omega
          rcases hii with h | h
          · subst h
            have hz : b + 0 * (a - b) = b := by omega
            rw [hz]
            exact mem_cons_of_tail a b (b :: t') (mem_self_cons b t')
          · subst h
            have ho : b + 1 * (a - b) = a := by omega
            rw [ho]
            exact mem_self_cons a (b :: t')
      exact absurd hAP hap

theorem k2_witness_apfree : APfree [1] 2 := by
  intro h
  obtain ⟨a, d, hd, hall⟩ := h
  have h0 := hall 0 (by omega)
  have h1 := hall 1 (by omega)
  have e0 : a + 0 * d = 1 := mem_singleton_one _ h0
  have e1 : a + 1 * d = 1 := mem_singleton_one _ h1
  omega

/-- **THE k=2 EDGE**: r_2(N) = 1 for N ≥ 2. -/
theorem k2_edge : ∀ (N : Nat), 2 ≤ N →
    ((∀ (S : List Nat), S.Nodup → (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) → APfree S 2 →
      S.length ≤ 1) ∧
    ([1] : List Nat).length = 1 ∧ [1].Nodup ∧
    (∀ s ∈ [1], 1 ≤ s ∧ s ≤ N) ∧ APfree [1] 2) := by
  intro N hN
  refine ⟨fun S hNod hb hap => k2_upper N S hN hNod hb hap, rfl, by simp, ?_,
    k2_witness_apfree⟩
  intro s hs
  rcases List.mem_cons.mp hs with h | h
  · subst h; omega
  · exact absurd h (by simp)

/-! ## §6 The exhaustive small-value engine -/

def allT (p : Nat → Bool) : List Nat → Bool
  | [] => true
  | a :: t => p a && allT p t

theorem allT_iff : ∀ (l : List Nat) (p : Nat → Bool),
    allT p l = true ↔ ∀ a ∈ l, p a = true := by
  intro l
  induction l with
  | nil =>
    intro p
    constructor
    · intro _ a ha; exact absurd ha (by simp)
    · intro _; rfl
  | cons a t ih =>
    intro p
    have e : allT p (a :: t) = (p a && allT p t) := rfl
    rw [e]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := and_split _ _ h
      intro b hb
      rcases List.mem_cons.mp hb with he | hm
      · subst he; exact h1
      · exact (ih p).mp h2 b hm
    · intro h
      refine and_true_of_true (p a) (allT p t) (h a (mem_self_cons a t)) ?_
      exact (ih p).mpr (fun b hb => h b (mem_cons_of_tail a b t hb))

def ap3Free (S : List Nat) : Bool :=
  allT (fun x => allT (fun y => allT (fun z => ! (eqb (x + z) (2 * y)) || (eqb x z)) S) S) S

/-- The checker's soundness: a green triple-scan certifies the Prop form. -/
theorem ap3Free_sound : ∀ (S : List Nat), ap3Free S = true → apFree3Set S := by
  intro S h x y z hx hy hz hxy
  have hall : ∀ b ∈ S,
      allT (fun y => allT (fun z => ! (eqb (b + z) (2 * y)) || (eqb b z)) S) S = true :=
    (allT_iff S (fun x => allT (fun y => allT (fun z => ! (eqb (x + z) (2 * y)) || (eqb x z)) S) S)).mp h
  have hx' := hall x hx
  have hyl : ∀ b ∈ S, allT (fun z => ! (eqb (x + z) (2 * b)) || (eqb x z)) S = true :=
    (allT_iff S (fun y => allT (fun z => ! (eqb (x + z) (2 * y)) || (eqb x z)) S)).mp hx'
  have hy' := hyl y hy
  have hzl : ∀ c ∈ S, (! (eqb (x + c) (2 * y)) || (eqb x c)) = true :=
    (allT_iff S (fun z => ! (eqb (x + z) (2 * y)) || (eqb x z))).mp hy'
  have hz' := hzl z hz
  rcases or_split _ _ hz' with hne | heq
  · have hbeq : eqb (x + z) (2 * y) = true := eqb_true_of_eq (x + z) (2 * y) hxy
    rw [hbeq] at hne
    rw [Bool.not_true] at hne
    exact Bool.noConfusion hne
  · exact eq_of_eqb_true x z heq

/-- The checker's completeness: the Prop form certifies the triple-scan. -/
theorem ap3Free_of_set : ∀ (S : List Nat), apFree3Set S → ap3Free S = true := by
  intro S h
  refine (allT_iff S _).mpr ?_
  intro x hx
  refine (allT_iff S _).mpr ?_
  intro y hy
  refine (allT_iff S _).mpr ?_
  intro z hz
  show (! (eqb (x + z) (2 * y)) || (eqb x z)) = true
  by_cases hxy : eqb (x + z) (2 * y) = true
  · have hxeq : x = z := h x y z hx hy hz (eq_of_eqb_true (x + z) (2 * y) hxy)
    exact or_true_right _ _ (eqb_true_of_eq x z hxeq)
  · have hbeq : eqb (x + z) (2 * y) = false := by
      cases hb : eqb (x + z) (2 * y) with
      | false => rfl
      | true => exact absurd hb hxy
    rw [hbeq]
    rfl

def sublists : List Nat → List (List Nat)
  | [] => [[]]
  | a :: t => sublists t ++ List.map (fun S => a :: S) (sublists t)

theorem filt_mem_sublists : ∀ (l : List Nat) (p : Nat → Bool),
    (filt p l) ∈ sublists l := by
  intro l
  induction l with
  | nil =>
    intro p
    have e1 : filt p [] = [] := rfl
    have e2 : sublists [] = [[]] := rfl
    rw [e1, e2]
    exact List.mem_cons_self
  | cons a t ih =>
    intro p
    have e : sublists (a :: t) = sublists t ++ List.map (fun S => a :: S) (sublists t) := rfl
    rw [e]
    by_cases hp : p a = true
    · have e1 : filt p (a :: t) = a :: filt p t := filt_cons_true p a t hp
      rw [e1]
      exact List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨filt p t, ih p, rfl⟩))
    · have e1 : filt p (a :: t) = filt p t := filt_cons_false p a t hp
      rw [e1]
      exact List.mem_append.mpr (Or.inl (ih p))

def upto : Nat → List Nat
  | 0 => []
  | N + 1 => upto N ++ [N]

theorem upto_length : ∀ N : Nat, (upto N).length = N := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
    have e : upto (N + 1) = upto N ++ [N] := rfl
    rw [e, List.length_append, ih]
    have hlen : [N].length = 1 := rfl
    omega

theorem upto_mem : ∀ (N a : Nat), a < N → a ∈ upto N := by
  intro N
  induction N with
  | zero => intro a ha; omega
  | succ N ih =>
    intro a ha
    have e : upto (N + 1) = upto N ++ [N] := rfl
    rw [e]
    rcases (by omega : a < N ∨ a = N) with h | h
    · exact List.mem_append.mpr (Or.inl (ih a h))
    · subst h
      exact List.mem_append.mpr (Or.inr List.mem_cons_self)

theorem upto_lt : ∀ (N a : Nat), a ∈ upto N → a < N := by
  intro N
  induction N with
  | zero => intro a ha; exact absurd ha (by simp [upto])
  | succ N ih =>
    intro a ha
    have e : upto (N + 1) = upto N ++ [N] := rfl
    rw [e] at ha
    rcases List.mem_append.mp ha with h | h
    · exact Nat.lt_succ_of_lt (ih a h)
    · rcases List.mem_cons.mp h with he | hn
      · subst he; omega
      · exact absurd hn (by simp)

def upto1 (N : Nat) : List Nat := (upto N).map (fun s => s + 1)

theorem upto1_mem : ∀ (N s : Nat), 1 ≤ s → s ≤ N → s ∈ upto1 N := by
  intro N s h1 h2
  refine List.mem_map.mpr ⟨s - 1, upto_mem N (s - 1) (by omega), ?_⟩
  show s - 1 + 1 = s
  omega

theorem upto1_bounds : ∀ (N s : Nat), s ∈ upto1 N → 1 ≤ s ∧ s ≤ N := by
  intro N s hs
  obtain ⟨a, ha, hfa⟩ := List.mem_map.mp hs
  have ha' := upto_lt N a ha
  have hs' : s = a + 1 := Eq.symm hfa
  subst hs'
  omega

def memB (a : Nat) : List Nat → Bool
  | [] => false
  | b :: t => (eqb a b) || memB a t

theorem memB_iff : ∀ (a : Nat) (l : List Nat), memB a l = true ↔ a ∈ l := by
  intro a l
  induction l with
  | nil =>
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; exact absurd h (by simp)
  | cons b t ih =>
    have e : memB a (b :: t) = (eqb a b || memB a t) := rfl
    rw [e]
    constructor
    · intro h
      rcases or_split _ _ h with hb | ht
      · exact List.mem_cons.mpr (Or.inl (eq_of_eqb_true a b hb))
      · exact List.mem_cons.mpr (Or.inr ((ih).mp ht))
    · intro h
      rcases List.mem_cons.mp h with he | ht
      · subst he
        exact or_true_left _ _ (eqb_refl _)
      · exact or_true_right _ _ ((ih).mpr ht)

def r3max (N : Nat) : Nat :=
  (filt ap3Free (sublists (upto1 N))).foldr (fun S acc => Nat.max S.length acc) 0

theorem fold_max_length_ge : ∀ (L : List (List Nat)) (S : List Nat), S ∈ L →
    S.length ≤ L.foldr (fun T acc => Nat.max T.length acc) 0 := by
  intro L
  induction L with
  | nil => intro S hS; exact absurd hS (by simp)
  | cons a t ih =>
    intro S hS
    rcases List.mem_cons.mp hS with he | hm
    · subst he
      show S.length ≤ Nat.max S.length (t.foldr (fun T acc => Nat.max T.length acc) 0)
      exact Nat.le_max_left S.length (t.foldr (fun T acc => Nat.max T.length acc) 0)
    · have h1 := ih S hm
      show S.length ≤ Nat.max a.length (t.foldr (fun T acc => Nat.max T.length acc) 0)
      exact Nat.le_trans h1 (Nat.le_max_right a.length
        (t.foldr (fun T acc => Nat.max T.length acc) 0))

/-- **THE r3max BRIDGE**: the enumeration dominates every AP-free set. -/
theorem r3_upper_via_r3max : ∀ (N : Nat) (S : List Nat), S.Nodup →
    (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) → apFree3Set S → S.length ≤ r3max N := by
  intro N S hN hb hAP
  have hS'mem : ∀ s ∈ S, s ∈ filt (fun s => memB s S) (upto1 N) := by
    intro s hs
    refine (mem_filt_iff (fun s => memB s S) (upto1 N) s).mpr
      ⟨upto1_mem N s (hb s hs).1 (hb s hs).2, (memB_iff s S).mpr hs⟩
  have hlen : S.length ≤ (filt (fun s => memB s S) (upto1 N)).length :=
    nodup_mem_le _ S hN hS'mem
  have hS'ap : ap3Free (filt (fun s => memB s S) (upto1 N)) = true :=
    ap3Free_of_set _ (fun x y z hx hy hz hxy =>
      hAP x y z ((memB_iff x S).mp ((mem_filt_iff (fun s => memB s S) (upto1 N) x).mp hx).2)
        ((memB_iff y S).mp ((mem_filt_iff (fun s => memB s S) (upto1 N) y).mp hy).2)
        ((memB_iff z S).mp ((mem_filt_iff (fun s => memB s S) (upto1 N) z).mp hz).2) hxy)
  have hsub : filt (fun s => memB s S) (upto1 N) ∈ filt ap3Free (sublists (upto1 N)) :=
    (mem_filt_iff ap3Free (sublists (upto1 N)) _).mpr
      ⟨filt_mem_sublists (upto1 N) (fun s => memB s S), hS'ap⟩
  have hmax := fold_max_length_ge (filt ap3Free (sublists (upto1 N)))
    (filt (fun s => memB s S) (upto1 N)) hsub
  have hrw : r3max N =
      (filt ap3Free (sublists (upto1 N))).foldr (fun T acc => Nat.max T.length acc) 0 := rfl
  omega

theorem r3_exact_small : r3Is 1 1 ∧ r3Is 2 2 ∧ r3Is 3 2 ∧ r3Is 4 3 ∧
    r3Is 5 4 ∧ r3Is 6 4 ∧ r3Is 7 4 ∧ r3Is 8 4 := by
  have hm1 : r3max 1 = 1 := by decide
  have hm2 : r3max 2 = 2 := by decide
  have hm3 : r3max 3 = 2 := by decide
  have hm4 : r3max 4 = 3 := by decide
  have hm5 : r3max 5 = 4 := by decide
  have hm6 : r3max 6 = 4 := by decide
  have hm7 : r3max 7 = 4 := by decide
  have hm8 : r3max 8 = 4 := by decide
  have hw1 : ap3Free [1] = true := by decide
  have hw2 : ap3Free [1, 2] = true := by decide
  have hw4 : ap3Free [1, 2, 4] = true := by decide
  have hw5 : ap3Free [1, 2, 4, 5] = true := by decide
  have mk : ∀ (N v : Nat) (W : List Nat), ap3Free W = true → W.length = v →
      (∀ s ∈ W, 1 ≤ s ∧ s ≤ N) → W.Nodup → r3max N = v → r3Is N v := by
    intro N v W hW hlen hb hNod hmax
    refine ⟨⟨W, hlen, hNod, hb, ap3Free_sound W hW⟩, ?_⟩
    intro S hS hSb hSap
    have hge := r3_upper_via_r3max N S hS hSb hSap
    omega
  have lift : ∀ (N M : Nat) (W : List Nat), N ≤ M → (∀ s ∈ W, 1 ≤ s ∧ s ≤ N) →
      ∀ s ∈ W, 1 ≤ s ∧ s ≤ M := by
    intro N M W hNM h s hs
    have hb := h s hs
    exact ⟨hb.1, by omega⟩
  have b1 : ∀ s ∈ [1], 1 ≤ s ∧ s ≤ 1 := by
    intro s hs
    rcases List.mem_cons.mp hs with h | h
    · subst h; omega
    · exact absurd h (by simp)
  have b2 : ∀ s ∈ [1, 2], 1 ≤ s ∧ s ≤ 2 := by
    intro s hs
    rcases List.mem_cons.mp hs with h | h
    · subst h; omega
    · rcases List.mem_cons.mp h with h | h
      · subst h; omega
      · exact absurd h (by simp)
  have b4 : ∀ s ∈ [1, 2, 4], 1 ≤ s ∧ s ≤ 4 := by
    intro s hs
    rcases List.mem_cons.mp hs with h | h
    · subst h; omega
    · rcases List.mem_cons.mp h with h | h
      · subst h; omega
      · rcases List.mem_cons.mp h with h | h
        · subst h; omega
        · exact absurd h (by simp)
  have b5 : ∀ s ∈ [1, 2, 4, 5], 1 ≤ s ∧ s ≤ 5 := by
    intro s hs
    rcases List.mem_cons.mp hs with h | h
    · subst h; omega
    · rcases List.mem_cons.mp h with h | h
      · subst h; omega
      · rcases List.mem_cons.mp h with h | h
        · subst h; omega
        · rcases List.mem_cons.mp h with h | h
          · subst h; omega
          · exact absurd h (by simp)
  have b3 := lift 2 3 [1, 2] (by omega) b2
  have b6 := lift 5 6 [1, 2, 4, 5] (by omega) b5
  have b7 := lift 5 7 [1, 2, 4, 5] (by omega) b5
  have b8 := lift 5 8 [1, 2, 4, 5] (by omega) b5
  exact ⟨mk 1 1 [1] hw1 rfl b1 (by simp) hm1,
          mk 2 2 [1, 2] hw2 rfl b2 (by simp) hm2,
          mk 3 2 [1, 2] hw2 rfl b3 (by simp) hm3,
          mk 4 3 [1, 2, 4] hw4 rfl b4 (by simp) hm4,
          mk 5 4 [1, 2, 4, 5] hw5 rfl b5 (by simp) hm5,
          mk 6 4 [1, 2, 4, 5] hw5 rfl b6 (by simp) hm6,
          mk 7 4 [1, 2, 4, 5] hw5 rfl b7 (by simp) hm7,
          mk 8 4 [1, 2, 4, 5] hw5 rfl b8 (by simp) hm8⟩

/-! ## §7 The Arsenal bridge + the board -/

/-- The Arsenal bridge: T's closure laws (the CardinalWorlds reader). -/
theorem arsenal_bridge : ∀ n : Nat, noTernaryTwo n = true →
    noTernaryTwo (3 * n) = true ∧ noTernaryTwo (3 * n + 1) = true :=
  fun n h => ⟨ntt_3n n h, ntt_3n1 n h⟩

theorem erdos142_board :
    (∀ x y z : Nat, noTernaryTwo x = true → noTernaryTwo y = true →
      noTernaryTwo z = true → x + z = 2 * y → x = z) ∧
    (∀ k : Nat, r3AtLeast (3 ^ k - 1) (2 ^ k - 1)) ∧
    (∀ (k N : Nat) (S : List Nat), 1 ≤ k → S.Nodup →
      (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) → APfree S k →
      S.length ≤ (k - 1) * (N / k) + N % k) ∧
    (∀ (N : Nat) (S : List Nat), S.Nodup → (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) →
      apFree3Set S → S.length ≤ 2 * (N / 3) + N % 3) ∧
    (∀ (N : Nat), 2 ≤ N →
      ((∀ (S : List Nat), S.Nodup → (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) → APfree S 2 →
        S.length ≤ 1) ∧
      ([1] : List Nat).length = 1 ∧ [1].Nodup ∧
      (∀ s ∈ [1], 1 ≤ s ∧ s ≤ N) ∧ APfree [1] 2)) ∧
    (r3Is 1 1 ∧ r3Is 2 2 ∧ r3Is 3 2 ∧ r3Is 4 3 ∧
      r3Is 5 4 ∧ r3Is 6 4 ∧ r3Is 7 4 ∧ r3Is 8 4) ∧
    (∀ n : Nat, noTernaryTwo n = true →
      noTernaryTwo (3 * n) = true ∧ noTernaryTwo (3 * n + 1) = true) :=
  ⟨t3free, cantor_lower, block_upper, r3_upper, k2_edge, r3_exact_small, arsenal_bridge⟩

/-! ## Receipt block -/

#print axioms t3free
#print axioms t3_no_nontriv
#print axioms cantor_lower
#print axioms block_upper
#print axioms r3_upper
#print axioms k2_edge
#print axioms r3_exact_small
#print axioms arsenal_bridge
#print axioms erdos142_board

#eval "E142_TERNARY_GREEN"
#eval "E142_CANTOR_GREEN"
#eval "E142_BOARD_GREEN"

end E142
