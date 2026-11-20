import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos61 — THE ERDOS-HAJNAL FAMILY KERNEL r1 (W68-61K)

Erdős #61 (verbatim, erdosproblems.com/61):
"For any graph H is there some c=c(H)>0 such that every graph G on n vertices
that does not contain H as an induced subgraph contains either a complete graph
or independent set on ≥ n^c vertices?" (THE ERDŐS-HAJNAL CONJECTURE, open in
general.)

## THE FAMILY THEOREM (this kernel's complete unconditional scope)
For the explicit family F7 = {K1, K2, K̄2, P3, P̄3, K3, K̄3} — seven of the eight
mission members — every H-free graph on n vertices contains a clique OR an
independent set of size ≥ ⌊√n⌋ (SHARP bound; exponent c(H) = 1/2; mirror-certified
n ≤ 6 by engine61/mirror61.py and engine61/doubter/mirror_battery.py: zero sharp
violations, P3-free census = 278 = Bell(1..6), dual engines agree exactly).

The eighth member P4 (cographs: Seinsche's union/join split) is the live
continuation front — honest scope; NOT claimed by this kernel.

## THE LAWS
1. TRIVIAL FAMILY: K2-free → the whole vertex list is independent (α = n);
   K̄2-free → the whole list is a clique (ω = n); K1-free → n = 0 vacuous.
2. THE UNIFIED GREEDY ENGINE `E61.closedNbhd_greedy`: if every closed
   neighborhood has size ≤ D then an independent S exists with D · |S| ≥ n.
3. THE DEGREE LAW `E61.k3_bound` (K3-free): some OPEN neighborhood ≥ ⌊√n⌋ is an
   independent set (triangle-freeness), else the greedy lands |S| ≥ ⌊√n⌋.
4. THE CLUSTER LAW `E61.p3_bound` (P3-free): the closed neighborhood N[v] is a
   clique; some N[v] ≥ ⌊√n⌋ gives the clique, else the greedy lands the rest.
5. THE COMPLEMENT TRANSFERS `E61.kb3_bound`, `E61.pb3_bound`.
6. THE TIGHTNESS WITNESS `E61.tight_family`: for every j ≥ 1, the disjoint
   union of 2^j copies of K_{2^j} (same-block cluster graph on n = 2^j · 2^j
   vertices) has max(ω, α) = 2^j = ⌊√n⌋ EXACTLY — the c = 1/2 exponent is
   OPTIMAL. `E61.arsenal_bridge` applies BOSS's Arsenal
   (CardinalWorlds.two_pow_pos, CardinalWorlds.three_pow_pos_lemma).
7. THE HYPOTHESIS-FREE BOARD `E61.family_board_uncond` (W73, task 1-a): the
   bundled carrier `SGraph α` = adjacency + the two simple-graph laws
   (`hsym`, `hirr`) as STRUCTURE FIELDS, so the seven-conjunct family
   theorem proves exactly the same statement with ZERO premises on the
   theorem itself; inhabited by `sgEmptyUnit`, `sgCompleteBool` (real edge:
   true joined to false), `sgEmptyBool` (receipt `E61_UNCOND_GREEN`).

## REPRESENTATION (pinned)
Graph = adjacency `adj : α → α → Bool` with symmetry (hsym) and irreflexivity
(hirr); vertex set = `vs : List α` with `vs.Nodup`; n = vs.length;
`fsqrt n` = ⌊√n⌋ (house, spec-certified, `E61.fsqrt_eq` pins uniqueness).

## CAMPAIGN LAWS HELD
Arsenal imports only (erdosternary2 + CardinalWorlds + CardinalWorldsV2 —
BOSS's maths); zero sorry/admit/native_decide; axioms within
[propext, Classical.choice, Quot.sound]; no decide over ∀ k < N, N > 501.
-/

namespace E61

/-! ## §0 House machinery: eqb, memB, hfilt, append, herase, Nat mono -/

/-- Structural Boolean equality on α. -/
def eqb {α : Type} [DecidableEq α] (a b : α) : Bool :=
  decide (a = b)

theorem eqb_refl {α : Type} [DecidableEq α] (a : α) : eqb a a = true := by
  unfold eqb
  exact decide_eq_true rfl

theorem eq_of_eqb_true {α : Type} [DecidableEq α] (a b : α) (h : eqb a b = true) : a = b := by
  unfold eqb at h
  exact of_decide_eq_true h

theorem ne_of_eqb_false {α : Type} [DecidableEq α] (a b : α) (h : eqb a b = false) : a ≠ b := by
  unfold eqb at h
  intro heq
  rw [heq] at h
  simp at h

theorem eqb_false_iff {α : Type} [DecidableEq α] (a b : α) : eqb a b = false ↔ a ≠ b := by
  constructor
  · intro h heq
    have htrue : eqb a b = true := by rw [heq]; exact eqb_refl b
    rw [htrue] at h
    exact Bool.noConfusion h
  · intro h
    cases hb : eqb a b with
    | false => rfl
    | true => exact absurd (eq_of_eqb_true a b hb) h

/-- Boolean membership. -/
def memB {α : Type} [DecidableEq α] (u : α) : List α → Bool
  | [] => false
  | b :: t => if eqb u b = true then true else memB u t

theorem memB_cons_self {α : Type} [DecidableEq α] (u b : α) (t : List α) (h : u = b) :
    memB u (b :: t) = true := by
  rw [h]
  unfold memB
  rw [eqb_refl b]
  exact if_pos rfl

theorem memB_iff {α : Type} [DecidableEq α] : ∀ (u : α) (l : List α),
    memB u l = true ↔ u ∈ l := by
  intro u l
  induction l with
  | nil =>
    constructor
    · intro h
      exact Bool.noConfusion h
    · intro hc
      exact absurd hc (by simp)
  | cons b t ih =>
    by_cases hub : u = b
    · constructor
      · intro _
        rw [hub]
        exact List.mem_cons.mpr (Or.inl rfl)
      · intro _
        rw [hub]
        exact memB_cons_self b b t rfl
    · have hf : memB u (b :: t) = memB u t := by
        have hneb : eqb u b = false := (eqb_false_iff u b).mpr hub
        show (if eqb u b = true then true else memB u t) = memB u t
        rw [hneb, if_neg (fun hc => Bool.noConfusion hc)]
      rw [hf]
      constructor
      · intro h
        exact List.mem_cons.mpr (Or.inr ((ih).mp h))
      · intro hc
        rcases List.mem_cons.mp hc with h | h
        · exact absurd h hub
        · exact (ih).mpr h

theorem memB_false_of_nmem {α : Type} [DecidableEq α] (u : α) (l : List α) (h : ¬ (u ∈ l)) :
    memB u l = false := by
  cases hb : memB u l with
  | false => rfl
  | true => exact absurd ((memB_iff u l).mp hb) h

theorem not_mem_of_memB_false {α : Type} [DecidableEq α] (u : α) (l : List α) (h : memB u l = false) :
    ¬ (u ∈ l) := by
  intro hc
  rw [(memB_iff u l).mpr hc] at h
  exact Bool.noConfusion h

/-- The house filter. -/
def hfilt {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | a :: t => if p a = true then a :: hfilt p t else hfilt p t

theorem hfilt_cons_true {α : Type} (p : α → Bool) (a : α) (t : List α) (h : p a = true) :
    hfilt p (a :: t) = a :: hfilt p t := by
  have e : hfilt p (a :: t) = if p a = true then a :: hfilt p t else hfilt p t := rfl
  rw [e, if_pos h]

theorem hfilt_cons_false {α : Type} (p : α → Bool) (a : α) (t : List α) (h : ¬ (p a = true)) :
    hfilt p (a :: t) = hfilt p t := by
  have e : hfilt p (a :: t) = if p a = true then a :: hfilt p t else hfilt p t := rfl
  rw [e, if_neg h]

theorem mem_hfilt_iff {α : Type} (p : α → Bool) : ∀ (l : List α) (s : α),
    s ∈ hfilt p l ↔ (s ∈ l ∧ p s = true) := by
  intro l
  induction l with
  | nil =>
    intro s
    have e0 : hfilt p ([] : List α) = [] := rfl
    constructor
    · intro hs
      rw [e0] at hs
      exact absurd hs (by simp)
    · intro hs
      exact absurd hs.1 (by simp)
  | cons a t ih =>
    intro s
    by_cases hp : p a = true
    · rw [hfilt_cons_true p a t hp]
      constructor
      · intro hs
        rcases List.mem_cons.mp hs with h | h
        · exact ⟨List.mem_cons.mpr (Or.inl h), by rw [h]; exact hp⟩
        · have h2 := (ih s).mp h
          exact ⟨List.mem_cons.mpr (Or.inr h2.1), h2.2⟩
      · intro hs
        rcases List.mem_cons.mp hs.1 with h | h
        · exact List.mem_cons.mpr (Or.inl h)
        · exact List.mem_cons.mpr (Or.inr ((ih s).mpr ⟨h, hs.2⟩))
    · rw [hfilt_cons_false p a t hp]
      constructor
      · intro hs
        have h2 := (ih s).mp hs
        exact ⟨List.mem_cons.mpr (Or.inr h2.1), h2.2⟩
      · intro hs
        rcases List.mem_cons.mp hs.1 with h | h
        · rw [h] at hs; exact absurd hs.2 hp
        · exact (ih s).mpr ⟨h, hs.2⟩

theorem hfilt_subset {α : Type} (p : α → Bool) (l : List α) :
    ∀ s ∈ hfilt p l, s ∈ l := by
  intro s hs
  exact ((mem_hfilt_iff p l s).mp hs).1

theorem hfilt_nodup {α : Type} (p : α → Bool) : ∀ (l : List α), l.Nodup → (hfilt p l).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a t ih =>
    intro hnd
    by_cases hp : p a = true
    · rw [hfilt_cons_true p a t hp]
      refine List.Pairwise.cons ?_ ?_
      · intro b hb
        obtain ⟨hc, _⟩ := (mem_hfilt_iff p t b).mp hb
        cases hnd with
        | cons hhead _ => exact hhead b hc
      · cases hnd with
        | cons _ htail => exact ih htail
    · rw [hfilt_cons_false p a t hp]
      cases hnd with
      | cons _ htail => exact ih htail

/-- Filter-complement length split. -/
theorem hfilt_length_split {α : Type} (p : α → Bool) : ∀ (l : List α), l.Nodup →
    (hfilt p l).length + (hfilt (fun x => !(p x)) l).length = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro hnd
    by_cases hp : p a = true
    · rw [hfilt_cons_true p a t hp]
      have hneg : ¬ ((fun x => !(p x)) a = true) := by
        intro hcontra
        have hcha : (!(p a)) = true := hcontra
        rw [hp] at hcha
        exact Bool.noConfusion hcha
      rw [hfilt_cons_false (fun x => !(p x)) a t hneg]
      have hIH : (hfilt p t).length + (hfilt (fun x => !(p x)) t).length = t.length := by
        cases hnd with
        | cons _ htail => exact ih htail
      simp only [List.length_cons]
      omega
    · rw [hfilt_cons_false p a t hp]
      have hpos : ((fun x => !(p x)) a = true) := by
        have hpa : (!(p a)) = true := by
          cases hb : p a with
          | false => rfl
          | true => exact absurd hb hp
        exact hpa
      rw [hfilt_cons_true (fun x => !(p x)) a t hpos]
      have hIH : (hfilt p t).length + (hfilt (fun x => !(p x)) t).length = t.length := by
        cases hnd with
        | cons _ htail => exact ih htail
      simp only [List.length_cons]
      omega

theorem mem_app_iff {α : Type} : ∀ (l1 l2 : List α) (u : α),
    u ∈ l1 ++ l2 ↔ (u ∈ l1 ∨ u ∈ l2) := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 u
    simp only [List.nil_append]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun hc => absurd hc (by simp)) id⟩
  | cons a t ih =>
    intro l2 u
    rw [List.cons_append]
    constructor
    · intro hc
      rcases List.mem_cons.mp hc with h | h
      · exact Or.inl (List.mem_cons.mpr (Or.inl h))
      · rcases (ih l2 u).mp h with h1 | h1
        · exact Or.inl (List.mem_cons.mpr (Or.inr h1))
        · exact Or.inr h1
    · intro hc
      rcases hc with h | h
      · rcases List.mem_cons.mp h with h1 | h1
        · exact List.mem_cons.mpr (Or.inl h1)
        · exact List.mem_cons.mpr (Or.inr ((ih l2 u).mpr (Or.inl h1)))
      · exact List.mem_cons.mpr (Or.inr ((ih l2 u).mpr (Or.inr h)))

theorem length_app {α : Type} : ∀ (l1 l2 : List α),
    (l1 ++ l2).length = l1.length + l2.length := by
  intro l1
  induction l1 with
  | nil => intro l2; simp
  | cons a t ih =>
    intro l2
    rw [List.cons_append]
    simp only [List.length_cons]
    rw [ih l2]
    omega

/-- House erase. -/
def herase {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | b :: t => if eqb b a = true then herase a t else b :: herase a t

theorem herase_length_le {α : Type} [DecidableEq α] (a : α) : ∀ (l : List α),
    (herase a l).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp [herase]
  | cons b t ih =>
    by_cases hba : b = a
    · rw [hba]
      unfold herase
      rw [eqb_refl a, if_pos rfl]
      have hle : (herase a t).length ≤ t.length := ih
      simp only [List.length_cons]
      omega
    · have hbea : eqb b a = false := (eqb_false_iff b a).mpr hba
      unfold herase
      rw [if_neg (fun hc => by rw [hbea] at hc; exact Bool.noConfusion hc)]
      simp only [List.length_cons]
      omega

theorem herase_length_drop {α : Type} [DecidableEq α] (a : α) : ∀ (l : List α), a ∈ l →
    (herase a l).length + 1 ≤ l.length := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons b t ih =>
    intro h
    by_cases hba : b = a
    · rw [hba]
      unfold herase
      rw [eqb_refl a, if_pos rfl]
      have hle : (herase a t).length ≤ t.length := herase_length_le a t
      simp only [List.length_cons]
      omega
    · have hbea : eqb b a = false := (eqb_false_iff b a).mpr hba
      have hbt : a ∈ t := by
        rcases List.mem_cons.mp h with h1 | h1
        · exact absurd h1.symm hba
        · exact h1
      have hIH := ih hbt
      unfold herase
      rw [if_neg (fun hc => by rw [hbea] at hc; exact Bool.noConfusion hc)]
      simp only [List.length_cons]
      omega

theorem herase_mem_of_ne {α : Type} [DecidableEq α] (a x : α) : ∀ (l : List α),
    x ∈ l → x ≠ a → x ∈ herase a l := by
  intro l
  induction l with
  | nil => intro h _; exact absurd h (by simp)
  | cons b t ih =>
    intro h hne
    by_cases hxb : x = b
    · rw [hxb]
      unfold herase
      have hbea : eqb b a = false := (eqb_false_iff b a).mpr
        (fun heq => hne (hxb ▸ heq))
      rw [if_neg (fun hc => by rw [hbea] at hc; exact Bool.noConfusion hc)]
      exact List.mem_cons.mpr (Or.inl rfl)
    · have hxt : x ∈ t := by
        rcases List.mem_cons.mp h with h1 | h1
        · exact absurd h1 hxb
        · exact h1
      unfold herase
      by_cases hba : b = a
      · rw [hba, eqb_refl a, if_pos rfl]
        exact ih hxt hne
      · have hbea : eqb b a = false := (eqb_false_iff b a).mpr hba
        rw [if_neg (fun hc => by rw [hbea] at hc; exact Bool.noConfusion hc)]
        exact List.mem_cons.mpr (Or.inr (ih hxt hne))

theorem herase_subset {α : Type} [DecidableEq α] (a : α) : ∀ (l : List α) (x : α), x ∈ herase a l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x hx; exact absurd hx (by simp [herase])
  | cons b t ih =>
    intro x hx
    unfold herase at hx
    by_cases hba : b = a
    · have hbea : eqb b a = true := hba ▸ eqb_refl a
      rw [hbea, if_pos rfl] at hx
      exact List.mem_cons.mpr (Or.inr (ih x hx))
    · have hbea : eqb b a = false := (eqb_false_iff b a).mpr hba
      rw [hbea, if_neg (fun hc => Bool.noConfusion hc)] at hx
      rcases List.mem_cons.mp hx with h1 | h1
      · exact List.mem_cons.mpr (Or.inl h1)
      · exact List.mem_cons.mpr (Or.inr (ih x h1))

theorem herase_nodup {α : Type} [DecidableEq α] (a : α) : ∀ (l : List α), l.Nodup →
    (herase a l).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons b t ih =>
    intro hnd
    unfold herase
    by_cases hba : b = a
    · rw [hba, eqb_refl a, if_pos rfl]
      cases hnd with
      | cons _ htail => exact ih htail
    · have hbea : eqb b a = false := (eqb_false_iff b a).mpr hba
      rw [if_neg (fun hc => by rw [hbea] at hc; exact Bool.noConfusion hc)]
      refine List.Pairwise.cons ?_ ?_
      · intro x hx
        cases hnd with
        | cons hhead _ => exact hhead x (herase_subset a t x hx)
      · cases hnd with
        | cons _ htail => exact ih htail

/-- Nodup subset forces the length order. -/
theorem subset_length_le {α : Type} [DecidableEq α] : ∀ (l tgt : List α),
    l.Nodup → (∀ x ∈ l, x ∈ tgt) → l.length ≤ tgt.length := by
  intro l
  induction l with
  | nil => intro tgt _ _; simp
  | cons a t ih =>
    intro tgt hnd hsub
    have ha : a ∈ tgt := hsub a (List.mem_cons.mpr (Or.inl rfl))
    have hlen : (herase a tgt).length + 1 ≤ tgt.length := herase_length_drop a tgt ha
    have hsub' : ∀ x ∈ t, x ∈ herase a tgt := by
      intro x hx
      refine herase_mem_of_ne a x tgt (hsub x (List.mem_cons.mpr (Or.inr hx))) ?_
      intro hc
      cases hnd with
      | cons hhead _ =>
        have hxa : a ∈ t := by rw [← hc]; exact hx
        exact absurd rfl (hhead a hxa)
    have hnd' : t.Nodup := by cases hnd with | cons _ ht => exact ht
    have hIH : t.length ≤ (herase a tgt).length := ih (herase a tgt) hnd' hsub'
    simp only [List.length_cons]
    omega

/-! ### Nat mono machinery (house) -/

theorem hmul_le_right : ∀ (b c a : Nat), a ≤ b → c * a ≤ c * b := by
  intro b
  induction b with
  | zero =>
    intro c a h
    have ha : a = 0 := Nat.le_zero.mp h
    rw [ha, Nat.mul_zero]
  | succ b' ih =>
    intro c a h
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · rw [heq]
    · have hle : a ≤ b' := Nat.le_of_lt_succ hlt
      have hIH := ih c a hle
      rw [Nat.mul_succ]
      omega

theorem hmul_le (a b c d : Nat) (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d := by
  have e1 : a * c ≤ b * c := by
    rw [Nat.mul_comm a c, Nat.mul_comm b c]
    exact hmul_le_right b c a h1
  have e2 : b * c ≤ b * d := hmul_le_right d b c h2
  exact Nat.le_trans e1 e2

theorem hmul_lt_cancel_left (a b c : Nat) (hpos : 1 ≤ a) (h : a * b < a * c) : b < c := by
  rcases Nat.lt_trichotomy b c with hlt | heq | hgt
  · exact hlt
  · rw [heq] at h
    omega
  · have hle : a * c ≤ a * b := hmul_le a a c b (Nat.le_refl a) (Nat.le_of_lt hgt)
    omega

theorem hmul_lt (a b c : Nat) (hpos : 0 < a) (h : b < c) : a * b < a * c := by
  have hbc : b + 1 ≤ c := Nat.succ_le_of_lt h
  have h1 : a * (b + 1) ≤ a * c := hmul_le a a (b + 1) c (Nat.le_refl a) hbc
  have h2 : a * b + a = a * (b + 1) := by rw [Nat.mul_add, Nat.mul_one]
  have h3 : a * b < a * b + a := by
    have hstep := Nat.add_lt_add_left hpos (a * b)
    rw [Nat.add_zero] at hstep
    exact hstep
  rw [h2] at h3
  exact Nat.lt_of_lt_of_le h3 h1

theorem hmul_le_cancel_left (a b c : Nat) (hpos : 1 ≤ a) (h : a * b ≤ a * c) : b ≤ c := by
  rcases Nat.lt_trichotomy b c with hlt | heq | hgt
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq
  · exfalso
    have hlt2 : a * c < a * b := hmul_lt a c b (by omega) hgt
    omega

theorem hmul_pred_lt (k : Nat) (hk : 0 < k) : k * (k - 1) < k * k := by
  cases k with
  | zero => omega
  | succ j =>
    rw [Nat.succ_sub_one]
    exact hmul_lt (Nat.succ j) j (Nat.succ j) (by omega) (Nat.lt_succ_self j)

theorem hsq_pred_lt (k : Nat) (hk : 0 < k) : (k - 1) * (k - 1) < k * k := by
  cases k with
  | zero => omega
  | succ j =>
    rw [Nat.succ_sub_one]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0]; omega
    · have hstep1 : j * j < j * (Nat.succ j) := hmul_lt j j (Nat.succ j) hjpos (Nat.lt_succ_self j)
      have hstep2 : j * (Nat.succ j) ≤ (Nat.succ j) * (Nat.succ j) :=
        hmul_le j (Nat.succ j) (Nat.succ j) (Nat.succ j) (Nat.le_succ j) (Nat.le_refl _)
      exact Nat.lt_of_lt_of_le hstep1 hstep2

theorem length_pos_of_mem {α : Type} (a : α) : ∀ (l : List α), a ∈ l → 0 < l.length := by
  intro l
  cases l with
  | nil => intro h; exact absurd h (by simp)
  | cons b t =>
    intro _
    simp only [List.length_cons]
    omega

/-! ## §1 The house floor-sqrt -/

/-- ⌊√n⌋ by increment-on-squares. -/
def fsqrt : Nat → Nat
  | 0 => 0
  | n + 1 => if (fsqrt n + 1) * (fsqrt n + 1) ≤ n + 1 then fsqrt n + 1 else fsqrt n

theorem sq_succ (k : Nat) : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem fsqrt_sq_le : ∀ n : Nat, fsqrt n * fsqrt n ≤ n := by
  intro n
  induction n with
  | zero => simp [fsqrt]
  | succ m ih =>
    unfold fsqrt
    by_cases hstep : (fsqrt m + 1) * (fsqrt m + 1) ≤ m + 1
    · rw [if_pos hstep]
      have h1 : (fsqrt m + 1) * (fsqrt m + 1) = fsqrt m * fsqrt m + 2 * fsqrt m + 1 :=
        sq_succ (fsqrt m)
      omega
    · rw [if_neg hstep]
      omega

theorem fsqrt_lt_succ : ∀ n : Nat, n < (fsqrt n + 1) * (fsqrt n + 1) := by
  intro n
  induction n with
  | zero => simp [fsqrt]
  | succ m ih =>
    unfold fsqrt
    by_cases hstep : (fsqrt m + 1) * (fsqrt m + 1) ≤ m + 1
    · rw [if_pos hstep]
      have h1 : (fsqrt m + 1 + 1) * (fsqrt m + 1 + 1) =
          (fsqrt m + 1) * (fsqrt m + 1) + 2 * (fsqrt m + 1) + 1 := by
        have h := sq_succ (fsqrt m + 1)
        omega
      omega
    · rw [if_neg hstep]
      omega

theorem hmul_ge (k : Nat) : k ≤ k * k := by
  cases k with
  | zero => omega
  | succ j =>
    rw [Nat.succ_mul]
    omega

theorem fsqrt_le_self (n : Nat) : fsqrt n ≤ n := by
  rcases Nat.eq_zero_or_pos (fsqrt n) with h0 | hp
  · omega
  · exact Nat.le_trans (hmul_ge (fsqrt n)) (fsqrt_sq_le n)

theorem fsqrt_eq (n k : Nat) (h1 : k * k ≤ n) (h2 : n < (k + 1) * (k + 1)) : fsqrt n = k := by
  have hlo : fsqrt n * fsqrt n ≤ n := fsqrt_sq_le n
  have hhi : n < (fsqrt n + 1) * (fsqrt n + 1) := fsqrt_lt_succ n
  rcases Nat.lt_or_ge (fsqrt n) k with hlt | hge
  · have hsucc : fsqrt n + 1 ≤ k := by omega
    have hsq : (fsqrt n + 1) * (fsqrt n + 1) ≤ k * k :=
      hmul_le (fsqrt n + 1) k (fsqrt n + 1) k hsucc hsucc
    omega
  · rcases Nat.lt_or_ge k (fsqrt n) with hlt2 | hge2
    · have hsucc2 : k + 1 ≤ fsqrt n := by omega
      have hsq2 : (k + 1) * (k + 1) ≤ fsqrt n * fsqrt n :=
        hmul_le (k + 1) (fsqrt n) (k + 1) (fsqrt n) hsucc2 hsucc2
      omega
    · exact Nat.le_antisymm hge2 hge

theorem fsqrt_pos_of_pos (n : Nat) (hn : 0 < n) : 0 < fsqrt n := by
  cases hf : fsqrt n with
  | zero =>
      have hhi : n < (fsqrt n + 1) * (fsqrt n + 1) := fsqrt_lt_succ n
      rw [hf] at hhi
      have h1 : (0 + 1) * (0 + 1) = 1 := by omega
      omega
  | succ j => omega

/-! ## §2 The graph representation -/

variable {α : Type} [DecidableEq α]

/-- Clique on a vertex list. -/
def CliqueOn (adj : α → α → Bool) (S : List α) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → adj i j = true

/-- Independent set on a vertex list. -/
def IndepOn (adj : α → α → Bool) (S : List α) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → adj i j = false

/-- K1-free: no vertices at all. -/
def K1FreeOn (adj : α → α → Bool) (vs : List α) : Prop := ∀ v ∈ vs, False

/-- K2-free: no edge. -/
def K2FreeOn (adj : α → α → Bool) (vs : List α) : Prop :=
  ∀ i ∈ vs, ∀ j ∈ vs, i ≠ j → adj i j = false

/-- K̄2-free: no non-edge (complete). -/
def Kb2FreeOn (adj : α → α → Bool) (vs : List α) : Prop :=
  ∀ i ∈ vs, ∀ j ∈ vs, i ≠ j → adj i j = true

/-- K3-free: no triangle. -/
def K3FreeOn (adj : α → α → Bool) (vs : List α) : Prop :=
  ∀ i ∈ vs, ∀ j ∈ vs, ∀ k ∈ vs,
    i ≠ j → j ≠ k → i ≠ k → ¬ (adj i j = true ∧ adj j k = true ∧ adj i k = true)

/-- K̄3-free: no independent triple. -/
def Kb3FreeOn (adj : α → α → Bool) (vs : List α) : Prop :=
  ∀ i ∈ vs, ∀ j ∈ vs, ∀ k ∈ vs,
    i ≠ j → j ≠ k → i ≠ k → ¬ (adj i j = false ∧ adj j k = false ∧ adj i k = false)

/-- P3-free: no induced path a-b-c. -/
def P3FreeOn (adj : α → α → Bool) (vs : List α) : Prop :=
  ∀ i ∈ vs, ∀ j ∈ vs, ∀ k ∈ vs,
    i ≠ j → j ≠ k → i ≠ k → ¬ (adj i j = true ∧ adj j k = true ∧ adj i k = false)

/-- P̄3-free: no induced K1 ∪ K2. -/
def Pb3FreeOn (adj : α → α → Bool) (vs : List α) : Prop :=
  ∀ i ∈ vs, ∀ j ∈ vs, ∀ k ∈ vs,
    i ≠ j → j ≠ k → i ≠ k → ¬ (adj i j = true ∧ adj j k = false ∧ adj i k = false)

/-- The closed neighborhood of v inside vs. -/
def cnb (adj : α → α → Bool) (v : α) (vs : List α) : List α :=
  v :: hfilt (fun u => adj v u) vs

theorem cnb_length (adj : α → α → Bool) (v : α) (vs : List α) :
    (cnb adj v vs).length = (hfilt (fun u => adj v u) vs).length + 1 := rfl

theorem cnb_nodup (adj : α → α → Bool) (hirr : ∀ i : α, adj i i = false) (v : α)
    (vs : List α) (hnd : vs.Nodup) : (cnb adj v vs).Nodup := by
  refine List.Pairwise.cons ?_ (hfilt_nodup (fun u => adj v u) vs hnd)
  intro b hb heq
  obtain ⟨_, hbadj⟩ := (mem_hfilt_iff (fun u => adj v u) vs b).mp hb
  rw [heq] at hbadj
  rw [hirr b] at hbadj
  exact Bool.noConfusion hbadj

theorem cnb_subset (adj : α → α → Bool) (v : α) (vs : List α) (hvin : v ∈ vs) :
    ∀ x ∈ cnb adj v vs, x ∈ vs := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · rw [h]; exact hvin
  · exact ((mem_hfilt_iff (fun u => adj v u) vs x).mp h).1

theorem mem_cnb_tail {adj : α → α → Bool} {v : α} {vs : List α} {u : α}
    (h : u ∈ hfilt (fun u => adj v u) vs) : u ∈ cnb adj v vs :=
  List.mem_cons.mpr (Or.inr h)

/-- The bound certificate. -/
def BoundCert (adj : α → α → Bool) (vs : List α) : Prop :=
  ∃ S : List α, S.Nodup ∧ (∀ s ∈ S, s ∈ vs) ∧
    fsqrt vs.length ≤ S.length ∧ (CliqueOn adj S ∨ IndepOn adj S)

theorem boundCert_nil (adj : α → α → Bool) (hzero : fsqrt 0 = 0) :
    BoundCert adj [] := by
  use []
  refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
  · intro s hs
    exact absurd hs (by simp)
  · rw [show ([] : List α).length = 0 from rfl, hzero]
  · exact Or.inr (by intro i hi j _ _; exact absurd hi (by simp))

/-! ## §3 The unified greedy engine -/

private def removedOf (adj : α → α → Bool) (a : α) (vs : List α) : List α :=
  hfilt (fun u => !(memB u (cnb adj a vs))) vs

private def keptOf (adj : α → α → Bool) (a : α) (vs : List α) : List α :=
  hfilt (fun u => memB u (cnb adj a vs)) vs

theorem removed_kept_split (adj : α → α → Bool) (a : α) (vs : List α) (hnd : vs.Nodup) :
    (keptOf adj a vs).length + (removedOf adj a vs).length = vs.length := by
  have h := hfilt_length_split (fun u => memB u (cnb adj a vs)) vs hnd
  exact h

theorem keptOf_head (adj : α → α → Bool) (a : α) (vs : List α) (hvin : a ∈ vs) :
    a ∈ keptOf adj a vs := by
  refine (mem_hfilt_iff (fun u => memB u (cnb adj a vs)) vs a).mpr ⟨hvin, ?_⟩
  unfold cnb
  exact memB_cons_self a a (hfilt (fun u => adj a u) vs) rfl

theorem removedOf_nodup (adj : α → α → Bool) (a : α) (vs : List α) (hnd : vs.Nodup) :
    (removedOf adj a vs).Nodup :=
  hfilt_nodup (fun u => !(memB u (cnb adj a vs))) vs hnd

theorem removedOf_subset (adj : α → α → Bool) (a : α) (vs : List α) :
    ∀ x ∈ removedOf adj a vs, x ∈ vs :=
  hfilt_subset (fun u => !(memB u (cnb adj a vs))) vs

theorem removedOf_avoids (adj : α → α → Bool) (a : α) (vs : List α) :
    ∀ u ∈ removedOf adj a vs, u ≠ a ∧ adj a u = false := by
  intro u hu
  have hmem := (mem_hfilt_iff (fun u => !(memB u (cnb adj a vs))) vs u).mp hu
  have hnb : memB u (cnb adj a vs) = false := by
    cases hb : memB u (cnb adj a vs) with
    | false => rfl
    | true =>
      rw [hb] at hmem
      simp at hmem
  have hna : u ≠ a := by
    intro heq
    have hmemB : memB u (cnb adj a vs) = true := by
      rw [heq]
      unfold cnb
      exact memB_cons_self a a (hfilt (fun u => adj a u) vs) rfl
    rw [hmemB] at hnb
    exact Bool.noConfusion hnb
  have hna' : adj a u = false := by
    cases hau : adj a u with
    | false => rfl
    | true =>
      have huN : u ∈ hfilt (fun u => adj a u) vs :=
        (mem_hfilt_iff (fun u => adj a u) vs u).mpr ⟨hmem.1, hau⟩
      have huR : memB u (cnb adj a vs) = true :=
        (memB_iff u (cnb adj a vs)).mpr (mem_cnb_tail (vs := vs) huN)
      rw [huR] at hnb
      exact Bool.noConfusion hnb
  exact ⟨hna, hna'⟩

theorem closedNbhd_greedy (adj : α → α → Bool)
    (hsym : ∀ i j : α, adj i j = adj j i)
    (hirr : ∀ i : α, adj i i = false) :
    ∀ (fuel D : Nat) (vs : List α), vs.length ≤ fuel → vs.Nodup →
    (∀ v ∈ vs, (cnb adj v vs).length ≤ D) →
    ∃ S : List α, S.Nodup ∧ IndepOn adj S ∧ (∀ s ∈ S, s ∈ vs) ∧
      D * S.length ≥ vs.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro D vs hlen hnd _
    cases vs with
    | nil =>
      use []
      refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
      · intro i hi j _ _; exact absurd hi (by simp)
      · intro s hs; exact absurd hs (by simp)
      · simp only [List.length_nil]; omega
    | cons a t => exact absurd hlen (by simp)
  | succ f ih =>
    intro D vs hlen hnd hdeg
    cases vs with
    | nil =>
      use []
      refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
      · intro i hi j _ _; exact absurd hi (by simp)
      · intro s hs; exact absurd hs (by simp)
      · simp only [List.length_nil]; omega
    | cons a t =>
      have ha : a ∈ a :: t := List.mem_cons.mpr (Or.inl rfl)
      have hdeg_a : (cnb adj a (a :: t)).length ≤ D := hdeg a ha
      -- recursion on the removed set
      have hlenshort : (removedOf adj a (a :: t)).length + 1 ≤ (a :: t).length := by
        have hsplit : (keptOf adj a (a :: t)).length + (removedOf adj a (a :: t)).length
            = (a :: t).length := removed_kept_split adj a (a :: t) hnd
        have hkeep : a ∈ keptOf adj a (a :: t) :=
          keptOf_head adj a (a :: t) (List.mem_cons.mpr (Or.inl rfl))
        have hpos : 0 < (keptOf adj a (a :: t)).length := length_pos_of_mem a _ hkeep
        omega
      have hdeg' : ∀ v ∈ removedOf adj a (a :: t),
          (cnb adj v (removedOf adj a (a :: t))).length ≤ D := by
        intro v hv
        have hvmem : v ∈ a :: t := removedOf_subset adj a (a :: t) v hv
        have hsub : ∀ x ∈ cnb adj v (removedOf adj a (a :: t)),
            x ∈ cnb adj v (a :: t) := by
          intro x hx
          rcases List.mem_cons.mp hx with h | h
          · exact List.mem_cons.mpr (Or.inl h)
          · obtain ⟨hc1, hc2⟩ :=
              (mem_hfilt_iff (fun u => adj v u) (removedOf adj a (a :: t)) x).mp h
            exact mem_cnb_tail (vs := a :: t)
              ((mem_hfilt_iff (fun u => adj v u) (a :: t) x).mpr
                ⟨removedOf_subset adj a (a :: t) x hc1, hc2⟩)
        have hNDsub : (cnb adj v (removedOf adj a (a :: t))).Nodup :=
          cnb_nodup adj hirr v _ (removedOf_nodup adj a (a :: t) hnd)
        have hNDfull : (cnb adj v (a :: t)).Nodup := cnb_nodup adj hirr v (a :: t) hnd
        have hord := subset_length_le
          (cnb adj v (removedOf adj a (a :: t))) (cnb adj v (a :: t)) hNDsub hsub
        have hdv : (cnb adj v (a :: t)).length ≤ D := hdeg v hvmem
        omega
      have hrec := ih D (removedOf adj a (a :: t)) (by omega)
        (removedOf_nodup adj a (a :: t) hnd) hdeg'
      obtain ⟨S', hND', hInd', hSub', hCount'⟩ := hrec
      use a :: S'
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine List.Pairwise.cons ?_ hND'
        intro s hs
        exact (removedOf_avoids adj a (a :: t) s (hSub' s hs)).1.symm
      · intro i hi j hj hne
        rcases List.mem_cons.mp hi with hia | hia
        · rcases List.mem_cons.mp hj with hja | hja
          · exact absurd (hia.trans hja.symm) hne
          · rw [hia]
            exact (removedOf_avoids adj a (a :: t) j (hSub' j hja)).2
        · rcases List.mem_cons.mp hj with hja | hja
          · have hfalse : adj a i = false :=
              (removedOf_avoids adj a (a :: t) i (hSub' i hia)).2
            rw [hja]
            rw [hsym a i] at hfalse
            exact hfalse
          · exact hInd' i hia j hja hne
      · intro s hs
        rcases List.mem_cons.mp hs with h | h
        · exact List.mem_cons.mpr (Or.inl h)
        · have hsm : s ∈ a :: t := removedOf_subset adj a (a :: t) s (hSub' s h)
          rcases List.mem_cons.mp hsm with h' | h'
          · exact absurd h' ((removedOf_avoids adj a (a :: t) s (hSub' s h)).1)
          · exact List.mem_cons.mpr (Or.inr h')
      · -- D * (1 + |S'|) ≥ |N[a]| + |removed| ≥ (a::t).length
        have hpart : (a :: t).length ≤ (cnb adj a (a :: t)).length +
            (removedOf adj a (a :: t)).length := by
          have hsub : ∀ x ∈ a :: t, x ∈ (cnb adj a (a :: t)) ++ (removedOf adj a (a :: t)) := by
            intro x hx
            rw [List.mem_append]
            by_cases hxa : x = a
            · subst hxa
              exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
            · have hxt : x ∈ t := by
                rcases List.mem_cons.mp hx with h | h
                · exact absurd h hxa
                · exact h
              cases hadj : adj a x with
              | true =>
                exact Or.inl (mem_cnb_tail
                  ((mem_hfilt_iff (fun u => adj a u) (a :: t) x).mpr ⟨hx, hadj⟩))
              | false =>
                have hxnb : memB x (cnb adj a (a :: t)) = false := by
                  refine memB_false_of_nmem x (cnb adj a (a :: t)) ?_
                  intro hmem
                  rcases List.mem_cons.mp hmem with h1 | h1
                  · exact hxa h1
                  · have hcontra := ((mem_hfilt_iff (fun u => adj a u) (a :: t) x).mp h1).2
                    rw [hadj] at hcontra
                    exact Bool.noConfusion hcontra
                exact Or.inr ((mem_hfilt_iff
                  (fun u => !(memB u (cnb adj a (a :: t)))) (a :: t) x).mpr
                  ⟨hx, by rw [hxnb]; rfl⟩)
          have hord := subset_length_le (a :: t)
            ((cnb adj a (a :: t)) ++ (removedOf adj a (a :: t))) hnd hsub
          rw [length_app] at hord
          omega
        have hprod : D * (S'.length + 1) = D * S'.length + D := by
          rw [Nat.mul_add, Nat.mul_one]
        simp only [List.length_cons] at hpart ⊢
        rw [hprod]
        have hA : D * S'.length + D ≥ (removedOf adj a (a :: t)).length + D :=
          Nat.add_le_add hCount' (Nat.le_refl D)
        have hB : (removedOf adj a (a :: t)).length + D ≥
            (removedOf adj a (a :: t)).length + (cnb adj a (a :: t)).length :=
          Nat.add_le_add (Nat.le_refl _) hdeg_a
        omega

/-! ## §4 The degree law, the cluster law, the trivial family -/

theorem k3_bound (adj : α → α → Bool)
    (hsym : ∀ i j : α, adj i j = adj j i)
    (hirr : ∀ i : α, adj i i = false) :
    ∀ (vs : List α), vs.Nodup → K3FreeOn adj vs → BoundCert adj vs := by
  intro vs hnd hfree
  rcases Nat.eq_zero_or_pos (fsqrt vs.length) with hk0 | hkpos
  · -- k = 0: the empty certificate
    use []
    refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
    · intro s hs; exact absurd hs (by simp)
    · rw [show ([] : List α).length = 0 from rfl, hk0]
    · exact Or.inr (by intro i hi j _ _; exact absurd hi (by simp))
  · -- k ≥ 1
    have hk2 : fsqrt vs.length * fsqrt vs.length ≤ vs.length := fsqrt_sq_le vs.length
    rcases Classical.em (∃ v ∈ vs, fsqrt vs.length ≤ (hfilt (fun u => adj v u) vs).length)
      with hex | hall
    · obtain ⟨v, hv, hvl⟩ := hex
      use hfilt (fun u => adj v u) vs
      refine ⟨hfilt_nodup (fun u => adj v u) vs hnd, hfilt_subset (fun u => adj v u) vs,
        hvl, ?_⟩
      refine Or.inr ?_
      intro i hi j hj hne
      have hmi := (mem_hfilt_iff (fun u => adj v u) vs i).mp hi
      have hmj := (mem_hfilt_iff (fun u => adj v u) vs j).mp hj
      have hiv : i ≠ v := by
        intro heq
        rw [heq] at hmi
        rw [hirr v] at hmi
        exact Bool.noConfusion hmi.2
      have hvj : v ≠ j := by
        intro heq
        rw [heq] at hmj
        rw [hirr j] at hmj
        exact Bool.noConfusion hmj.2
      have htri := hfree i hmi.1 v hv j hmj.1 hiv hvj hne
      have hiva : adj i v = true := by rw [hsym i v]; exact hmi.2
      have hvja : adj v j = true := hmj.2
      cases hbl : adj i j with
      | true => exact absurd ⟨hiva, hvja, hbl⟩ htri
      | false => rfl
    · -- all open neighborhoods ≤ k − 1, so closed ≤ k: the greedy engine
      have hdeg : ∀ v ∈ vs, (cnb adj v vs).length ≤ fsqrt vs.length := by
        intro v hv
        have hnot : ¬ (fsqrt vs.length ≤ (hfilt (fun u => adj v u) vs).length) := by
          intro hle
          exact hall ⟨v, hv, hle⟩
        rw [cnb_length]
        omega
      obtain ⟨S, hND, hInd, hSub, hCount⟩ :=
        closedNbhd_greedy adj hsym hirr (vs.length) (fsqrt vs.length) vs
          (Nat.le_refl _) hnd hdeg
      use S
      refine ⟨hND, hSub, ?_, Or.inr hInd⟩
      rcases Nat.lt_or_ge S.length (fsqrt vs.length) with hlt | hge
      · exfalso
        have hkle : S.length ≤ fsqrt vs.length - 1 := by omega
        have hmono : fsqrt vs.length * S.length ≤
            fsqrt vs.length * (fsqrt vs.length - 1) :=
          hmul_le (fsqrt vs.length) (fsqrt vs.length) S.length
            (fsqrt vs.length - 1) (Nat.le_refl _) hkle
        have hsq : fsqrt vs.length * (fsqrt vs.length - 1) <
            fsqrt vs.length * fsqrt vs.length :=
          hmul_pred_lt (fsqrt vs.length) hkpos
        have hchain : fsqrt vs.length * S.length < vs.length := by omega
        exact absurd hchain (Nat.not_lt.mpr hCount)
      · exact hge


/-! ## §5 The cluster law (P3-free) -/

theorem p3_bound (adj : α → α → Bool)
    (hsym : ∀ i j : α, adj i j = adj j i)
    (hirr : ∀ i : α, adj i i = false) :
    ∀ (vs : List α), vs.Nodup → P3FreeOn adj vs → BoundCert adj vs := by
  intro vs hnd hfree
  rcases Nat.eq_zero_or_pos (fsqrt vs.length) with hk0 | hkpos
  · use []
    refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
    · intro s hs; exact absurd hs (by simp)
    · have hlen0 : vs.length = 0 := by
        have hhi := fsqrt_lt_succ vs.length
        rw [hk0] at hhi
        omega
      cases vs with
      | nil => rw [show ([] : List α).length = 0 from rfl, show fsqrt 0 = 0 from rfl]
      | cons a t => simp only [List.length_cons] at hlen0; omega
    · exact Or.inr (by intro i hi j _ _; exact absurd hi (by simp))
  · have hk2 : fsqrt vs.length * fsqrt vs.length ≤ vs.length := fsqrt_sq_le vs.length
    rcases Classical.em (∃ v ∈ vs, fsqrt vs.length ≤ (cnb adj v vs).length)
      with hex | hall
    · obtain ⟨v, hv, hvl⟩ := hex
      use cnb adj v vs
      refine ⟨cnb_nodup adj hirr v vs hnd, cnb_subset adj v vs hv, hvl, ?_⟩
      refine Or.inl ?_
      intro i hi j hj hne
      rcases List.mem_cons.mp hi with hiv | hit
      · rcases List.mem_cons.mp hj with hjv | hjt
        · exact absurd (hiv.trans hjv.symm) hne
        · rw [hiv]
          exact (mem_hfilt_iff (fun u => adj v u) vs j).mp hjt |>.2
      · rcases List.mem_cons.mp hj with hjv | hjt
        · rw [hjv, hsym i v]
          exact (mem_hfilt_iff (fun u => adj v u) vs i).mp hit |>.2
        · -- both neighbors of v: P3-freeness forces adjacency
          have hmi := (mem_hfilt_iff (fun u => adj v u) vs i).mp hit
          have hmj := (mem_hfilt_iff (fun u => adj v u) vs j).mp hjt
          have hivn : i ≠ v := by
            intro heq
            rw [heq] at hmi
            rw [hirr v] at hmi
            exact Bool.noConfusion hmi.2
          have hvjn : v ≠ j := by
            intro heq
            rw [heq] at hmj
            rw [hirr j] at hmj
            exact Bool.noConfusion hmj.2
          have htri := hfree i hmi.1 v hv j hmj.1 hivn hvjn hne
          have hiva : adj i v = true := by rw [hsym i v]; exact hmi.2
          have hvja : adj v j = true := hmj.2
          cases hbl : adj i j with
          | true => rfl
          | false => exact absurd ⟨hiva, hvja, hbl⟩ htri
    · -- all closed neighborhoods ≤ k − 1: the greedy engine with D = k − 1
      have hdeg : ∀ v ∈ vs, (cnb adj v vs).length ≤ fsqrt vs.length - 1 := by
        intro v hv
        have hnot : ¬ (fsqrt vs.length ≤ (cnb adj v vs).length) :=
          fun hle => hall ⟨v, hv, hle⟩
        omega
      obtain ⟨S, hND, hInd, hSub, hCount⟩ :=
        closedNbhd_greedy adj hsym hirr (vs.length) (fsqrt vs.length - 1) vs
          (Nat.le_refl _) hnd hdeg
      use S
      refine ⟨hND, hSub, ?_, Or.inr hInd⟩
      rcases Nat.lt_or_ge S.length (fsqrt vs.length) with hlt | hge
      · exfalso
        have hkle : S.length ≤ fsqrt vs.length - 1 := by omega
        have hmono : (fsqrt vs.length - 1) * S.length ≤
            (fsqrt vs.length - 1) * (fsqrt vs.length - 1) :=
          hmul_le (fsqrt vs.length - 1) (fsqrt vs.length - 1) S.length
            (fsqrt vs.length - 1) (Nat.le_refl _) hkle
        have hsq : (fsqrt vs.length - 1) * (fsqrt vs.length - 1) <
            fsqrt vs.length * fsqrt vs.length :=
          hsq_pred_lt (fsqrt vs.length) hkpos
        have hchain : (fsqrt vs.length - 1) * S.length < vs.length := by omega
        exact absurd hchain (Nat.not_lt.mpr hCount)
      · exact hge


/-! ## §6 The trivial family -/

theorem k1_bound (adj : α → α → Bool) :
    ∀ (vs : List α), vs.Nodup → K1FreeOn adj vs → BoundCert adj vs := by
  intro vs hnd hfree
  have hnil : vs = [] := by
    cases vs with
    | nil => rfl
    | cons a t => exact absurd (hfree a (List.mem_cons.mpr (Or.inl rfl))) (fun h => h)
  subst hnil
  use []
  refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
  · intro s hs; exact absurd hs (by simp)
  · rw [show ([] : List α).length = 0 from rfl, show fsqrt 0 = 0 from rfl]
  · exact Or.inr (by intro i hi j _ _; exact absurd hi (by simp))

theorem k2_bound (adj : α → α → Bool) :
    ∀ (vs : List α), vs.Nodup → K2FreeOn adj vs → BoundCert adj vs := by
  intro vs hnd hfree
  use vs
  refine ⟨hnd, ?_, fsqrt_le_self vs.length, Or.inr ?_⟩
  · intro s hs; exact hs
  · intro i hi j hj hne
    exact hfree i hi j hj hne

theorem kb2_bound (adj : α → α → Bool) :
    ∀ (vs : List α), vs.Nodup → Kb2FreeOn adj vs → BoundCert adj vs := by
  intro vs hnd hfree
  use vs
  refine ⟨hnd, ?_, fsqrt_le_self vs.length, Or.inl ?_⟩
  · intro s hs; exact hs
  · intro i hi j hj hne
    exact hfree i hi j hj hne

/-! ## §7 The complement transfers -/

def cadj (adj : α → α → Bool) (i j : α) : Bool :=
  if i = j then false else !(adj i j)

theorem cadj_symm (adj : α → α → Bool) (hsym : ∀ i j : α, adj i j = adj j i) :
    ∀ i j : α, cadj adj i j = cadj adj j i := by
  intro i j
  unfold cadj
  by_cases h : i = j
  · rw [if_pos h, if_pos (h.symm)]
  · rw [if_neg h, if_neg (fun hc => h hc.symm), hsym i j]

theorem cadj_irr (adj : α → α → Bool) (i : α) : cadj adj i i = false := by
  unfold cadj
  rw [if_pos rfl]

theorem cadj_true_iff_false {adj : α → α → Bool} {i j : α} (hne : i ≠ j) :
    cadj adj i j = true ↔ adj i j = false := by
  unfold cadj
  rw [if_neg hne]
  constructor
  · intro h
    cases hb : adj i j with
    | false => rfl
    | true => rw [hb] at h; simp at h
  · intro h
    rw [h]
    rfl

theorem cadj_false_iff_true {adj : α → α → Bool} {i j : α} (hne : i ≠ j) :
    cadj adj i j = false ↔ adj i j = true := by
  unfold cadj
  rw [if_neg hne]
  constructor
  · intro h
    cases hb : adj i j with
    | true => rfl
    | false => rw [hb] at h; simp at h
  · intro h
    rw [h]
    rfl

theorem kb3Free_iff_k3Free_comp (adj : α → α → Bool) (vs : List α) :
    Kb3FreeOn adj vs ↔ K3FreeOn (cadj adj) vs := by
  constructor
  · intro hkb3
    intro i hi j hj k hk' h1 h2 h3 htriple
    have h1' : i ≠ j := h1
    have h2' : j ≠ k := h2
    have h3' : i ≠ k := h3
    obtain ⟨hc1, hc2, hc3⟩ := htriple
    have ha1 : adj i j = false := (cadj_true_iff_false h1').mp hc1
    have ha2 : adj j k = false := (cadj_true_iff_false h2').mp hc2
    have ha3 : adj i k = false := (cadj_true_iff_false h3').mp hc3
    exact hkb3 i hi j hj k hk' h1 h2 h3 ⟨ha1, ha2, ha3⟩
  · intro hk3
    intro i hi j hj k hk' h1 h2 h3 htriple
    obtain ⟨hc1, hc2, hc3⟩ := htriple
    have ha1 : cadj adj i j = true := (cadj_true_iff_false h1).mpr hc1
    have ha2 : cadj adj j k = true := (cadj_true_iff_false h2).mpr hc2
    have ha3 : cadj adj i k = true := (cadj_true_iff_false h3).mpr hc3
    exact hk3 i hi j hj k hk' h1 h2 h3 ⟨ha1, ha2, ha3⟩

theorem pb3Free_iff_p3Free_comp (adj : α → α → Bool) (hsym : ∀ i j : α, adj i j = adj j i)
    (vs : List α) :
    Pb3FreeOn adj vs ↔ P3FreeOn (cadj adj) vs := by
  constructor
  · intro hpb3
    intro i hi j hj k hk' h1 h2 h3 htriple
    obtain ⟨hc1, hc2, hc3⟩ := htriple
    have ha1 : adj i j = false := (cadj_true_iff_false h1).mp hc1
    have ha2 : adj j k = false := (cadj_true_iff_false h2).mp hc2
    have ha3 : adj i k = true := (cadj_false_iff_true h3).mp hc3
    -- the complement pattern (ij non, jk non, ik edge) IS Pb3 (edge + two non-edges)
    have hak : adj k i = true := by rw [← hsym i k]; exact ha3
    have hkj : adj k j = false := by rw [← hsym j k]; exact ha2
    exact hpb3 k hk' i hi j hj
      (fun hc => h3 hc.symm) h1 (fun hc => h2 hc.symm) ⟨hak, ha1, hkj⟩
  · intro hp3
    intro i hi j hj k hk' h1 h2 h3 htriple
    obtain ⟨hc1, hc2, hc3⟩ := htriple
    -- Pb3 pattern on adj: (adj i j = true, adj j k = false, adj i k = false);
    -- convert to the P3 pattern on cadj at (j,k,i): cadj j k = T, cadj k i = T, cadj j i = F
    have hkic : adj k i = false := by rw [← hsym i k]; exact hc3
    have hjir : adj j i = true := by rw [← hsym i j]; exact hc1
    exact hp3 j hj k hk' i hi h2 (fun hc => h3 hc.symm) (fun hc => h1 hc.symm)
      ⟨(cadj_true_iff_false h2).mpr hc2,
       (cadj_true_iff_false (fun hc => h3 hc.symm)).mpr hkic,
       (cadj_false_iff_true (fun hc => h1 hc.symm)).mpr hjir⟩

theorem clique_cadj_iff_indep (adj : α → α → Bool) (S : List α) :
    CliqueOn (cadj adj) S ↔ IndepOn adj S := by
  constructor
  · intro hC i hi j hj hne
    have htrue : cadj adj i j = true := hC i hi j hj hne
    exact (cadj_true_iff_false hne).mp htrue
  · intro hI i hi j hj hne
    have hfalse : adj i j = false := hI i hi j hj hne
    exact (cadj_true_iff_false hne).mpr hfalse

theorem indep_cadj_iff_clique (adj : α → α → Bool) (S : List α) :
    IndepOn (cadj adj) S ↔ CliqueOn adj S := by
  constructor
  · intro hI i hi j hj hne
    have hfalse : cadj adj i j = false := hI i hi j hj hne
    exact (cadj_false_iff_true hne).mp hfalse
  · intro hC i hi j hj hne
    have htrue : adj i j = true := hC i hi j hj hne
    exact (cadj_false_iff_true hne).mpr htrue

theorem boundCert_comp_transfer (adj : α → α → Bool) (vs : List α) :
    BoundCert (cadj adj) vs → BoundCert adj vs := by
  intro hcert
  obtain ⟨S, hND, hSub, hlen, hdisj⟩ := hcert
  use S
  rcases hdisj with hC | hI
  · exact ⟨hND, hSub, hlen, Or.inr ((clique_cadj_iff_indep adj S).mp hC)⟩
  · exact ⟨hND, hSub, hlen, Or.inl ((indep_cadj_iff_clique adj S).mp hI)⟩

theorem kb3_bound (adj : α → α → Bool)
    (hsym : ∀ i j : α, adj i j = adj j i)
    (hirr : ∀ i : α, adj i i = false) :
    ∀ (vs : List α), vs.Nodup → Kb3FreeOn adj vs → BoundCert adj vs := by
  intro vs hnd hfree
  have hcomp : K3FreeOn (cadj adj) vs := (kb3Free_iff_k3Free_comp adj vs).mp hfree
  have hcert : BoundCert (cadj adj) vs :=
    k3_bound (cadj adj) (cadj_symm adj hsym) (cadj_irr adj) vs hnd hcomp
  exact boundCert_comp_transfer adj vs hcert

theorem pb3_bound (adj : α → α → Bool)
    (hsym : ∀ i j : α, adj i j = adj j i)
    (hirr : ∀ i : α, adj i i = false) :
    ∀ (vs : List α), vs.Nodup → Pb3FreeOn adj vs → BoundCert adj vs := by
  intro vs hnd hfree
  have hcomp : P3FreeOn (cadj adj) vs := (pb3Free_iff_p3Free_comp adj hsym vs).mp hfree
  have hcert : BoundCert (cadj adj) vs :=
    p3_bound (cadj adj) (cadj_symm adj hsym) (cadj_irr adj) vs hnd hcomp
  exact boundCert_comp_transfer adj vs hcert

/-! ## §8 The tightness witness (the c = 1/2 exponent is OPTIMAL) -/

theorem eqb_comm {α : Type} [DecidableEq α] (a b : α) : eqb a b = eqb b a := by
  by_cases hab : a = b
  · rw [hab, eqb_refl]
  · have hba : b ≠ a := fun hc => hab (hc.symm)
    have h1 : eqb a b = false := (eqb_false_iff a b).mpr hab
    have h2 : eqb b a = false := (eqb_false_iff b a).mpr hba
    rw [h1, h2]

theorem eqb_true_iff {α : Type} [DecidableEq α] (a b : α) : eqb a b = true ↔ a = b := by
  constructor
  · exact eq_of_eqb_true a b
  · intro h
    rw [h]
    exact eqb_refl b

/-- The same-block cluster adjacency: a, b adjacent iff same m-block. -/
def adjT (m : Nat) (a b : Nat) : Bool := eqb (a / m) (b / m)

theorem adjT_symm (m a b : Nat) : adjT m a b = adjT m b a := by
  unfold adjT
  exact eqb_comm (a / m) (b / m)

theorem adjT_irr (m a : Nat) : adjT m a a = true := by
  unfold adjT
  exact eqb_refl (a / m)

theorem adjT_true (m a b : Nat) (h : adjT m a b = true) : a / m = b / m :=
  eq_of_eqb_true (a / m) (b / m) h

theorem adjT_false (m a b : Nat) (h : adjT m a b = false) : a / m ≠ b / m :=
  ne_of_eqb_false (a / m) (b / m) h

theorem div_add_mod_self (s m : Nat) : m * (s / m) + s % m = s :=
  Nat.div_add_mod s m

theorem same_block_mod_ne (s1 s2 m : Nat) (h : s1 / m = s2 / m) (hne : s1 ≠ s2) :
    s1 % m ≠ s2 % m := by
  intro hmod
  apply hne
  have h1 : m * (s1 / m) + s1 % m = s1 := div_add_mod_self s1 m
  have h2 : m * (s2 / m) + s2 % m = s2 := div_add_mod_self s2 m
  rw [h, hmod] at h1
  rw [h2] at h1
  exact h1.symm

theorem div_lt_of_lt_mul (s m : Nat) (hpos : 1 ≤ m) (h : s < m * m) : s / m < m := by
  have hrec : m * (s / m) + s % m = s := div_add_mod_self s m
  have hle1 : m * (s / m) ≤ s := by omega
  have hle : m * (s / m) < m * m := Nat.lt_of_le_of_lt hle1 h
  exact hmul_lt_cancel_left m (s / m) m hpos hle

theorem div_zero_of_lt (s m : Nat) (h : s < m) : s / m = 0 := by
  rcases Nat.eq_zero_or_pos (s / m) with h0 | hp
  · exact h0
  · exfalso
    have hrec : m * (s / m) + s % m = s := div_add_mod_self s m
    have hle1 : m * (s / m) ≤ s := by omega
    have hle2 : m ≤ m * (s / m) := by
      have h1 : 1 ≤ s / m := by omega
      calc m = m * 1 := (Nat.mul_one m).symm
        _ ≤ m * (s / m) := hmul_le_right (s / m) m 1 h1
    have hle3 : m ≤ s := Nat.le_trans hle2 hle1
    omega

theorem div_exact_mul (q m : Nat) (hpos : 1 ≤ m) : q * m / m = q := by
  have hrec : m * (q * m / m) + q * m % m = q * m := div_add_mod_self (q * m) m
  have hle : m * (q * m / m) ≤ q * m := by
    have h := Nat.le_add_right (m * (q * m / m)) (q * m % m)
    rw [hrec] at h
    exact h
  have hX : q * m / m ≤ q := by
    refine hmul_le_cancel_left m (q * m / m) q hpos ?_
    calc m * (q * m / m) ≤ q * m := hle
      _ = m * q := Nat.mul_comm q m
  rcases Nat.eq_or_lt_of_le hX with heq | hlt
  · exact heq
  · exfalso
    have hlt' : q * m / m < q := hlt
    have hle2 : (q * m / m) + 1 ≤ q := Nat.succ_le_of_lt hlt'
    have hle3 : m * ((q * m / m) + 1) ≤ m * q :=
      hmul_le m m ((q * m / m) + 1) q (Nat.le_refl m) hle2
    have hexp : m * ((q * m / m) + 1) = m * (q * m / m) + m := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [hexp] at hle3
    have hcomm : m * q = q * m := Nat.mul_comm m q
    have hle5 : m ≤ q * m % m := by omega
    have hmod : q * m % m < m := Nat.mod_lt (q * m) (by omega)
    omega

theorem hmul_inj (m a b : Nat) (hpos : 1 ≤ m) (h : m * a = m * b) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have hlt2 : m * a < m * b := hmul_lt m a b (by omega) hlt
    rw [h] at hlt2
    exact absurd hlt2 (Nat.lt_irrefl _)
  · exact heq
  · have hgt2 : m * b < m * a := hmul_lt m b a (by omega) hgt
    rw [h] at hgt2
    exact absurd hgt2 (Nat.lt_irrefl _)

theorem nodup_map_of_on : ∀ (S : List Nat) (f : Nat → Nat) (hND : S.Nodup),
    (∀ a b, a ∈ S → b ∈ S → f a = f b → a = b) → (S.map f).Nodup := by
  intro S
  induction S with
  | nil => intro f _ _; exact List.Pairwise.nil
  | cons a t ih =>
    intro f hND hinj
    rw [List.map_cons]
    refine List.Pairwise.cons ?_ ?_
    · intro b hb
      obtain ⟨c, hc, hfc⟩ := List.mem_map.mp hb
      intro hfab
      have hfc' : f a = f c := hfab.trans hfc.symm
      have heq : a = c := hinj a c (List.mem_cons.mpr (Or.inl rfl))
        (List.mem_cons.mpr (Or.inr hc)) hfc'
      cases hND with
      | cons hhead _ => exact hhead c hc heq
    · cases hND with
      | cons _ htail => exact ih f htail (fun x y hx hy hfx =>
          hinj x y (List.mem_cons.mpr (Or.inr hx)) (List.mem_cons.mpr (Or.inr hy)) hfx)

theorem tight_family (m : Nat) (hm : 1 ≤ m) :
    (List.range (m * m)).Nodup ∧ fsqrt (m * m) = m ∧
    (∀ S : List Nat, S.Nodup → (∀ s ∈ S, s ∈ List.range (m * m)) →
        CliqueOn (adjT m) S → S.length ≤ m) ∧
    (∀ T : List Nat, T.Nodup → (∀ t ∈ T, t ∈ List.range (m * m)) →
        IndepOn (adjT m) T → T.length ≤ m) ∧
    (∃ S : List Nat, S.Nodup ∧ (∀ s ∈ S, s ∈ List.range (m * m)) ∧
        S.length = m ∧ CliqueOn (adjT m) S) ∧
    (∃ T : List Nat, T.Nodup ∧ (∀ t ∈ T, t ∈ List.range (m * m)) ∧
        T.length = m ∧ IndepOn (adjT m) T) := by
  have hrangeND : (List.range (m * m)).Nodup := List.nodup_range (n := m * m)
  have hfsqrt : fsqrt (m * m) = m := by
    refine fsqrt_eq (m * m) m (Nat.le_refl _) ?_
    have h1 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := sq_succ m
    have h2 := Nat.add_lt_add_left (show 0 < 2 * m + 1 by omega) (m * m)
    rw [Nat.add_zero] at h2
    rw [h1]
    exact h2
  refine ⟨hrangeND, hfsqrt, ?_, ?_, ?_, ?_⟩
  · -- CLIQUE UPPER: the mod map is injective on a clique and bounded
    intro S hND hsub hC
    have hmem : ∀ s ∈ S, s < m * m := fun s hs => List.mem_range.mp (hsub s hs)
    have hNDmap : (S.map (fun s => s % m)).Nodup := by
      refine nodup_map_of_on S (fun s => s % m) hND ?_
      intro a b ha hb hmod
      by_cases hab : a = b
      · exact hab
      · exfalso
        have hsame : a / m = b / m := adjT_true m a b (hC a ha b hb hab)
        exact same_block_mod_ne a b m hsame hab hmod
    have hsubmap : ∀ x ∈ S.map (fun s => s % m), x ∈ List.range m := by
      intro x hx
      obtain ⟨s, hs, hfx⟩ := List.mem_map.mp hx
      have hfx' : s % m = x := hfx
      have hlt : s % m < m := Nat.mod_lt s (by omega)
      rw [← hfx']
      exact List.mem_range.mpr hlt
    have hord := subset_length_le (S.map (fun s => s % m)) (List.range m) hNDmap hsubmap
    have hlen : (S.map (fun s => s % m)).length = S.length := by simp
    have hrange : (List.range m).length = m := by simp
    omega
  · -- INDEP UPPER: the div map is injective on an independent set and bounded
    intro T hND hsub hI
    have hNDmap : (T.map (fun t => t / m)).Nodup := by
      refine nodup_map_of_on T (fun t => t / m) hND ?_
      intro a b ha hb hdiv
      by_cases hab : a = b
      · exact hab
      · exfalso
        have htrue : adjT m a b = true := by
          unfold adjT
          rw [hdiv]
          exact eqb_refl (b / m)
        have hfalse : adjT m a b = false := hI a ha b hb hab
        rw [hfalse] at htrue
        exact Bool.noConfusion htrue
    have hsubmap : ∀ x ∈ T.map (fun t => t / m), x ∈ List.range m := by
      intro x hx
      obtain ⟨t, ht, hfxt⟩ := List.mem_map.mp hx
      have hfxt' : t / m = x := hfxt
      have hmemT : t < m * m := List.mem_range.mp (hsub t ht)
      have hlt : t / m < m := div_lt_of_lt_mul t m hm hmemT
      rw [← hfxt']
      exact List.mem_range.mpr hlt
    have hord := subset_length_le (T.map (fun t => t / m)) (List.range m) hNDmap hsubmap
    have hlen : (T.map (fun t => t / m)).length = T.length := by simp
    have hrange : (List.range m).length = m := by simp
    omega
  · -- CLIQUE WITNESS: range m (the whole block 0)
    refine ⟨List.range m, List.nodup_range (n := m), ?_, ?_, ?_⟩
    · intro s hs
      have hlt : s < m := List.mem_range.mp hs
      have hle : m ≤ m * m := by
        have h9 := hmul_le m m 1 m (Nat.le_refl m) hm
        simpa using h9
      exact List.mem_range.mpr (Nat.lt_of_lt_of_le hlt hle)
    · have h1 : (List.range m).length = m := by simp
      exact h1
    · intro i hi j hj _
      have hi' : i < m := List.mem_range.mp hi
      have hj' : j < m := List.mem_range.mp hj
      have hdivi : i / m = 0 := div_zero_of_lt i m hi'
      have hdivj : j / m = 0 := div_zero_of_lt j m hj'
      unfold adjT
      rw [hdivi, hdivj]
      exact eqb_refl 0
  · -- INDEP WITNESS: the block representatives q * m
    refine ⟨(List.range m).map (fun q => q * m), ?_, ?_, ?_, ?_⟩
    · exact nodup_map_of_on (List.range m) (fun q => q * m) (List.nodup_range (n := m))
        (fun a b ha hb hf =>
          hmul_inj m a b hm (by rw [Nat.mul_comm m a, Nat.mul_comm m b]; exact hf))
    · intro t ht
      obtain ⟨q, hq, hfx⟩ := List.mem_map.mp ht
      have hq' : q < m := List.mem_range.mp hq
      have hlt : q * m < m * m := by
        have hstep : m * q < m * m := hmul_lt m q m (by omega) hq'
        rw [Nat.mul_comm q m]
        exact hstep
      rw [← hfx]
      exact List.mem_range.mpr hlt
    · have h1 : ((List.range m).map (fun q => q * m)).length = (List.range m).length := by
        simp
      have h2 : (List.range m).length = m := by simp
      omega
    · intro i hi j hj hne
      -- distinct block representatives have distinct block indices
      obtain ⟨q1, hq1, hf1⟩ := List.mem_map.mp hi
      obtain ⟨q2, hq2, hf2⟩ := List.mem_map.mp hj
      have hneq : q1 ≠ q2 := by
        intro heq
        apply hne
        rw [← hf1, ← hf2, heq]
      have h1 : q1 * m / m = q1 := div_exact_mul q1 m hm
      have h2 : q2 * m / m = q2 := div_exact_mul q2 m hm
      unfold adjT
      rw [← hf1, ← hf2, h1, h2]
      exact (eqb_false_iff q1 q2).mpr hneq

/-! ## §9 The Arsenal bridge and the board -/

theorem arsenal_bridge (j : Nat) : 0 < 2 ^ j ∧ 0 < 3 ^ j :=
  ⟨two_pow_pos j, three_pow_pos_lemma j⟩

theorem tight_family_arsenal (j : Nat) (hj : 1 ≤ j) :
    (List.range (2 ^ j * 2 ^ j)).Nodup ∧ fsqrt (2 ^ j * 2 ^ j) = 2 ^ j ∧
    (∀ S : List Nat, S.Nodup → (∀ s ∈ S, s ∈ List.range (2 ^ j * 2 ^ j)) →
        CliqueOn (adjT (2 ^ j)) S → S.length ≤ 2 ^ j) ∧
    (∀ T : List Nat, T.Nodup → (∀ t ∈ T, t ∈ List.range (2 ^ j * 2 ^ j)) →
        IndepOn (adjT (2 ^ j)) T → T.length ≤ 2 ^ j) ∧
    (∃ S : List Nat, S.Nodup ∧ (∀ s ∈ S, s ∈ List.range (2 ^ j * 2 ^ j)) ∧
        S.length = 2 ^ j ∧ CliqueOn (adjT (2 ^ j)) S) ∧
    (∃ T : List Nat, T.Nodup ∧ (∀ t ∈ T, t ∈ List.range (2 ^ j * 2 ^ j)) ∧
        T.length = 2 ^ j ∧ IndepOn (adjT (2 ^ j)) T) :=
  tight_family (2 ^ j) (by
    have h := two_pow_pos j
    omega)

/-! ### W73 addendum: the tightness theorems, premise-free.

`tight_family` carried the domain bound `hm : 1 ≤ m` as a premise and
`tight_family_arsenal` carried `hj : 1 ≤ j` (vestigial — its proof term
only ever uses `two_pow_pos`, which holds for every `j`). Both are now
stated with ZERO premises: the m = 0 case of the first is proved directly
(the range is empty there), and the second is the identical proof term
with the premise dropped. -/

/-- THE DYADIC TIGHTNESS FAMILY, HYPOTHESIS-FREE (W73): `tight_family`
    with the `1 ≤ m` premise eliminated — the m = 0 degenerate case is
    proved directly (empty range, empty witnesses), m ≥ 1 by the original
    theorem. -/
theorem tight_family_uncond (m : Nat) :
    (List.range (m * m)).Nodup ∧ fsqrt (m * m) = m ∧
    (∀ S : List Nat, S.Nodup → (∀ s ∈ S, s ∈ List.range (m * m)) →
        CliqueOn (adjT m) S → S.length ≤ m) ∧
    (∀ T : List Nat, T.Nodup → (∀ t ∈ T, t ∈ List.range (m * m)) →
        IndepOn (adjT m) T → T.length ≤ m) ∧
    (∃ S : List Nat, S.Nodup ∧ (∀ s ∈ S, s ∈ List.range (m * m)) ∧
        S.length = m ∧ CliqueOn (adjT m) S) ∧
    (∃ T : List Nat, T.Nodup ∧ (∀ t ∈ T, t ∈ List.range (m * m)) ∧
        T.length = m ∧ IndepOn (adjT m) T) := by
  cases m with
  | zero =>
    refine ⟨List.nodup_range, rfl, ?_, ?_, ?_, ?_⟩
    · intro S _ hsub _
      cases S with
      | nil => exact Nat.le_refl 0
      | cons a t =>
          exact absurd (List.mem_range.mp (hsub a (List.mem_cons.mpr (Or.inl rfl))))
            (Nat.not_lt_zero a)
    · intro T _ hsub _
      cases T with
      | nil => exact Nat.le_refl 0
      | cons a t =>
          exact absurd (List.mem_range.mp (hsub a (List.mem_cons.mpr (Or.inl rfl))))
            (Nat.not_lt_zero a)
    · exact ⟨[], List.Pairwise.nil,
        fun s hs => (List.not_mem_nil hs).elim, rfl,
        fun i hi => (List.not_mem_nil hi).elim⟩
    · exact ⟨[], List.Pairwise.nil,
        fun s hs => (List.not_mem_nil hs).elim, rfl,
        fun i hi => (List.not_mem_nil hi).elim⟩
  | succ k => exact tight_family (k + 1) (by omega)

/-- THE DYADIC TIGHTNESS AT THE ARSENAL ANCHORS, HYPOTHESIS-FREE (W73):
    `tight_family_arsenal` with the vestigial `1 ≤ j` premise dropped —
    the proof term is identical (`two_pow_pos j` covers every j,
    including j = 0). -/
theorem tight_family_arsenal_uncond (j : Nat) :
    (List.range (2 ^ j * 2 ^ j)).Nodup ∧ fsqrt (2 ^ j * 2 ^ j) = 2 ^ j ∧
    (∀ S : List Nat, S.Nodup → (∀ s ∈ S, s ∈ List.range (2 ^ j * 2 ^ j)) →
        CliqueOn (adjT (2 ^ j)) S → S.length ≤ 2 ^ j) ∧
    (∀ T : List Nat, T.Nodup → (∀ t ∈ T, t ∈ List.range (2 ^ j * 2 ^ j)) →
        IndepOn (adjT (2 ^ j)) T → T.length ≤ 2 ^ j) ∧
    (∃ S : List Nat, S.Nodup ∧ (∀ s ∈ S, s ∈ List.range (2 ^ j * 2 ^ j)) ∧
        S.length = 2 ^ j ∧ CliqueOn (adjT (2 ^ j)) S) ∧
    (∃ T : List Nat, T.Nodup ∧ (∀ t ∈ T, t ∈ List.range (2 ^ j * 2 ^ j)) ∧
        T.length = 2 ^ j ∧ IndepOn (adjT (2 ^ j)) T) :=
  tight_family (2 ^ j) (by
    have h := two_pow_pos j
    omega)

theorem family_board {α : Type} [DecidableEq α] (adj : α → α → Bool)
    (hsym : ∀ i j : α, adj i j = adj j i)
    (hirr : ∀ i : α, adj i i = false) :
    (∀ (vs : List α), vs.Nodup → K1FreeOn adj vs → BoundCert adj vs) ∧
    (∀ (vs : List α), vs.Nodup → K2FreeOn adj vs → BoundCert adj vs) ∧
    (∀ (vs : List α), vs.Nodup → Kb2FreeOn adj vs → BoundCert adj vs) ∧
    (∀ (vs : List α), vs.Nodup → K3FreeOn adj vs → BoundCert adj vs) ∧
    (∀ (vs : List α), vs.Nodup → Kb3FreeOn adj vs → BoundCert adj vs) ∧
    (∀ (vs : List α), vs.Nodup → P3FreeOn adj vs → BoundCert adj vs) ∧
    (∀ (vs : List α), vs.Nodup → Pb3FreeOn adj vs → BoundCert adj vs) :=
  ⟨k1_bound adj, k2_bound adj, kb2_bound adj, k3_bound adj hsym hirr,
    kb3_bound adj hsym hirr, p3_bound adj hsym hirr, pb3_bound adj hsym hirr⟩

theorem E61_FAMILY_GREEN : 0 < 61 := Nat.succ_pos 60

#print axioms E61.family_board
#print axioms E61.closedNbhd_greedy
#print axioms E61.k3_bound
#print axioms E61.p3_bound
#print axioms E61.kb3_bound
#print axioms E61.pb3_bound
#print axioms E61.tight_family
#print axioms E61.arsenal_bridge
#print axioms E61.E61_FAMILY_GREEN

/-! ## §10 THE HYPOTHESIS-FREE CARRIER (W73: BOSS's elimination order)

The `hsym`/`hirr` premises of `family_board` are eliminated by bundling:
`SGraph α` carries the adjacency together with the two simple-graph laws
as structure fields. Every inhabitant satisfies them BY CONSTRUCTION, so
`family_board_uncond` below has NO hypotheses — the universal family
theorem now applies to every bundled graph with zero premises. -/

/-- A simple graph as a carrier: adjacency + symmetry + irreflexivity as
    FIELDS (not premises). -/
structure SGraph (α : Type) where
  adj : α → α → Bool
  hsym : ∀ i j : α, adj i j = adj j i
  hirr : ∀ i : α, adj i i = false

/-- THE FAMILY BOARD, HYPOTHESIS-FREE (W73): the same seven conjuncts as
    `family_board`, stated over the bundled carrier — ZERO premises on the
    theorem itself. -/
theorem family_board_uncond {α : Type} [DecidableEq α] (G : SGraph α) :
    (∀ (vs : List α), vs.Nodup → K1FreeOn G.adj vs → BoundCert G.adj vs) ∧
    (∀ (vs : List α), vs.Nodup → K2FreeOn G.adj vs → BoundCert G.adj vs) ∧
    (∀ (vs : List α), vs.Nodup → Kb2FreeOn G.adj vs → BoundCert G.adj vs) ∧
    (∀ (vs : List α), vs.Nodup → K3FreeOn G.adj vs → BoundCert G.adj vs) ∧
    (∀ (vs : List α), vs.Nodup → Kb3FreeOn G.adj vs → BoundCert G.adj vs) ∧
    (∀ (vs : List α), vs.Nodup → P3FreeOn G.adj vs → BoundCert G.adj vs) ∧
    (∀ (vs : List α), vs.Nodup → Pb3FreeOn G.adj vs → BoundCert G.adj vs) :=
  ⟨k1_bound G.adj, k2_bound G.adj, kb2_bound G.adj, k3_bound G.adj G.hsym G.hirr,
    kb3_bound G.adj G.hsym G.hirr, p3_bound G.adj G.hsym G.hirr, pb3_bound G.adj G.hsym G.hirr⟩

/-- Witness 1: the empty graph on Unit — every pair non-adjacent. -/
def sgEmptyUnit : SGraph Unit :=
  ⟨fun _ _ => false, fun _ _ => rfl, fun _ => rfl⟩

/-- Witness 2: the complete graph on Bool — adjacent iff distinct. -/
def sgCompleteBool : SGraph Bool :=
  ⟨fun i j => decide (i ≠ j),
   fun i j => by cases i <;> cases j <;> rfl,
   fun i => by cases i <;> rfl⟩

/-- Witness 3: the empty graph on Bool. -/
def sgEmptyBool : SGraph Bool :=
  ⟨fun _ _ => false, fun _ _ => rfl, fun _ => rfl⟩

/-- The carrier is inhabited with a real edge: the complete Bool graph
    joins true and false. -/
theorem sgCompleteBool_edge : sgCompleteBool.adj true false = true := rfl

#print axioms E61.family_board_uncond
#print axioms E61.sgCompleteBool_edge
#print axioms E61.tight_family_uncond
#print axioms E61.tight_family_arsenal_uncond
#eval "E61_UNCOND_GREEN"

end E61
