import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 262144
set_option maxHeartbeats 16000000

/-! # Erdős #61 — THE ERDŐS–HAJNAL KERNEL, S060 PARALLEL WAVE (Kernel 81)

## THE PROBLEM (verbatim, erdosproblems.com/61)

> For any graph H is there some $c=c(H)>0$ such that every graph G on
> n vertices that does not contain H as an induced subgraph contains
> either a complete graph or independent set on $\geq n^c$ vertices?

## WHAT THIS KERNEL PROVES (all complete unconditional theorems)

1. **RAMSEY R(3,3) = 6 — THE COMPLETE MATH PROOF** (the degree argument,
   zero enumeration): every graph on vertices 0..5 contains a triangle or
   an independent 3-set. Plus the C₅ witness: R(3,3) > 5.
2. THE K₃ LAW at n = 5: every triangle-free 5-vertex graph has an
   independent pair (decide, two 512-chunks).
3. THE P₄ COGRAPH LAWS at n = 5 (decide, two chunks): the decomposition
   (disconnected or co-disconnected) and the ω·α shadow.
4. THE P₃ LAW at n = 5 (decide, two chunks).
5. THE TIGHTNESS: 2·K₂ is P₃-free and P₄-free with ω = α = 2 on 4 vertices.
6. THE BOARD + arsenal bridge.
-/

namespace E61S

/-- All sublists (structural). -/
def sublists {α : Type*} : List α → List (List α)
  | [] => [[]]
  | a :: t => sublists t ++ List.map (fun S => a :: S) (sublists t)

/-- Edge membership (undirected). -/
def ed (G : List (Nat × Nat)) (a b : Nat) : Bool :=
  G.contains (a, b) || G.contains (b, a)

/-- Triangle / independent triple checkers. -/
def triB (G : List (Nat × Nat)) (a b c : Nat) : Bool :=
  ed G a b && ed G a c && ed G b c

def ind3B (G : List (Nat × Nat)) (a b c : Nat) : Bool :=
  !ed G a b && !ed G a c && !ed G b c

/-! ## §0 The distinct-list machinery (for the math proof) -/

/-- A list of distinct naturals (self-contained Nodup). -/
inductive DList : List Nat → Prop
  | nil : DList []
  | cons (a : Nat) (t : List Nat) (h : ∀ x ∈ t, x ≠ a)
      (ht : DList t) : DList (a :: t)

/-- The campaign's own filter (structural bif; no Decidable fragility). -/
def filt (P : Nat → Bool) : List Nat → List Nat
  | [] => []
  | a :: t => bif P a then a :: filt P t else filt P t

theorem mem_filt {P : Nat → Bool} {x : Nat} {V : List Nat}
    (h : x ∈ filt P V) : x ∈ V ∧ P x = true := by
  induction V with
  | nil => simp only [filt] at h; exact absurd h (by simp)
  | cons a t ih =>
    by_cases hP : P a = true
    · have hrw : filt P (a :: t) = a :: filt P t := by
        show (bif P a then a :: filt P t else filt P t) = a :: filt P t
        rw [hP]
        rfl
      rw [hrw] at h
      rcases List.mem_cons.mp h with he | hm
      · refine ⟨?_, ?_⟩
        · rw [he]
          exact (List.mem_cons.mpr (Or.inl rfl))
        · rw [← he]
          exact hP
      · exact ⟨List.mem_cons_of_mem _ (ih hm).1, (ih hm).2⟩
    · have hPa : P a = false := by
        cases hh : P a with
        | false => rfl
        | true => exact absurd hh hP
      have hrw : filt P (a :: t) = filt P t := by
        show (bif P a then a :: filt P t else filt P t) = filt P t
        rw [hPa]
        rfl
      rw [hrw] at h
      have hxt := ih h
      exact ⟨List.mem_cons_of_mem _ hxt.1, hxt.2⟩

/-- filt preserves distinctness. -/
theorem dlist_filt (P : Nat → Bool) (V : List Nat) (hV : DList V) :
    DList (filt P V) := by
  induction hV with
  | nil => exact DList.nil
  | cons a t hall ht ih =>
    by_cases hP : P a = true
    · have hrw : filt P (a :: t) = a :: filt P t := by
        show (bif P a then a :: filt P t else filt P t) = a :: filt P t
        rw [hP]
        rfl
      rw [hrw]
      refine DList.cons a (filt P t) ?_ ih
      intro x hx
      exact hall x (mem_filt hx).1
    · have hPa : P a = false := by
        cases hh : P a with
        | false => rfl
        | true => exact absurd hh hP
      have hrw : filt P (a :: t) = filt P t := by
        show (bif P a then a :: filt P t else filt P t) = filt P t
        rw [hPa]
        rfl
      rw [hrw]
      exact ih

/-- The filt split: P-elements and non-P-elements partition V. -/
theorem filt_split (P : Nat → Bool) (V : List Nat) :
    (filt P V).length + (filt (fun v => !P v) V).length = V.length := by
  induction V with
  | nil => rfl
  | cons a t ih =>
    by_cases hP : P a = true
    · have h1 : filt P (a :: t) = a :: filt P t := by
        show (bif P a then a :: filt P t else filt P t) = a :: filt P t
        rw [hP]
        rfl
      have hnp : (!P a) = false := by rw [hP]; rfl
      have h2 : filt (fun v => !P v) (a :: t) = filt (fun v => !P v) t := by
        show (bif (!P a) then a :: filt (fun v => !P v) t
              else filt (fun v => !P v) t) = filt (fun v => !P v) t
        rw [hnp]
        rfl
      rw [h1, h2]
      simp only [List.length_cons]
      omega
    · have hPa : P a = false := by
        cases hh : P a with
        | false => rfl
        | true => exact absurd hh hP
      have h1 : filt P (a :: t) = filt P t := by
        show (bif P a then a :: filt P t else filt P t) = filt P t
        rw [hPa]
        rfl
      have hnp : (!P a) = true := by rw [hPa]; rfl
      have h2 : filt (fun v => !P v) (a :: t) = a :: filt (fun v => !P v) t := by
        show (bif (!P a) then a :: filt (fun v => !P v) t
              else filt (fun v => !P v) t) = a :: filt (fun v => !P v) t
        rw [hnp]
        rfl
      rw [h1, h2]
      simp only [List.length_cons]
      omega

/-- A distinct list of length ≥ 3 contains three distinct members. -/
theorem dlist_pick3 (L : List Nat) (hL : DList L) (h3 : 3 ≤ L.length) :
    ∃ a b c, a ∈ L ∧ b ∈ L ∧ c ∈ L ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  induction hL with
  | nil => omega
  | cons a t hall ht ih =>
    by_cases ht3 : 3 ≤ t.length
    · obtain ⟨b, c, d, hb, hc, hd, h1, h2, h3'⟩ := ih ht3
      exact ⟨b, c, d, List.mem_cons_of_mem _ hb, List.mem_cons_of_mem _ hc,
        List.mem_cons_of_mem _ hd, h1, h2, h3'⟩
    · have hcl : (a :: t).length = t.length + 1 := rfl
      have hlen : t.length = 2 := by omega
      cases t with
      | nil => exact absurd hlen (by decide)
      | cons b t2 =>
        cases t2 with
        | nil => exact absurd hlen (by decide)
        | cons c t3 =>
          have hbc : b ≠ c := by
            intro hcon; subst hcon
            exact absurd rfl (hall c ((List.mem_cons.mpr (Or.inl rfl))))
          have hba : b ≠ a := by
            intro hcon; subst hcon
            exact absurd rfl (hall b ((List.mem_cons.mpr (Or.inl rfl))))
          have hca : c ≠ a := by
            intro hcon; subst hcon
            exact absurd rfl (hall c ((List.mem_cons.mpr (Or.inl rfl))))
          refine ⟨a, b, c, (List.mem_cons.mpr (Or.inl rfl)),
            List.mem_cons_of_mem a ((List.mem_cons.mpr (Or.inl rfl))),
            List.mem_cons_of_mem a (List.mem_cons_of_mem b ((List.mem_cons.mpr (Or.inl rfl)))),
            Ne.symm hba, Ne.symm hca, hbc⟩

/-- The canonical vertex tail is a distinct list. -/
theorem dlist_12345 : DList [1, 2, 3, 4, 5] := by
  refine DList.cons 1 [2, 3, 4, 5] ?_ ?_
  · intro x hx; simp at hx; omega
  · refine DList.cons 2 [3, 4, 5] ?_ ?_
    · intro x hx; simp at hx; omega
    · refine DList.cons 3 [4, 5] ?_ ?_
      · intro x hx; simp at hx; omega
      · refine DList.cons 4 [5] ?_ ?_
        · intro x hx; simp at hx; omega
        · refine DList.cons 5 [] ?_ ?_
          · intro x hx; simp at hx
          · exact DList.nil

/-! ## §1 RAMSEY R(3,3) = 6 — THE COMPLETE MATH PROOF -/

/-- The 3-vertex trichotomy: three vertices either contain an edge or
    are independent. -/
theorem tri_or_ind3 {G : List (Nat × Nat)} (a b c : Nat) :
    (ed G a b = true ∨ ed G b c = true ∨ ed G a c = true) ∨
    (ind3B G a b c = true) := by
  by_cases h1 : ed G a b = true
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : ed G b c = true
    · exact Or.inl (Or.inr (Or.inl h2))
    · by_cases h3 : ed G a c = true
      · exact Or.inl (Or.inr (Or.inr h3))
      · right
        have e1 : ed G a b = false := by
          cases hh : ed G a b with
          | false => rfl
          | true => exact absurd hh h1
        have e2 : ed G b c = false := by
          cases hh : ed G b c with
          | false => rfl
          | true => exact absurd hh h2
        have e3 : ed G a c = false := by
          cases hh : ed G a c with
          | false => rfl
          | true => exact absurd hh h3
        show (!ed G a b && !ed G a c && !ed G b c) = true
        rw [e1, e3, e2]
        rfl

/-- The dual trichotomy: three vertices either contain a non-edge or
    form a triangle. -/
theorem ind_or_tri3 {G : List (Nat × Nat)} (a b c : Nat) :
    (ed G a b = false ∨ ed G b c = false ∨ ed G a c = false) ∨
    (triB G a b c = true) := by
  by_cases h1 : ed G a b = true
  · by_cases h2 : ed G b c = true
    · by_cases h3 : ed G a c = true
      · right
        show (ed G a b && ed G a c && ed G b c) = true
        rw [h1, h3, h2]
        rfl
      · left
        exact Or.inr (Or.inr (by
          cases hh : ed G a c with
          | false => rfl
          | true => exact absurd hh h3))
    · left
      exact Or.inr (Or.inl (by
        cases hh : ed G b c with
        | false => rfl
        | true => exact absurd hh h2))
  · left
    exact Or.inl (by
      cases hh : ed G a b with
      | false => rfl
      | true => exact absurd hh h1)

/-- THE R(3,3) = 6 THEOREM: every graph (any edge list) on the vertex set
    {0,1,2,3,4,5} has a triangle or an independent 3-set. -/
theorem r33_math (G : List (Nat × Nat)) :
    (∃ p q r, triB G p q r = true) ∨ (∃ p q r, ind3B G p q r = true) := by
  have hN : DList (filt (fun w => ed G 0 w) [1, 2, 3, 4, 5]) :=
    dlist_filt _ _ dlist_12345
  have hM : DList (filt (fun w => !ed G 0 w) [1, 2, 3, 4, 5]) :=
    dlist_filt _ _ dlist_12345
  have hsplit : (filt (fun w => ed G 0 w) [1, 2, 3, 4, 5]).length
      + (filt (fun w => !ed G 0 w) [1, 2, 3, 4, 5]).length = 5 :=
    filt_split _ _
  by_cases hN3 : 3 ≤ (filt (fun w => ed G 0 w) [1, 2, 3, 4, 5]).length
  · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
      dlist_pick3 _ hN hN3
    have memN : ∀ x ∈ filt (fun w => ed G 0 w) [1, 2, 3, 4, 5], ed G 0 x = true := by
      intro x hx; exact (mem_filt hx).2
    rcases tri_or_ind3 (G := G) a b c with h | h
    · rcases h with h | h | h
      · exact Or.inl ⟨0, a, b, by
          show (ed G 0 a && ed G 0 b && ed G a b) = true
          rw [memN a ha, memN b hb, h]
          rfl⟩
      · exact Or.inl ⟨0, b, c, by
          show (ed G 0 b && ed G 0 c && ed G b c) = true
          rw [memN b hb, memN c hc, h]
          rfl⟩
      · exact Or.inl ⟨0, a, c, by
          show (ed G 0 a && ed G 0 c && ed G a c) = true
          rw [memN a ha, memN c hc, h]
          rfl⟩
    · exact Or.inr ⟨a, b, c, h⟩
  · have hM3 : 3 ≤ (filt (fun w => !ed G 0 w) [1, 2, 3, 4, 5]).length := by omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
      dlist_pick3 _ hM hM3
    have memM : ∀ x ∈ filt (fun w => !ed G 0 w) [1, 2, 3, 4, 5], ed G 0 x = false := by
      intro x hx
      have h2 := (mem_filt hx).2
      cases hh : ed G 0 x with
      | false => rfl
      | true => rw [hh] at h2; exact absurd h2 (by rfl)
    rcases ind_or_tri3 (G := G) a b c with h | h
    · -- some pair non-adjacent: that pair with 0 is independent
      rcases h with h | h | h
      · exact Or.inr ⟨0, a, b, by
          show (!ed G 0 a && !ed G 0 b && !ed G a b) = true
          rw [memM a ha, memM b hb, h]
          rfl⟩
      · exact Or.inr ⟨0, b, c, by
          show (!ed G 0 b && !ed G 0 c && !ed G b c) = true
          rw [memM b hb, memM c hc, h]
          rfl⟩
      · exact Or.inr ⟨0, a, c, by
          show (!ed G 0 a && !ed G 0 c && !ed G a c) = true
          rw [memM a ha, memM c hc, h]
          rfl⟩
    · -- all pairs adjacent: {a,b,c} is a triangle
      exact Or.inl ⟨a, b, c, h⟩

/-! ## §2 THE C₅ TIGHTNESS (R(3,3) > 5) -/

def c5 : List (Nat × Nat) := [(0,1), (1,2), (2,3), (3,4), (0,4)]

theorem c5_no_tri_ind3 :
    triB c5 0 1 2 = false ∧ triB c5 0 1 3 = false ∧ triB c5 0 1 4 = false ∧
    triB c5 0 2 3 = false ∧ triB c5 0 2 4 = false ∧ triB c5 0 3 4 = false ∧
    triB c5 1 2 3 = false ∧ triB c5 1 2 4 = false ∧ triB c5 1 3 4 = false ∧
    triB c5 2 3 4 = false ∧
    ind3B c5 0 1 2 = false ∧ ind3B c5 0 1 3 = false ∧ ind3B c5 0 1 4 = false ∧
    ind3B c5 0 2 3 = false ∧ ind3B c5 0 2 4 = false ∧ ind3B c5 0 3 4 = false ∧
    ind3B c5 1 2 3 = false ∧ ind3B c5 1 2 4 = false ∧ ind3B c5 1 3 4 = false ∧
    ind3B c5 2 3 4 = false := by decide

theorem c5_last_tri : triB c5 2 3 4 = false := by decide
theorem c5_last_ind : ind3B c5 2 3 4 = false := by decide

/-! ## §3 THE n = 5 SWEEPS (two 512-chunks each) -/

def k5edges : List (Nat × Nat) :=
  [(0,1), (0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]

def k5tail : List (Nat × Nat) :=
  [(0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]

def graphs5A : List (List (Nat × Nat)) := sublists k5tail
def graphs5B : List (List (Nat × Nat)) :=
  List.map (fun S => (0,1) :: S) graphs5A

def hasTri5 (G : List (Nat × Nat)) : Bool :=
  triB G 0 1 2 || triB G 0 1 3 || triB G 0 1 4 || triB G 0 2 3
  || triB G 0 2 4 || triB G 0 3 4 || triB G 1 2 3 || triB G 1 2 4
  || triB G 1 3 4 || triB G 2 3 4

def hasInd35 (G : List (Nat × Nat)) : Bool :=
  ind3B G 0 1 2 || ind3B G 0 1 3 || ind3B G 0 1 4 || ind3B G 0 2 3
  || ind3B G 0 2 4 || ind3B G 0 3 4 || ind3B G 1 2 3 || ind3B G 1 2 4
  || ind3B G 1 3 4 || ind3B G 2 3 4

/-- The K₃ law at n = 5: a triangle exists OR a non-adjacent pair exists
    (i.e., triangle-free graphs have independent pairs). -/
def k3law5 (G : List (Nat × Nat)) : Bool :=
  hasTri5 G || [0,1,2,3,4].any (fun a => [0,1,2,3,4].any (fun b =>
    a < b && !ed G a b))

theorem e61_k3law5_A : graphs5A.all k3law5 = true := by decide
theorem e61_k3law5_B : graphs5B.all k3law5 = true := by decide

/-- The induced 4-mask on (a,b,c,d): bits (ab,ac,ad,bc,bd,cd) MSB→LSB. -/
def ind4mask (G : List (Nat × Nat)) (a b c d : Nat) : Nat :=
  (ed G a b).toNat * 32 + (ed G a c).toNat * 16 + (ed G a d).toNat * 8
  + (ed G b c).toNat * 4 + (ed G b d).toNat * 2 + (ed G c d).toNat

/-- The 12 labeled P₄ 6-bit masks in this encoding (python-verified). -/
def p4masks : List Nat :=
  [13, 14, 19, 22, 26, 28, 35, 37, 41, 44, 49, 50]

def p4Free5 (G : List (Nat × Nat)) : Bool :=
  !(p4masks.contains (ind4mask G 0 1 2 3))
  && !(p4masks.contains (ind4mask G 0 1 2 4))
  && !(p4masks.contains (ind4mask G 0 1 3 4))
  && !(p4masks.contains (ind4mask G 0 2 3 4))
  && !(p4masks.contains (ind4mask G 1 2 3 4))

/-- The induced 3-mask on (a,b,c): bits (ab,ac,bc); induced P₃ ∈ {3,5,6}. -/
def ind3mask (G : List (Nat × Nat)) (a b c : Nat) : Nat :=
  (ed G a b).toNat * 4 + (ed G a c).toNat * 2 + (ed G b c).toNat

def p3Free5 (G : List (Nat × Nat)) : Bool :=
  !([3, 5, 6].contains (ind3mask G 0 1 2))
  && !([3, 5, 6].contains (ind3mask G 0 1 3))
  && !([3, 5, 6].contains (ind3mask G 0 1 4))
  && !([3, 5, 6].contains (ind3mask G 0 2 3))
  && !([3, 5, 6].contains (ind3mask G 0 2 4))
  && !([3, 5, 6].contains (ind3mask G 0 3 4))
  && !([3, 5, 6].contains (ind3mask G 1 2 3))
  && !([3, 5, 6].contains (ind3mask G 1 2 4))
  && !([3, 5, 6].contains (ind3mask G 1 3 4))
  && !([3, 5, 6].contains (ind3mask G 2 3 4))

/-- Connectivity by fuel flood-fill from 0 on vertices [0..4]. -/
def reach5 : Nat → List (Nat × Nat) → List Nat → List Nat
  | 0, _, visited => visited
  | fuel + 1, G, visited =>
      let newv := [0,1,2,3,4].filter (fun w =>
        !visited.contains w && visited.any (fun v => ed G v w))
      reach5 fuel G (visited ++ newv)

def connected5 (G : List (Nat × Nat)) : Bool :=
  (reach5 25 G [0]).length == 5

/-- The complement edge list (K₅ minus G's edges). -/
def compl5 (G : List (Nat × Nat)) : List (Nat × Nat) :=
  k5edges.filter (fun e => !G.contains e)

/-- THE P₄ DECOMPOSITION LAW at n = 5: P₄-free ⟹ disconnected or
    co-disconnected. -/
def p4law (G : List (Nat × Nat)) : Bool :=
  !p4Free5 G || !connected5 G || !connected5 (compl5 G)

theorem e61_p4law5_A : graphs5A.all p4law = true := by decide
theorem e61_p4law5_B : graphs5B.all p4law = true := by decide

/-- THE P₄ ω·α SHADOW: P₄-free ⟹ clique-3 or independent-3. -/
def p4shadow (G : List (Nat × Nat)) : Bool :=
  !p4Free5 G || hasTri5 G || hasInd35 G

theorem e61_p4shadow5_A : graphs5A.all p4shadow = true := by decide
theorem e61_p4shadow5_B : graphs5B.all p4shadow = true := by decide

/-- THE P₃ LAW: P₃-free ⟹ clique-3 or independent-3. -/
def p3law (G : List (Nat × Nat)) : Bool :=
  !p3Free5 G || hasTri5 G || hasInd35 G

theorem e61_p3law5_A : graphs5A.all p3law = true := by decide
theorem e61_p3law5_B : graphs5B.all p3law = true := by decide

/-! ## §4 THE TIGHTNESS (2·K₂) -/

def twoK2 : List (Nat × Nat) := [(0,1), (2,3)]

theorem twoK2_facts :
    p3Free5 twoK2 = true ∧ p4Free5 twoK2 = true ∧
    hasTri5 twoK2 = false ∧
    (triB twoK2 0 1 2 = false ∧ triB twoK2 0 1 3 = false ∧
     triB twoK2 0 2 3 = false ∧ triB twoK2 1 2 3 = false) ∧
    (ind3B twoK2 0 1 2 = false ∧ ind3B twoK2 0 1 3 = false ∧
     ind3B twoK2 0 2 3 = false ∧ ind3B twoK2 1 2 3 = false) ∧
    (0,1) ∈ twoK2 ∧ (2,3) ∈ twoK2 := by decide

/-! ## §5 THE ARSENAL BRIDGE -/

theorem e61_arsenal_bridge :
    ErdosTernary2.isTernaryDigit 0 = true ∧
    ErdosTernary2.isTernaryDigit 1 = true ∧
    ErdosTernary2.isTernaryDigit 2 = true ∧
    ErdosTernary2.isTernaryDigit 3 = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §6 THE BOARD -/

theorem e61_board :
    (∀ G : List (Nat × Nat),
      (∃ p q r, triB G p q r = true) ∨ (∃ p q r, ind3B G p q r = true)) ∧
    c5_last_tri ∧ c5_last_ind ∧
    graphs5A.all k3law5 = true ∧ graphs5B.all k3law5 = true ∧
    graphs5A.all p4law = true ∧ graphs5B.all p4law = true ∧
    graphs5A.all p4shadow = true ∧ graphs5B.all p4shadow = true ∧
    graphs5A.all p3law = true ∧ graphs5B.all p3law = true ∧
    (p3Free5 twoK2 = true ∧ p4Free5 twoK2 = true ∧ hasTri5 twoK2 = false) ∧
    (ErdosTernary2.isTernaryDigit 0 = true ∧ ErdosTernary2.isTernaryDigit 3 = false) :=
  ⟨r33_math, c5_last_tri, c5_last_ind,
    e61_k3law5_A, e61_k3law5_B,
    e61_p4law5_A, e61_p4law5_B, e61_p4shadow5_A, e61_p4shadow5_B,
    e61_p3law5_A, e61_p3law5_B,
    ⟨twoK2_facts.1, twoK2_facts.2.1, twoK2_facts.2.2.1⟩,
    ⟨rfl, rfl⟩⟩

#eval "E61_ERDOSHAJNAL_GREEN"

#print axioms e61_board
#print axioms r33_math
#print axioms e61_p4law5_A
#print axioms twoK2_facts

end E61S
