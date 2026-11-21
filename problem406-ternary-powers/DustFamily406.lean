import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE DUST-FAMILY KERNEL (S078): the five exact family laws

## THE OBJECT

The dust tree of the 406 campaign (DustLaw406's object, restated
self-contained): a node at level `j` is a residue class `r mod 3^j` whose
members `K` have the first `j+1` ternary digits of `4^K` all in `{0,1}`.
The S078 assault engine (`caplaw/assault406.py`, `assault406b.py`)
computed the family split of the tree and found FIVE EXACT LAWS,
confirmed through level 13 (and to level 16 in the battery).  This kernel
proves them **for every level, forever**:

* **THE FAM-7 LAW** (`dust_fam7_zero`): `|dust j ∩ {r ≡ 7 mod 9}| = 0`
  (j ≥ 2) — no exponent class `≡ 7 mod 9` ever survives (the row-2 fire,
  as a cardinality law).
* **THE FAM-1 LAW** (`dust_fam1_card`): `|dust j ∩ {r ≡ 1 mod 9}| =
  2^(j-2)` (j ≥ 2) — the hard family holds exactly a quarter of the tree.
* **THE FAM-4 LAW** (`dust_fam4_card`): `|dust j ∩ {r ≡ 4 mod 9}| =
  2^(j-2)` (j ≥ 2) — the witness family (of the riders 1 and 4) also
  exactly a quarter.
* **THE TOWER LAW** (`dust_tower_card`): `|dust j ∩ {3 ∣ r}| = 2^(j-1)`
  (j ≥ 1) — the tower-sheet (scaled-exponent) half of the tree is
  exactly half the dust, at every level.
* **THE MOD-3-TWO LAW** (`dust_mod3two_zero`): `|dust j ∩ {r ≡ 2
  mod 3}| = 0` (j ≥ 1) — the cut-row fire as a cardinality law.

Together: the row families hold exactly half the non-tower dust, split
evenly between `≡ 1` and `≡ 4 mod 9`; the tower sheets hold exactly
half; the fired families hold nothing — the fine structure of the
anti-concentration battlefield, machine-checked at every level.

## THE ENGINE (all self-contained)

Every live child of a level-`j` node `r` is one of `r + t·3^j`
(`t ∈ {0,1,2}` minus the dead child), and for `j ≥ 2` the children stay
in the parent's class mod 9 (for `j ≥ 1`, mod 3): the family filters are
constant on children, so each family's count exactly doubles per level.
The base counts are kernel-decided (the tree computes exactly).

## THE HONEST SCOPE

These are cardinality laws of the necessary-condition tree — the
distribution of the survivors inside the residue lattice.  They do not
close the CAP(185) seam (the wall stands); they map its exact shape.

All arithmetic uses the Arsenal's own laws plus core Nat lemmas — no
external theory, BOSS's mathematics only.
-/

/-! ## §0 The dust tree (the DustLaw406 block, self-contained) -/

/-- The ternary digit at position `p`. -/
def digit3 (x p : Nat) : Nat := x / 3^p % 3

theorem digit3_lt_three (x p : Nat) : digit3 x p < 3 := by
  unfold digit3
  exact Nat.mod_lt _ (show 0 < 3 by decide)

/-- One node's live children: the dead child (the one whose new digit is
2) is dropped; exactly two survive. -/
def dustStep (j r : Nat) : List Nat :=
  match (digit3 (4^r) (j+1)) % 3 with
  | 0 => [r, r + 3^j]
  | 1 => [r, r + 2 * 3^j]
  | _ => [r + 3^j, r + 2 * 3^j]

/-- The level join. -/
def dustJoin : Nat → List Nat → List Nat
  | _, [] => []
  | j, r :: rest => dustStep j r ++ dustJoin j rest

/-- The dust tree: the survivor classes at every level. -/
def dust : Nat → List Nat
  | 0 => [0]
  | j+1 => dustJoin j (dust j)

theorem dust_succ_eq (j : Nat) : dust (j+1) = dustJoin j (dust j) := rfl

theorem dustJoin_cons (j r : Nat) (rest : List Nat) :
    dustJoin j (r :: rest) = dustStep j r ++ dustJoin j rest := rfl

/-- The three step-value laws (the DustLaw406 idiom: matcher-on-literal
keeps its explicit `rfl`). -/
theorem dustStep_val0 (j r : Nat) (h : (digit3 (4^r) (j+1)) % 3 = 0) :
    dustStep j r = [r, r + 3^j] := by unfold dustStep; rw [h]; rfl

theorem dustStep_val1 (j r : Nat) (h : (digit3 (4^r) (j+1)) % 3 = 1) :
    dustStep j r = [r, r + 2 * 3^j] := by unfold dustStep; rw [h]; rfl

theorem dustStep_val2 (j r : Nat) (h : (digit3 (4^r) (j+1)) % 3 = 2) :
    dustStep j r = [r + 3^j, r + 2 * 3^j] := by unfold dustStep; rw [h]; rfl

/-! ## §1 The family predicates and their congruence laws -/

/-- The hard-family filter (`r ≡ 1 mod 9`). -/
def fam1B (r : Nat) : Bool := decide (r % 9 = 1)
/-- The witness-family filter (`r ≡ 4 mod 9`). -/
def fam4B (r : Nat) : Bool := decide (r % 9 = 4)
/-- The fired-family filter (`r ≡ 7 mod 9`). -/
def fam7B (r : Nat) : Bool := decide (r % 9 = 7)
/-- The tower filter (`3 ∣ r`). -/
def towerB (r : Nat) : Bool := decide (r % 3 = 0)
/-- The cut-row-fired filter (`r ≡ 2 mod 3`). -/
def mod3twoB (r : Nat) : Bool := decide (r % 3 = 2)

theorem fam1B_congr : ∀ x y : Nat, x % 9 = y % 9 → fam1B x = fam1B y := by
  intro x y h; rw [fam1B, fam1B, h]

theorem fam4B_congr : ∀ x y : Nat, x % 9 = y % 9 → fam4B x = fam4B y := by
  intro x y h; rw [fam4B, fam4B, h]

theorem fam7B_congr : ∀ x y : Nat, x % 9 = y % 9 → fam7B x = fam7B y := by
  intro x y h; rw [fam7B, fam7B, h]

theorem towerB_congr : ∀ x y : Nat, x % 3 = y % 3 → towerB x = towerB y := by
  intro x y h; rw [towerB, towerB, h]

theorem mod3twoB_congr : ∀ x y : Nat, x % 3 = y % 3 → mod3twoB x = mod3twoB y := by
  intro x y h; rw [mod3twoB, mod3twoB, h]

/-! ## §2 The filter-length engine -/

/-- The length of a filtered two-element list (the `if` form). -/
theorem filter_cons_two (f : Nat → Bool) (a b : Nat) :
    ([a, b].filter f).length = (if f a then 1 else 0) + (if f b then 1 else 0) := by
  by_cases h1 : f a = true
  · by_cases h2 : f b = true
    · simp [List.filter, h1, h2]
    · simp [List.filter, h1, h2]
  · by_cases h2 : f b = true
    · simp [List.filter, h1, h2]
    · simp [List.filter, h1, h2]

/-- Adding a multiple of `3^j` preserves the class mod `m` whenever
`m ∣ 3^j` (the child-residue law). -/
theorem child_mod (m j r t : Nat) (hdiv : m ∣ 3^j) :
    (r + t * 3^j) % m = r % m := by
  obtain ⟨c, hc⟩ := hdiv
  have hd : (t * 3^j) % m = 0 := by
    refine Nat.mod_eq_zero_of_dvd ⟨t * c, ?_⟩
    rw [hc]
    ring
  rw [Nat.add_mod, hd, Nat.add_zero]

/-- **THE FAMILY-FILTER STEP LAW.**  If `m ∣ 3^j` and `f` is constant on
classes mod `m`, then the `f`-count of any node's live children is 2 on
the parent's family and 0 off it. -/
theorem dustStep_filter_len {m : Nat} (j r : Nat) (hdiv : m ∣ 3^j)
    (f : Nat → Bool) (hf : ∀ x y, x % m = y % m → f x = f y) :
    (dustStep j r).filter f |>.length = if f r then 2 else 0 := by
  have hmod1 : (r + 3^j) % m = r % m := child_mod m j r 1 hdiv
  have hmod2 : (r + 2 * 3^j) % m = r % m := child_mod m j r 2 hdiv
  have hc1 : f (r + 3^j) = f r := hf _ _ hmod1
  have hc2 : f (r + 2 * 3^j) = f r := hf _ _ hmod2
  rcases ErdosTernary2.lt_three_cases ((digit3 (4^r) (j+1)) % 3)
      (Nat.mod_lt _ (show 0 < 3 by decide)) with hd | hd | hd
  · rw [dustStep_val0 j r hd, filter_cons_two]
    by_cases h : f r = true
    · have hc1' : f (r + 3^j) = true := by rw [hc1]; exact h
      rw [if_pos h, if_pos hc1', if_pos h]
    · have hc1' : f (r + 3^j) = false := by rw [hc1]; exact h
      rw [if_neg h, if_neg hc1', if_neg h]
  · rw [dustStep_val1 j r hd, filter_cons_two]
    by_cases h : f r = true
    · have hc2' : f (r + 2 * 3^j) = true := by rw [hc2]; exact h
      rw [if_pos h, if_pos hc2', if_pos h]
    · have hc2' : f (r + 2 * 3^j) = false := by rw [hc2]; exact h
      rw [if_neg h, if_neg hc2', if_neg h]
  · rw [dustStep_val2 j r hd, filter_cons_two]
    by_cases h : f r = true
    · have hc1' : f (r + 3^j) = true := by rw [hc1]; exact h
      have hc2' : f (r + 2 * 3^j) = true := by rw [hc2]; exact h
      rw [if_pos hc1', if_pos hc2', if_pos h]
    · have hc1' : f (r + 3^j) = false := by rw [hc1]; exact h
      have hc2' : f (r + 2 * 3^j) = false := by rw [hc2]; exact h
      rw [if_neg hc1', if_neg hc2', if_neg h]

/-- **THE JOIN LAW.**  The `f`-count of a joined level doubles the
`f`-count of the parent level (family-constant `f`, `m ∣ 3^j`). -/
theorem dustJoin_filter_len {m : Nat} (j : Nat) (hdiv : m ∣ 3^j)
    (f : Nat → Bool) (hf : ∀ x y, x % m = y % m → f x = f y) :
    ∀ l : List Nat,
      (dustJoin j l).filter f |>.length = 2 * (l.filter f).length := by
  intro l
  induction l with
  | nil => rfl
  | cons r rest ih =>
    have hstep := dustStep_filter_len j r hdiv f hf
    rw [dustJoin_cons, List.filter_append, List.length_append, hstep, ih]
    by_cases h : f r = true
    · rw [if_pos h]
      have hR : ((r :: rest).filter f).length
          = (rest.filter f).length + 1 := by
        rw [List.filter_cons, if_pos h, List.length_cons]
      rw [hR]
      omega
    · rw [if_neg h]
      have hR : ((r :: rest).filter f).length
          = (rest.filter f).length := by
        rw [List.filter_cons, if_neg h]
      rw [hR]
      omega

/-! ## §3 The divisibility receipts -/

/-- `9 ∣ 3^j` for `j ≥ 2` (the mod-9 family preservation). -/
theorem dvd9_of_two_le (j : Nat) (hj : 2 ≤ j) : 9 ∣ 3^j := by
  refine ⟨3^(j-2), ?_⟩
  rw [show (9:Nat) = 3^2 from rfl, ← Nat.pow_add,
    show 2 + (j - 2) = j from by omega]

/-- `3 ∣ 3^j` for `j ≥ 1` (the mod-3 family preservation). -/
theorem dvd3_of_one_le (j : Nat) (hj : 1 ≤ j) : 3 ∣ 3^j := by
  refine ⟨3^(j-1), ?_⟩
  rw [show (3:Nat) = 3^1 from rfl, ← Nat.pow_add,
    show 1 + (j - 1) = j from by omega]

/-! ## §4 THE FIVE EXACT FAMILY LAWS -/

/-- **THE MOD-3-TWO LAW.**  `|dust j ∩ {r ≡ 2 mod 3}| = 0` for every
`j ≥ 1`: the cut-row fire (every class `≡ 2 mod 3` fires at row 1) as a
cardinality law — the fired family holds nothing, forever. -/
theorem dust_mod3two_zero : ∀ j : Nat, 1 ≤ j →
    (dust j).filter mod3twoB |>.length = 0 := by
  intro j
  induction j with
  | zero => intro hj; exact absurd hj (by omega)
  | succ j ih =>
    intro hj
    rcases (by omega : j = 0 ∨ 1 ≤ j) with h0 | h1
    · subst h0
      decide
    · rw [dust_succ_eq,
        dustJoin_filter_len j (dvd3_of_one_le j h1) mod3twoB mod3twoB_congr]
      have hrec := ih h1
      omega

/-- **THE TOWER LAW.**  `|dust j ∩ {3 ∣ r}| = 2^(j-1)` for every `j ≥ 1`:
the tower-sheet half of the dust is exactly half the tree, at every
level, forever. -/
theorem dust_tower_card : ∀ j : Nat, 1 ≤ j →
    (dust j).filter towerB |>.length = 2^(j-1) := by
  intro j
  induction j with
  | zero => intro hj; exact absurd hj (by omega)
  | succ j ih =>
    intro hj
    rcases (by omega : j = 0 ∨ 1 ≤ j) with h0 | h1
    · subst h0
      decide
    · rw [dust_succ_eq,
        dustJoin_filter_len j (dvd3_of_one_le j h1) towerB towerB_congr,
        show j + 1 - 1 = (j - 1) + 1 from by omega, Nat.pow_succ]
      have hrec := ih h1
      omega

/-- **THE FAM-7 LAW.**  `|dust j ∩ {r ≡ 7 mod 9}| = 0` for every `j ≥ 2`:
no class `≡ 7 mod 9` ever survives — the row-2 fire as a cardinality law
(every `K ≡ 7 mod 9` owns its ternary digit two at position 2). -/
theorem dust_fam7_zero : ∀ j : Nat, 2 ≤ j →
    (dust j).filter fam7B |>.length = 0 := by
  intro j
  induction j with
  | zero => intro hj; exact absurd hj (by omega)
  | succ j ih =>
    intro hj
    rcases (by omega : j = 1 ∨ 2 ≤ j) with h1j | hge
    · subst h1j
      decide
    · rw [dust_succ_eq,
        dustJoin_filter_len j (dvd9_of_two_le j hge) fam7B fam7B_congr]
      have hrec := ih hge
      omega

/-- **THE FAM-1 LAW.**  `|dust j ∩ {r ≡ 1 mod 9}| = 2^(j-2)` for every
`j ≥ 2`: the hard-family (sheet-zero `≡ 1 mod 9`) survivors are exactly
a quarter of the tree, doubling per level, forever. -/
theorem dust_fam1_card : ∀ j : Nat, 2 ≤ j →
    (dust j).filter fam1B |>.length = 2^(j-2) := by
  intro j
  induction j with
  | zero => intro hj; exact absurd hj (by omega)
  | succ j ih =>
    intro hj
    rcases (by omega : j = 1 ∨ 2 ≤ j) with h1j | hge
    · subst h1j
      decide
    · rw [dust_succ_eq,
        dustJoin_filter_len j (dvd9_of_two_le j hge) fam1B fam1B_congr,
        show j + 1 - 2 = (j - 2) + 1 from by omega, Nat.pow_succ]
      have hrec := ih hge
      omega

/-- **THE FAM-4 LAW.**  `|dust j ∩ {r ≡ 4 mod 9}| = 2^(j-2)` for every
`j ≥ 2`: the sheet-zero `≡ 4 mod 9` family — the family of the rider
witnesses 1 and 4 — also exactly a quarter, doubling per level, forever. -/
theorem dust_fam4_card : ∀ j : Nat, 2 ≤ j →
    (dust j).filter fam4B |>.length = 2^(j-2) := by
  intro j
  induction j with
  | zero => intro hj; exact absurd hj (by omega)
  | succ j ih =>
    intro hj
    rcases (by omega : j = 1 ∨ 2 ≤ j) with h1j | hge
    · subst h1j
      decide
    · rw [dust_succ_eq,
        dustJoin_filter_len j (dvd9_of_two_le j hge) fam4B fam4B_congr,
        show j + 1 - 2 = (j - 2) + 1 from by omega, Nat.pow_succ]
      have hrec := ih hge
      omega

/-! ## §5 The receipts (kernel-decided level checks) -/

/-- The family counts at level 3 (the engine's F3 row: fam1 = 2,
fam4 = 2, fam7 = 0, tower = 4 — the first nontrivial level). -/
theorem fam3_receipt :
    (dust 3).filter fam1B |>.length = 2 ∧
    (dust 3).filter fam4B |>.length = 2 ∧
    (dust 3).filter fam7B |>.length = 0 ∧
    (dust 3).filter towerB |>.length = 4 := by decide

/-- The level-4 counts (fam1 = 4, fam4 = 4, tower = 8). -/
theorem fam4_receipt :
    (dust 4).filter fam1B |>.length = 4 ∧
    (dust 4).filter fam4B |>.length = 4 ∧
    (dust 4).filter towerB |>.length = 8 := by decide

/-! ## §6 The receipt board -/

#check dust_mod3two_zero
#check dust_tower_card
#check dust_fam7_zero
#check dust_fam1_card
#check dust_fam4_card

#print axioms dust_mod3two_zero
#print axioms dust_tower_card
#print axioms dust_fam7_zero
#print axioms dust_fam1_card
#print axioms dust_fam4_card

#eval "ERDOS406_DUSTFAMILY_KERNEL_GREEN"
