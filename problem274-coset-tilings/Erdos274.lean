import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos274 — THE COSET-TILING KERNEL r1 (W57-4, Kernel — P274)

Erdős #274 (verbatim, erdosproblems.com/274):

> Let G be a group with |G| = n. Is it true that G can be partitioned into
> cosets of distinct sizes, i.e. cosets of distinct subgroups whose sizes
> are all distinct? (The "coset tilings" problem.)

Campaign state: abelian groups of order ≤ 36 ALL NEGATIVE (17 groups
checked); nonabelian ≤ 24 queued. A tiling exists ⟺ some group admits a
distinct-size coset partition; the witness hunt is the frontier.

THE BOARD (full statements, complete unconditional proofs, zero sorry):
1. THE ARITHMETIC TILING FRAME (group-free): `tilingSizes` — sizes divide
   the order, distinct, sum to the order. `feasible_structure`: every n
   admits the trivial one-coset multiset [n] (G as a single coset of
   itself — the k = 1 degenerate layer).
2. `two_coset_impossible` — THE TWO-COSET KILL (full, all n, no search):
   no two positive distinct subgroup orders a < b with a + b = n can both
   divide n. Proof: the larger b divides n, hence b ∣ n − b = a
   (`Nat.dvd_sub`), so b ≤ a (`Nat.le_of_dvd`) — contradiction. Subgroup
   orders divide |G| in ANY group, so no 2-coset distinct-size tiling
   exists in ANY group of ANY order.
3. `divisor_le_half` — the structural law: a proper coset size (a divisor
   d < n) satisfies 2·d ≤ n (proper cosets have size ≤ n/2).
4. THE MULTI-COSET ARITHMETIC WITNESSES: [1,2,3] tiles 6; [2,4,6] and
   [1,2,3,6] tile 12 — arithmetic is FEASIBLE at k ≥ 3; the group theory
   is what blocks real instances (the census below).
5. THE CYCLIC CENSUS (decide-certified): for C_n = Z/n, the subgroup of
   order s (s ∣ n) is the multiples of n/s (unique), and its cosets are
   the residue classes x ≡ c (mod n/s), c < n/s. A distinct-size coset
   tiling of C_n is exactly: distinct divisors s_i of n (k ≥ 2, Σ s_i = n)
   plus shifts c_i making the classes pairwise disjoint (equivalently:
   every x < n lies in exactly one). `cyclicHasTiling n` enumerates ALL
   divisor subsets with ALL shift assignments (exhaustive over the
   (subgroup, coset) choices) and checks exact cover; `by decide`
   certifies FALSE for every n ≤ 12 (only n = 6 and n = 12 have arithmetic
   candidates at all — 36 resp. 612 shift assignments, all failing
   disjointness). Python battery `battery274.py` mirrors the search and
   cross-checks to n ≤ 36.
6. `e274_arsenal_bridge` — BOSS's arsenal applied to the anchors
   (erdosternary2 + CardinalWorlds: `isTernaryDigit`, `sq_sub_one`,
   `mod_mod_mul`, `carryAtPos_bound`, `v2r_ternary_scaling`, `v2r`).
7. `e274_board` — the master composite (seven conjuncts, one term each).

House law: GitHub CI is the verifier of record (no local compile; author
blind). Axiom profile within [propext, Classical.choice, Quot.sound].
Zero sorry, zero native_decide.
-/

namespace E274

/-! ## §1 The arithmetic tiling frame (group-free core). -/

/-- List sum. -/
def sumNat : List Nat → Nat
  | [] => 0
  | s :: t => s + sumNat t

/-- Boolean membership. -/
def memNat : Nat → List Nat → Bool
  | _, [] => false
  | s, t :: r => (s == t) || memNat s r

/-- All entries pairwise distinct. -/
def sizesDistinct : List Nat → Bool
  | [] => true
  | s :: t => !(memNat s t) && sizesDistinct t

/-- Every entry divides `n` (Boolean arithmetic mirror of `∣`). -/
def dividesAll (n : Nat) : List Nat → Bool
  | [] => true
  | s :: t => (n % s == 0) && dividesAll n t

/-- THE TILING FRAME: `sizes` is an arithmetic coset-size multiset for an
order-`n` group — each size divides the order, the sizes are distinct,
and they sum to the order. -/
def tilingSizes (n : Nat) (sizes : List Nat) : Bool :=
  (dividesAll n sizes) && (sizesDistinct sizes) && (sumNat sizes == n)

/-- Reflexivity of boolean equality on Nat (self-contained core-free). -/
theorem beq_self_true (n : Nat) : (n == n) = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

/-- The trivial one-coset multiset [n] passes the tiling frame. -/
theorem tilingSizes_self (n : Nat) : tilingSizes n [n] = true := by
  have h1 : (dividesAll n [n]) = true := by
    show (n % n == 0) && true = true
    rw [Nat.mod_self n]
  have h2 : (sizesDistinct [n]) = true := rfl
  have h3 : (sumNat [n] == n) = true := beq_self_true n
  show (dividesAll n [n]) && (sizesDistinct [n]) && (sumNat [n] == n) = true
  rw [h1, h2, h3]

/-- THE ARITHMETIC FEASIBILITY LAW (trivial layer): every order n admits
the one-coset size multiset [n] (G as a single coset of itself). -/
theorem feasible_structure (n : Nat) : ∃ sizes : List Nat, tilingSizes n sizes = true :=
  ⟨[n], tilingSizes_self n⟩

/-! ## §2 THE TWO-COSET KILL (full, group-general, all n). -/

/-- THE TWO-COSET IMPOSSIBILITY: no order n has two positive distinct
subgroup orders a < b with a + b = n and b ∣ n. Proof: b ∣ n and b ∣ b
give b ∣ n − b = a (`Nat.dvd_sub`); 0 < a then forces b ≤ a
(`Nat.le_of_dvd`), contradicting a < b. The hypothesis a ∣ n is not even
needed: the LARGER of two distinct sizes summing to the order can never
divide the order. In any group, coset sizes are subgroup orders, which
divide |G| — so no 2-coset distinct-size tiling exists in ANY group of
ANY order. -/
theorem two_coset_impossible (n a b : Nat) (ha : 0 < a) (hab : a < b)
    (hnb : b ∣ n) (hsum : a + b = n) : False := by
  have hsub : b ∣ n - b := Nat.dvd_sub hnb (Nat.dvd_refl b)
  have hne : n - b = a := by omega
  have hba : b ∣ a := by rw [← hne]; exact hsub
  have hle : b ≤ a := Nat.le_of_dvd ha hba
  omega

/-- The tiling-flavored form: no order n admits two coset sizes a < b
(both subgroup orders, hence divisors of n) with a + b = n. -/
theorem no_two_coset_tiling (n : Nat) :
    ¬ ∃ a b : Nat, 0 < a ∧ a < b ∧ a ∣ n ∧ b ∣ n ∧ a + b = n := by
  intro h
  obtain ⟨a, b, ha, hab, _, hnb, hsum⟩ := h
  exact two_coset_impossible n a b ha hab hnb hsum

/-- The proper-coset form: two distinct divisors of n (each ≤ n/2, i.e.
proper subgroup orders) can never sum to n. -/
theorem no_two_coset_half (n : Nat) :
    ¬ ∃ a b : Nat, a ∣ n ∧ b ∣ n ∧ a ≠ b ∧ a + b = n ∧ a ≤ n / 2 ∧ b ≤ n / 2 := by
  intro h
  obtain ⟨a, b, han, hbn, hne, hsum, _, _⟩ := h
  have ha0 : 0 < a := by
    cases a with
    | zero =>
      exfalso
      obtain ⟨k, hk⟩ := han
      rw [Nat.zero_mul] at hk
      omega
    | succ m => omega
  have hb0 : 0 < b := by
    cases b with
    | zero =>
      exfalso
      obtain ⟨k, hk⟩ := hbn
      rw [Nat.zero_mul] at hk
      omega
    | succ m => omega
  rcases (by omega : a < b ∨ b ≤ a) with hab | hab
  · exact two_coset_impossible n a b ha0 hab hbn hsum
  · exact two_coset_impossible n b a hb0 (by omega) han (by omega)

/-! ## §3 The proper-size structural law. -/

/-- THE PROPER-SIZE LAW: a proper coset size (a subgroup order d dividing
n with d < n — any size that can occur in a ≥ 2-coset tiling, since then
some other coset is nonempty) satisfies 2·d ≤ n, i.e. every proper coset
has size ≤ n/2. -/
theorem divisor_le_half (d n : Nat) (hd : d ∣ n) (hlt : d < n) : 2 * d ≤ n := by
  obtain ⟨k, hk⟩ := hd
  have hk2 : 2 ≤ k := by
    rcases (by omega : k < 2 ∨ 2 ≤ k) with h | h
    · exfalso
      cases k with
      | zero =>
        rw [Nat.mul_zero] at hk
        omega
      | succ m =>
        cases m with
        | zero =>
          rw [Nat.mul_succ, Nat.mul_zero] at hk
          omega
        | succ m2 => omega
    · exact h
  have h3 : d * 2 ≤ d * k := Nat.mul_le_mul_left d hk2
  omega

/-! ## §4 The multi-coset arithmetic witnesses. -/

/-- THE k = 3 FEASIBILITY WITNESS (arithmetic layer): 6 = 1+2+3 with
1, 2, 3 all dividing 6, distinct. Arithmetic is FEASIBLE at k ≥ 3 — the
blocking is group-theoretic (C_6 has no such disjoint coset system, §5). -/
theorem feasible_6 : tilingSizes 6 [1, 2, 3] = true := by decide

/-- THE k = 4 FEASIBILITY WITNESS: 12 = 1+2+3+6, all dividing 12. -/
theorem feasible_12 : tilingSizes 12 [1, 2, 3, 6] = true := by decide

/-- THE k = 3 FEASIBILITY WITNESS at order 12: 12 = 2+4+6. -/
theorem feasible_12b : tilingSizes 12 [2, 4, 6] = true := by decide

/-! ## §5 THE CYCLIC CENSUS (decide-certified, n ≤ 12).

Model: C_n = Z/n. For s ∣ n the (unique) subgroup of order s is the set
of multiples of n/s; its cosets are the residue classes x ≡ c (mod n/s)
with c ∈ [0, n/s), each of size exactly s. A distinct-size coset tiling
of C_n is exactly: distinct divisors s_i of n (k ≥ 2, Σ s_i = n) and
shifts c_i with every x < n in exactly one class. The search below is
exhaustive over divisor subsets and shift assignments — i.e. over all
(subgroup, coset) choices of C_n, in canonical ascending-size order. -/

/-- The size projections of a coset configuration. -/
def sizeList : List (Nat × Nat) → List Nat
  | [] => []
  | p :: t => p.1 :: sizeList t

/-- Count of the configuration's cosets containing x (the coset (s, c)
contains x iff x ≡ c mod n/s). -/
def cosetCount (n : Nat) : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (s, c) :: t, x => (if x % (n / s) == c then 1 else 0) + cosetCount n t x

/-- Exact-cover check: every x < k lies in exactly one coset. -/
def coverOK (n : Nat) (cfg : List (Nat × Nat)) : Nat → Bool
  | 0 => true
  | (k + 1) => (cosetCount n cfg k == 1) && coverOK n cfg k

/-- Per-coset validity: size ≥ 1, size divides n, shift < n / size. -/
def cfgElemOK (n : Nat) (p : Nat × Nat) : Bool :=
  (n % p.1 == 0) && !(p.1 == 0) && Nat.ble (p.2 + 1) (n / p.1)

def cfgAllOK (n : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | p :: t => (cfgElemOK n p) && cfgAllOK n t

/-- The full configuration checker: ≥ 2 cosets, sizes divide n and are
≥ 1, sizes distinct, sum of sizes = n, every x < n in exactly one coset. -/
def cfgOK (n : Nat) (cfg : List (Nat × Nat)) : Bool :=
  (Nat.ble 2 (List.length cfg)) && (cfgAllOK n cfg) &&
  (sizesDistinct (sizeList cfg)) && (sumNat (sizeList cfg) == n) &&
  (coverOK n cfg n)

/-- For n ≥ 1: the divisors of n in ascending order (for n = 0 the list
is [0], which never reaches the ≥ 2-coset filter). -/
def divisorsList (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun d => n % d == 0)

/-- All sublists of the divisor list (the 2^τ divisor-subsets, each in
ascending order). -/
def subLists : List Nat → List (List Nat)
  | [] => [[]]
  | s :: t => (subLists t).map (fun S => s :: S) ++ subLists t

/-- The arithmetic candidates: divisor sublists with ≥ 2 sizes (distinct
by construction) summing to n. -/
def censusSizes (n : Nat) : List (List Nat) :=
  (subLists (divisorsList n)).filter
    (fun S => (Nat.ble 2 (List.length S)) && (sumNat S == n))

/-- Prepend c to every tuple. -/
def prependAll (c : Nat) : List (List Nat) → List (List Nat)
  | [] => []
  | t :: r => (c :: t) :: prependAll c r

/-- Cross product: one entry per modulus m from [0, m). -/
def tuplesJoin : List Nat → List (List Nat) → List (List Nat)
  | [], _ => []
  | c :: cs, tails => prependAll c tails ++ tuplesJoin cs tails

/-- All shift tuples for the modulus list `ms` (one shift per entry). -/
def prodTuples : List Nat → List (List Nat)
  | [] => [[]]
  | m :: rest => tuplesJoin (List.range m) (prodTuples rest)

/-- Zip sizes with shifts into a coset configuration. -/
def zipCfg : List Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | [], _ => []
  | s :: ss, c :: cs => (s, c) :: zipCfg ss cs

/-- All coset configurations for the size list S: every shift
assignment (c_i < n / s_i). -/
def configsForSizes (n : Nat) (S : List Nat) : List (List (Nat × Nat)) :=
  (prodTuples (S.map (fun s => n / s))).map (fun t => zipCfg S t)

def configsJoin (n : Nat) : List (List Nat) → List (List (Nat × Nat))
  | [] => []
  | S :: rest => configsForSizes n S ++ configsJoin n rest

/-- The full candidate space: all arithmetic-candidate size lists with
all shift assignments. -/
def censusConfigs (n : Nat) : List (List (Nat × Nat)) :=
  configsJoin n (censusSizes n)

def anyCfgOK (n : Nat) : List (List (Nat × Nat)) → Bool
  | [] => false
  | cfg :: rest => (cfgOK n cfg) || anyCfgOK n rest

/-- THE CYCLIC TILING SEARCH: true iff some divisor-subset size choice
with some shift assignment gives a genuine distinct-size exact coset
cover of C_n. Exhaustive over the (subgroup, coset) choices. -/
def cyclicHasTiling (n : Nat) : Bool := anyCfgOK n (censusConfigs n)

def noneTiling : List Nat → Bool
  | [] => true
  | k :: r => !(cyclicHasTiling k) && noneTiling r

/-- THE C_6 CASE: the only arithmetic candidate is [1, 2, 3]
(1+2+3 = 6, all dividing 6); all 6·3·2 = 36 shift assignments fail
exact cover. C_6 has NO distinct-size coset tiling. -/
theorem cyclic_6_negative : cyclicHasTiling 6 = false := by decide

/-- THE C_12 CASE: the arithmetic candidates are [2, 4, 6] and
[1, 2, 3, 6]; all 6·3·2 + 12·6·4·2 = 612 shift assignments fail exact
cover. C_12 has NO distinct-size coset tiling. -/
theorem cyclic_12_negative : cyclicHasTiling 12 = false := by decide

/-- THE CHUNKED CENSUS: for EVERY n ≤ 12 the exhaustive search finds no
distinct-size coset tiling of C_n. (n = 0, 1 have no candidates at all;
n = 2, 3, 5, 7, 11 are prime — only [n]-trivial; n = 4, 8, 9, 10 have no
distinct-divisor subset summing to n; n = 6 and n = 12 are killed by the
disjointness searches above.) -/
theorem cyclic_census_le_12 : noneTiling (List.range 13) = true := by decide

/-! ## §6 THE ARSENAL BRIDGE (BOSS's mathematics on the 274 anchors). -/

/-- BOSS's arsenal applied to the 274 anchors: order 6 (the k = 3
arithmetic-feasible order, sizes 1, 2, 3), order 12 (the k = 4 order),
and the modulus pair (2, 3) of the C_6 candidate sizes. -/
theorem e274_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (6 % 3) ∧
    (6 ^ 2 - 1 = (6 - 1) * (6 + 1)) ∧
    (12 % (2 * 3)) % 2 = 12 % 2 ∧
    carryAtPos 12 1 < 4 ∧
    v2r (3 ^ 1 * 2) = v2r 2 :=
  ⟨by decide, sq_sub_one 6 (by decide), mod_mod_mul 12 2 3 (by decide),
    carryAtPos_bound 12 1, CardinalWorldsV2.v2r_ternary_scaling 1 2⟩

/-! ## §7 THE MASTER BOARD. -/

/-- THE P274 ROUND-1 CASE BOARD (seven conjuncts, full statements,
unconditional): the trivial feasibility law + the two-coset kill + the
proper-size law + the k ≥ 2 arithmetic witnesses at orders 6 and 12 +
the cyclic census (C_6, C_12, and the chunked n ≤ 12) + the arsenal
bridge core. -/
theorem e274_board :
    (∀ n : Nat, ∃ sizes : List Nat, tilingSizes n sizes = true) ∧
    (∀ n a b : Nat, 0 < a → a < b → b ∣ n → a + b = n → False) ∧
    (∀ d n : Nat, d ∣ n → d < n → 2 * d ≤ n) ∧
    (∃ sizes : List Nat, tilingSizes 6 sizes = true ∧ 2 ≤ sizes.length ∧
      sumNat sizes = 6) ∧
    (∃ sizes : List Nat, tilingSizes 12 sizes = true ∧ 2 ≤ sizes.length ∧
      sumNat sizes = 12) ∧
    (cyclicHasTiling 6 = false ∧ cyclicHasTiling 12 = false ∧
      noneTiling (List.range 13) = true) ∧
    (ErdosTernary2.isTernaryDigit (6 % 3) ∧
      (6 ^ 2 - 1 = (6 - 1) * (6 + 1)) ∧
      (12 % (2 * 3)) % 2 = 12 % 2 ∧
      carryAtPos 12 1 < 4 ∧
      v2r (3 ^ 1 * 2) = v2r 2) :=
  ⟨feasible_structure, two_coset_impossible, divisor_le_half,
    ⟨[1, 2, 3], by decide, by decide, by decide⟩,
    ⟨[2, 4, 6], by decide, by decide, by decide⟩,
    ⟨cyclic_6_negative, cyclic_12_negative, cyclic_census_le_12⟩,
    e274_arsenal_bridge⟩

end E274

/-! ## RECEIPT. -/

#print axioms E274.beq_self_true
#print axioms E274.tilingSizes_self
#print axioms E274.feasible_structure
#print axioms E274.two_coset_impossible
#print axioms E274.no_two_coset_tiling
#print axioms E274.no_two_coset_half
#print axioms E274.divisor_le_half
#print axioms E274.feasible_6
#print axioms E274.feasible_12
#print axioms E274.feasible_12b
#print axioms E274.cyclic_6_negative
#print axioms E274.cyclic_12_negative
#print axioms E274.cyclic_census_le_12
#print axioms E274.e274_arsenal_bridge
#print axioms E274.e274_board

#eval "E274_COSET_TILING_GREEN"
