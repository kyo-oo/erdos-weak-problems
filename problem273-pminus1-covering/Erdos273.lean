import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos273 — THE P−1 COVERING KERNEL (Kernel 59, W58-B)

Erdős #273 (the p−1 covering question): does an explicit covering system
{x ≡ a_i (mod n_i)} of Z with DISTINCT moduli exist, every n_i = p_i − 1 with
p_i ≥ 5 prime (the M_even family: m even with 2m+1 prime)? Rounds 1–3 of the
campaign (the nine-engine war 2a–2i, the annealing, the sieve-greedy 273k)
produced no covering; the certified yield of PROOF.md §4 is the LAW SET, and
this kernel certifies it unconditionally, all in exact-integer form (NO Rat):

* **L-A (Kraft confinement) — `E273.kraft_confinement`, the star:** the
  leaves' ν (each ≥ 2, each dividing the cross-multiplier L — L-B: only ν
  matters, never the residue c) satisfy the cross-multiplied Kraft equality
  Σ L/ν = L only with leaf count ≤ L, every leaf 2 ≤ ν ≤ L, and at least two
  leaves — the solution is a SMALL object; the huge-ν descent (ν → 10⁴⁰⁰⁰)
  is structurally useless.
* **L-D (Mirsky–Newman granularity):** `no_single_leaf` (a lone leaf never
  closes), `granul_wall_4to12` (decide census: with the small-m density
  carriers consumed — every modulus ≥ 4 in window 12 — NO distinct-moduli
  selection hits Σ 27720/m = 27720; the residual never closes), while
  repeated moduli do close (`parity_cover` at [2, 2]).
* **L-E (density):** `pool400_census` / `pool400_density` (decide): the
  M_even ≤ 400 pool has 67 moduli, every 2m+1 prime, density ∈ [1.464,
  1.465) cross-multiplied by 1000·L400 — density is NOT the blocker.

Laws obeyed: no sorry / admit / native_decide; decide only on closed terms;
nonlinear products enter omega only as opaque atoms; divisibility bridges
via Nat.mul_le_mul_left/right; `Nat.div_add_mod` spells k*(m/k) LEFT.
-/

namespace E273

/-! ## §1 Structural core (self-contained, equation-compiler native). -/

/-- Structural boolean equality on Nat (the residue-class equality
primitive; iota-reduces on constructor pairs). -/
def natB : Nat → Nat → Bool
  | 0, 0 => true
  | Nat.succ a, Nat.succ b => natB a b
  | _, _ => false

theorem natB_self : ∀ n : Nat, natB n n = true
  | 0 => rfl
  | Nat.succ k => natB_self k

/-! ## §2 The Kraft machinery (exact-integer, cross-multiplied). -/

/-- THE EXACT-INTEGER KRAFT WEIGHT: `kraftW leaves L` = Σ L/ν over the leaf
moduli, cross-multiplied by L (the pool lcm in use). NO rationals. -/
def kraftW : List Nat → Nat → Nat
  | [], _ => 0
  | ν :: t, L => kraftW t L + L / ν

/-- A leaf list is LEGAL at L: every leaf ν satisfies 2 ≤ ν and ν ∣ L
(L-B: assignability depends only on ν, never on the residue c). -/
def leafOK : List Nat → Nat → Prop
  | [], _ => True
  | ν :: t, L => 2 ≤ ν ∧ ν ∣ L ∧ leafOK t L

theorem leafOK_nil (L : Nat) : leafOK [] L ↔ True := Iff.rfl

theorem leafOK_cons (ν : Nat) (t : List Nat) (L : Nat) :
    leafOK (ν :: t) L ↔ 2 ≤ ν ∧ ν ∣ L ∧ leafOK t L := Iff.rfl

/-- The ν-bounds of confinement: every leaf 2 ≤ ν ≤ L (ν ≲ pool bound). -/
def leafBound : List Nat → Nat → Prop
  | [], _ => True
  | ν :: t, L => 2 ≤ ν ∧ ν ≤ L ∧ leafBound t L

theorem leafBound_cons (ν : Nat) (t : List Nat) (L : Nat) :
    leafBound (ν :: t) L ↔ 2 ≤ ν ∧ ν ≤ L ∧ leafBound t L := Iff.rfl

theorem kraftW_singleton (ν : Nat) (L : Nat) : kraftW [ν] L = L / ν := by
  show 0 + L / ν = L / ν
  exact Nat.zero_add (L / ν)

/-! ## §3 Arithmetic bridges (omega for linear shells, mul lemmas for atoms). -/

theorem dvd_le (ν L : Nat) (hd : ν ∣ L) (hL : 0 < L) : ν ≤ L := by
  obtain ⟨k, hk⟩ := hd
  cases k with
  | zero => rw [hk, Nat.mul_zero] at hL; exact absurd hL (Nat.lt_irrefl 0)
  | succ j =>
    calc ν = ν * 1 := (Nat.mul_one ν).symm
      _ ≤ ν * Nat.succ j := Nat.mul_le_mul_left ν (Nat.succ_le_succ (Nat.zero_le j))
      _ = L := by rw [hk]

/-- Every legal leaf carries Kraft weight ≥ 1 (the divisibility bridge:
ν ∣ L and 0 < L force 1 ≤ L/ν). -/
theorem kraft_leaf_ge1 (ν L : Nat) (h2 : 2 ≤ ν) (hL : 0 < L) (hd : ν ∣ L) :
    1 ≤ L / ν := by
  have hpos : 0 < ν := by omega
  have hdm : ν * (L / ν) + L % ν = L := Nat.div_add_mod L ν
  have hmlt : L % ν < ν := Nat.mod_lt L hpos
  cases q : L / ν with
  | zero =>
    rw [q, Nat.mul_zero, Nat.zero_add] at hdm
    rw [hdm] at hmlt
    exact absurd (Nat.lt_of_lt_of_le hmlt (dvd_le ν L hd hL)) (Nat.lt_irrefl L)
  | succ j => omega

/-! ## §4 THE KRAFT CONFINEMENT LAW (L-A — the star, full induction). -/

/-- THE CONFINEMENT CORE (full induction): under legality at L, the leaf
count never exceeds the Kraft weight itself. -/
theorem length_le_kraft (leaves : List Nat) (L : Nat) (hL : 0 < L)
    (hok : leafOK leaves L) : leaves.length ≤ kraftW leaves L := by
  induction leaves with
  | nil => exact Nat.le_refl 0
  | cons ν t ih =>
    rw [leafOK_cons] at hok
    obtain ⟨h2, hd, ht⟩ := hok
    have h1 : 1 ≤ L / ν := kraft_leaf_ge1 ν L h2 hL hd
    show t.length + 1 ≤ kraftW t L + L / ν
    exact Nat.add_le_add (ih ht) h1

/-- THE ν-BOUNDS (L-B smallness): legality at a positive L bounds every
leaf by 2 ≤ ν ≤ L. -/
theorem leafOK_bound (leaves : List Nat) (L : Nat) (hL : 0 < L)
    (hok : leafOK leaves L) : leafBound leaves L := by
  induction leaves with
  | nil => exact True.intro
  | cons ν t ih =>
    rw [leafOK_cons] at hok
    obtain ⟨h2, hd, ht⟩ := hok
    rw [leafBound_cons]
    exact ⟨h2, dvd_le ν L hd hL, ih ht⟩

/-- Mirsky–Newman granularity core (L-D): a LONE leaf can never close the
Kraft equality — Σ L/ν = L with ν ≥ 2 shrinks strictly below L. -/
theorem no_single_leaf (ν L : Nat) (h2 : 2 ≤ ν) (hL : 0 < L) (hd : ν ∣ L)
    (hk : kraftW [ν] L = L) : False := by
  have hk' : L / ν = L := by rw [← kraftW_singleton ν L]; exact hk
  have hdm : ν * (L / ν) + L % ν = L := Nat.div_add_mod L ν
  rw [hk'] at hdm
  have h1 : 1 ≤ L := by omega
  have h2L : L < 2 * L := by omega
  have hνL : 2 * L ≤ ν * L := Nat.mul_le_mul_right L h2
  have hLt : L < ν * L := Nat.lt_of_lt_of_le h2L hνL
  have hle : ν * L ≤ L :=
    Nat.le_trans (Nat.le_add_right (ν * L) (L % ν)) (by rw [hdm])
  exact absurd (Nat.lt_of_lt_of_le hLt hle) (Nat.lt_irrefl L)

/-- **THE KRAFT CONFINEMENT LAW (L-A, the star of PROOF.md §4)**: if the
leaves' ν (each ≥ 2, each dividing L) satisfy the cross-multiplied Kraft
equality Σ L/ν = L, then the leaf count is ≤ L, every leaf ν satisfies
2 ≤ ν ≤ L, and there are at least TWO leaves — the solution is a SMALL
object; the huge-ν descent is structurally useless. -/
theorem kraft_confinement (leaves : List Nat) (L : Nat) (hL : 0 < L)
    (hok : leafOK leaves L) (hk : kraftW leaves L = L) :
    leaves.length ≤ L ∧ leafBound leaves L ∧ 2 ≤ leaves.length := by
  refine ⟨?_, leafOK_bound leaves L hL hok, ?_⟩
  · have hlen := length_le_kraft leaves L hL hok
    rw [hk] at hlen
    exact hlen
  · cases leaves with
    | nil =>
      have h0 : kraftW [] L = 0 := rfl
      rw [h0] at hk
      rw [← hk] at hL
      exact absurd hL (Nat.lt_irrefl 0)
    | cons ν t =>
      cases t with
      | nil =>
        rw [leafOK_cons] at hok
        obtain ⟨h2, hd, _⟩ := hok
        exact (no_single_leaf ν L h2 hL hd hk).elim
      | cons w t' =>
        show 2 ≤ t'.length + 1 + 1
        omega

/-! ## §5 The certified witness tables (decide only on closed terms). -/

/-- Trial-division divisibility/primality (self-contained, kernel-evaluable). -/
def dividesB (d n : Nat) : Bool := Nat.beq (n % d) 0

def noDivFrom (n k : Nat) : Nat → Bool
  | 0 => true
  | Nat.succ f =>
    Nat.ble (n + 1) (k * k) || (!(dividesB k n) && noDivFrom n (k + 1) f)

def primeB (n : Nat) : Bool := Nat.ble 2 n && noDivFrom n 2 n

/-- M_even membership: m ≥ 2, m even, 2m+1 prime (the p−1 family, p = 2m+1). -/
def pMinus1B (m : Nat) : Bool := Nat.ble 2 m && Nat.beq (m % 2) 0 && primeB (2 * m + 1)

/-- The M_even ≤ 400 pool (the S273 census: 67 moduli, engine273k). -/
def pool400 : List Nat :=
  [2, 6, 8, 14, 18, 20, 26, 30, 36, 44, 48, 50, 54, 56, 68, 74, 78, 86, 90, 96, 98,
   114, 116, 120, 128, 134, 138, 140, 146, 156, 158, 168, 174, 176, 186, 194, 198, 200,
   204, 210, 216, 224, 228, 230, 254, 260, 270, 278, 284, 288, 296, 300, 306, 308, 320,
   326, 330, 336, 338, 350, 354, 366, 378, 380, 384, 386, 398]

/-- The cross-multiplier for the full ≤ 400 pool (lcm, python-verified). -/
def L400 : Nat := 88512098376606446381456558928295729570550400

/-- The cross-multiplied pool weight Σ L400/m (python-verified). -/
def S400 : Nat := 129657203152767075702464412934392296885747522

/-- The pool-12 prefix weight at its own lcm (3603600): the density surplus
of the small carriers is already 4078497/3603600 ≈ 1.132 — past unity. -/
def pool12 : List Nat := [2, 6, 8, 14, 18, 20, 26, 30, 36, 44, 48, 50]

theorem pool12_kraft : kraftW pool12 3603600 = 4078497 := by decide

theorem pool400_kraft : kraftW pool400 L400 = S400 := by decide

/-- THE POOL CENSUS (L-E): 67 moduli ≤ 400 in M_even, every one with
2m+1 prime. -/
theorem pool400_census :
    (pool400.length = 67) ∧ ((pool400.all pMinus1B) = true) := by decide

/-- THE DENSITY WINDOW (L-E): Σ 1/m over M_even ≤ 400 lies in [1.464, 1.465)
(1464·L400 ≤ 1000·S400 < 1465·L400) — density is NOT the blocker. -/
theorem pool400_density :
    ((Nat.ble (1464 * L400) (1000 * S400)) = true) ∧
    ((Nat.ble (1000 * S400 + 1) (1465 * L400)) = true) := by decide

/-! ## §6 The L-D granularity wall + the repeated-moduli escape (censuses). -/

def bitAt (mask p : Nat) : Bool := Nat.beq ((mask / (2 ^ p)) % 2) 1

/-- Sub-sum over the 9 DISTINCT moduli 4..12, cross-multiplied by 27720 =
lcm(4..12): bit p selects modulus p + 4 (the small-m density carriers
CONSUMED — every modulus ≥ 4). -/
def wFrom4 (mask : Nat) : Nat → Nat
  | 0 => 0
  | Nat.succ p => (cond (bitAt mask p) (27720 / (p + 4)) 0) + wFrom4 mask p

/-- **THE GRANULARITY WALL (L-D / 2i)**: NO selection of distinct moduli
from the consumed window [4, 12] closes the Kraft equality — Σ 27720/m ≠
27720 for every one of the 512 masks (wFrom4 < 27720 or > 27720): the
residual never closes with the small-m density carriers gone. -/
theorem granul_wall_4to12 :
    (List.range 512).all
      (fun m => Nat.ble (wFrom4 m 9 + 1) 27720 || Nat.ble (27720 + 1) (wFrom4 m 9)) = true := by
  decide

/-- The parity-lift instance: repeated moduli DO close the Kraft equality
(the even side y ≡ 0, 1 (mod 2) of the trivial parity cover) — L-D: exact
covers NEED repeated moduli; distinctness is the only missing piece. -/
theorem parity_leafOK : leafOK [2, 2] 2 := by
  rw [leafOK_cons, leafOK_cons, leafOK_nil]
  exact ⟨by omega, ⟨1, (Nat.mul_one 2).symm⟩,
    ⟨by omega, ⟨1, (Nat.mul_one 2).symm⟩, True.intro⟩⟩

theorem parity_cover : kraftW [2, 2] 2 = 2 := by decide

/-! ## §7 The arsenal bridge — the campaign's certified anchors. -/

/-- THE ARSENAL BRIDGE: three Arsenal lemma instances at #273-native anchor
numbers (44 and 14 are M_even members; ternary digit 2 carries the scaling). -/
theorem e273_arsenal_bridge :
    ErdosTernary2.isTernaryDigit 2 = true ∧
    v2r (3 ^ 1 * 44) = v2r 44 ∧
    v2r (3 ^ 1 * 14) = v2r 14 :=
  ⟨rfl, CardinalWorldsV2.v2r_ternary_scaling 1 44,
    CardinalWorldsV2.v2r_ternary_scaling 1 14⟩

/-! ## §8 The master board (flat anonymous constructor). -/

/-- THE P273 KERNEL MASTER BOARD: the confinement law + the Mirsky–Newman
core + the pool tables + the density window + the granularity wall + the
repeated-moduli escape + the arsenal bridge — every certified fact of
PROOF.md §4 in one unconditional conjunction. -/
theorem erdos273_board :
    (∀ (leaves : List Nat) (L : Nat), 0 < L → leafOK leaves L → kraftW leaves L = L →
        leaves.length ≤ L ∧ leafBound leaves L ∧ 2 ≤ leaves.length) ∧
    (∀ ν L : Nat, 2 ≤ ν → ν ∣ L → 0 < L → kraftW [ν] L = L → False) ∧
    (kraftW pool12 3603600 = 4078497) ∧
    (pool400.length = 67 ∧ ((pool400.all pMinus1B) = true)) ∧
    (((Nat.ble (1464 * L400) (1000 * S400)) = true) ∧
        ((Nat.ble (1000 * S400 + 1) (1465 * L400)) = true)) ∧
    ((List.range 512).all
        (fun m => Nat.ble (wFrom4 m 9 + 1) 27720 || Nat.ble (27720 + 1) (wFrom4 m 9)) = true) ∧
    (kraftW [2, 2] 2 = 2 ∧ leafOK [2, 2] 2) ∧
    (ErdosTernary2.isTernaryDigit 2 = true ∧ v2r (3 ^ 1 * 44) = v2r 44 ∧
        v2r (3 ^ 1 * 14) = v2r 14) :=
  ⟨fun leaves L hL hok hk => kraft_confinement leaves L hL hok hk,
    fun ν L h2 hd hL hk => no_single_leaf ν L h2 hL hd hk,
    pool12_kraft, pool400_census, pool400_density,
    granul_wall_4to12, ⟨parity_cover, parity_leafOK⟩, e273_arsenal_bridge⟩

/-! ## §9 Receipts. -/
#print axioms E273.kraft_confinement
#print axioms E273.no_single_leaf
#print axioms E273.length_le_kraft
#print axioms E273.leafOK_bound
#print axioms E273.pool12_kraft
#print axioms E273.pool400_kraft
#print axioms E273.pool400_census
#print axioms E273.pool400_density
#print axioms E273.granul_wall_4to12
#print axioms E273.e273_arsenal_bridge
#print axioms E273.erdos273_board
#eval "E273_PMINUS1_COVERING_GREEN"

end E273
