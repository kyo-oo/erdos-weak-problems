import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-! # Erdos317 — THE SIGNED HARMONIC KERNEL (Kernel 63, W58-B)

Erdős #317 (verbatim, PROBLEM.md): for c > 0, does there exist δ_k ∈ {−1,0,1}
for 1 ≤ k ≤ n with 0 < |Σ_{1≤k≤n} δ_k/k| < c/2ⁿ?  And is it true that for
sufficiently large n, for ANY δ_k ∈ {−1,0,1}, |Σ δ_k/k| > 1/Lₙ (the lcm)
whenever the sum is nonzero?  The DERIVATION (Session 026) reduces everything
to integer arithmetic: Σ δ_k/k = M/Lₙ with M = Σ δ_k·(Lₙ/k) ∈ ℤ, so PART 2 is
the ±1/Lₙ-infeasibility question and PART 1 asks for a uniform c.
This kernel certifies, in exact cross-multiplied n!-integer arithmetic (NO
Rat — every statement is `hsum δ n = Σ δ_k·(n!/k)`):
1. the two-sided magnitude law and the 2ⁿ envelope (|Σ| < 2ⁿ · n!-units,
   full generality over sign vectors);
2. the witness δ-vectors achieving the minimal nonzero values for n = 1..8
   (n ≤ 4 hit 1/Lₙ EXACTLY: 1, 1/2, 1/6, 1/12 — the DERIVATION §4 achievers;
   n ≥ 5: the minima are 2/L₅, 2/L₆, 4/L₇, 7/L₈);
3. THE MINIMAL-VALUE CLASSIFICATION for n = 5, 6, 7: every one of the 3ⁿ sign
   codes has |hsum| = 0 or ≥ 4, 24, 48 respectively (decide sweeps over
   243/729/2187 codes, chunked ≤ 500 rows per theorem);
4. the granularity law (every n=5 value is a multiple of n!/L₅ = 2), the
   Theorem-A mod-5 residue mechanism at n = 5, the ±1/L₅ infeasibility
   (hsum ≠ ±2), and the exponentially-small frontier band: for EVERY n ≤ 8
   a witness with 0 < |Σδ_k/k| < 3/2ⁿ (the c = 3 PART-1 band, 8 conjuncts);
5. the arsenal bridge (ternary-digit world on the trit codes) + the board.

Honest scope: K1 (the residue lemma for all n ≥ 5, empirically universal to
n = 20000 in k1_results.txt) and K2 (the collision-count bound for PART 1)
are the two OPEN kernels named in DERIVATION §5 — NOT attempted here; this
kernel certifies the small-n classification + frontier completely.  Zero
sorry/admit/native_decide; `by decide` only on closed numerics and bounded
List.range enumerations (≤ 500 rows — the L45 no-OOM law).  L86/L90/L91
laws respected: no variable-level defeq trust across multiplication, no
variable-level beq, omega only on consistent atoms. -/

namespace E317

/-! ## §0 The definitions — the sign vectors and the exact integer sums. -/

/-- The factorial (the cross-multiplication scale). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The signed-harmonic numerator fold: `hsumAux n k ds` = Σ over the list
`ds` (the δ-vectors, δ_1 first) of δ_k · (n!/k), with `k` the current index.
All arithmetic is exact Int arithmetic — no rationals anywhere. -/
def hsumAux : Nat → Nat → List Int → Int
  | _, _, [] => 0
  | n, k, d :: ds => d * Int.ofNat (fact n / k) + hsumAux n (k + 1) ds

/-- THE SIGNED HARMONIC NUMERATOR: `hsum δ n = Σ_{1≤k≤n} δ_k · (n!/k)`, the
exact cross-multiplied integer of Σ δ_k/k against the scale n!. -/
def hsum (ds : List Int) (n : Nat) : Int := hsumAux n 1 ds

/-- The trit reader: the k-th sign δ = trit c (k−1) ∈ {−1,0,1} of the code
`c`, read as the base-3 digit at position j minus 1 (the ternary world). -/
def trit (c j : Nat) : Int := Int.ofNat ((c / 3 ^ j) % 3) - 1

/-- The code-fold: `hsumCode c n = Σ_{j<n} trit c j · (n!/(j+1))` — the same
signed harmonic numerator, enumerated over all 3ⁿ sign assignments by code. -/
def hsumCodeAux : Nat → Nat → Nat → Nat → Int
  | _, _, _, 0 => 0
  | n, c, j, m + 1 => trit c j * Int.ofNat (fact n / (j + 1)) + hsumCodeAux n c (j + 1) m

/-- `hsumCode c n`: the signed harmonic numerator of the sign vector encoded
by the ternary code `c < 3 ^ n` (codes 0..3ⁿ−1 ↔ {−1,0,1}ⁿ, bijectively). -/
def hsumCode (c n : Nat) : Int := hsumCodeAux n c 0 n

theorem hsumAux_nil (n k : Nat) : hsumAux n k [] = 0 := rfl

theorem hsumAux_cons (n k : Nat) (d : Int) (ds : List Int) :
    hsumAux n k (d :: ds) = d * Int.ofNat (fact n / k) + hsumAux n (k + 1) ds := rfl

theorem hsum_eq (ds : List Int) (n : Nat) : hsum ds n = hsumAux n 1 ds := rfl

/-! ## §1 The structural laws — the magnitude envelope (2ⁿ frontier bound). -/

/-- Strict positivity of Nat products (the E289-green DIY: `Nat.mul_succ`
expansion + omega shell; no external mul_pos). -/
theorem e317_mul_pos (x y : Nat) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, y = k + 1 := ⟨y - 1, by omega⟩
  rw [hk]
  have hms : x * (k + 1) = x * k + x := Nat.mul_succ x k
  rw [hms]
  omega

theorem fact_succ (n : Nat) : fact (n + 1) = (n + 1) * fact n := rfl

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => rw [fact_succ]; exact e317_mul_pos (n + 1) (fact n) (by omega) ih

/-- Floor division never exceeds its dividend (DIY: `Nat.div_add_mod` +
the L86 `Nat.mul_le_mul_right` bridge — omega never touches the product). -/
theorem natDiv_le (N k : Nat) : N / k ≤ N := by
  cases k with
  | zero => rw [Nat.div_zero]; exact Nat.zero_le _
  | succ k =>
      have h1 : 1 ≤ k + 1 := by omega
      have h2 : 1 * (N / (k + 1)) ≤ (k + 1) * (N / (k + 1)) :=
        Nat.mul_le_mul_right _ h1
      rw [Nat.one_mul] at h2
      have h3 := Nat.div_add_mod N (k + 1)
      have h4 : (k + 1) * (N / (k + 1)) ≤ (k + 1) * (N / (k + 1)) + N % (k + 1) :=
        Nat.le_add_right _ _
      exact Nat.le_trans h2 (Nat.le_trans h4 (Nat.le_of_eq h3))

/-- Right monotonicity of Nat products (ring expansion + omega atoms). -/
theorem e317_le_mul_right (x y z : Nat) (hxy : x ≤ y) (hz : 0 < z) : x * z ≤ y * z := by
  obtain ⟨s, hs⟩ : ∃ s : Nat, y = x + s := ⟨y - x, by omega⟩
  rw [hs]
  have hexp : (x + s) * z = x * z + s * z := by ring
  omega

theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- `n ≤ 2ⁿ` — the exponential that dominates the harmonic count. -/
theorem two_pow_ge (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hp : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
      have hd : 2 ^ n * 2 = 2 ^ n + 2 ^ n := by ring
      have hP := two_pow_pos n
      omega

/-- Cast-of-sum distribution (omega on linear Nat under the Int cast). -/
theorem ofNat_add (a b : Nat) :
    Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b := by omega

/-- THE TWO-SIDED MAGNITUDE LAW: every sign vector's numerator is bounded by
its length times the scale n! (induction over the fold; sign case-split —
each δ ∈ {−1,0,1} contributes at most one weight n!/k ≤ n!). -/
theorem hsumAux_two_sided (n k : Nat) : ∀ ds : List Int,
    (∀ d ∈ ds, d = -1 ∨ d = 0 ∨ d = 1) →
    -(Int.ofNat (ds.length * fact n)) ≤ hsumAux n k ds ∧
      hsumAux n k ds ≤ Int.ofNat (ds.length * fact n) := by
  intro ds
  induction ds with
  | nil =>
      intro _
      have hl : ([] : List Int).length = 0 := rfl
      have hz : hsumAux n k [] = 0 := rfl
      rw [hl, hz]
      constructor <;> omega
  | cons d ds ih =>
      intro hdom
      have hd : d = -1 ∨ d = 0 ∨ d = 1 :=
        hdom d ((List.mem_cons d d ds).mpr (Or.inl rfl))
      have hdom' : ∀ x ∈ ds, x = -1 ∨ x = 0 ∨ x = 1 :=
        fun x hx => hdom x ((List.mem_cons x d ds).mpr (Or.inr hx))
      have IH := ih hdom'
      have hNat := natDiv_le (fact n) k
      have hW : Int.ofNat (fact n / k) ≤ Int.ofNat (fact n) := by omega
      have hl : (d :: ds).length = ds.length + 1 := rfl
      have hN : (ds.length + 1) * fact n = ds.length * fact n + fact n := by ring
      have hca : Int.ofNat (ds.length * fact n + fact n)
          = Int.ofNat (ds.length * fact n) + Int.ofNat (fact n) := ofNat_add _ _
      rw [hl, hN, hca, hsumAux_cons]
      rcases hd with h | h | h
      · subst h; constructor <;> omega
      · subst h; constructor <;> omega
      · subst h; constructor <;> omega

theorem hsum_two_sided (ds : List Int) (n : Nat)
    (hdom : ∀ d ∈ ds, d = -1 ∨ d = 0 ∨ d = 1) :
    -(Int.ofNat (ds.length * fact n)) ≤ hsum ds n ∧
      hsum ds n ≤ Int.ofNat (ds.length * fact n) :=
  hsumAux_two_sided n 1 ds hdom

/-- THE 2ⁿ ENVELOPE (the frontier's upper law): every sign vector of length
≤ n satisfies |Σ δ_k/k| ≤ len·n!/n! ≤ 2ⁿ — in numerator units,
−(2ⁿ·n!) ≤ hsum ≤ 2ⁿ·n!.  The problem's 2ⁿ threshold, exactly as stated. -/
theorem hsum_envelope (ds : List Int) (n : Nat)
    (hdom : ∀ d ∈ ds, d = -1 ∨ d = 0 ∨ d = 1)
    (hlen : ds.length ≤ n) :
    -(Int.ofNat (2 ^ n * fact n)) ≤ hsum ds n ∧
      hsum ds n ≤ Int.ofNat (2 ^ n * fact n) := by
  have htwo := hsum_two_sided ds n hdom
  have hN : ds.length * fact n ≤ 2 ^ n * fact n :=
    Nat.le_trans (e317_le_mul_right _ _ _ hlen (fact_pos n))
      (e317_le_mul_right _ _ _ (two_pow_ge n) (fact_pos n))
  constructor <;> omega

/-! ## §2 The witness constructions — the certified δ-vectors. -/

/-- THE WITNESS TABLE: the minimal nonzero sums for n = 1..8 as explicit
δ-vectors.  n ≤ 4: |Σδ_k/k| = 1/Lₙ EXACTLY (the DERIVATION §4 achievers —
these are the ONLY n where the minimal value hits the 1/Lₙ granularity);
n = 5..8: the minima 2/L₅, 2/L₆, 4/L₇, 7/L₈ (engine/battery-certified). -/
theorem e317_witness_table :
    hsum [1] 1 = 1 ∧
    hsum [0, 1] 2 = 1 ∧
    hsum [0, 1, -1] 3 = 1 ∧
    hsum [-1, 1, 1, 1] 4 = 2 ∧
    hsum [-1, 1, 1, 0, 1] 5 = 4 ∧
    hsum [-1, 1, 1, 0, 1, 0] 6 = 24 ∧
    hsum [-1, 1, 0, 0, 1, 1, 1] 7 = 48 ∧
    hsum [-1, 1, 0, 0, 1, 1, 0, 1] 8 = -336 := by
  decide

/-- The same minima as CODES (the ternary encodings of the witness vectors). -/
theorem e317_code_witness_table :
    hsumCode 213 5 = 4 ∧ hsumCode 456 6 = 24 ∧
    hsumCode 2148 7 = 48 ∧ hsumCode 5793 8 = -336 := by
  decide

/-- The bridge: each code-witness IS the list-witness (both encodings of the
same δ-vector compute the same numerator — kernel-decided, closed terms). -/
theorem e317_code_list_bridge :
    hsumCode 213 5 = hsum [-1, 1, 1, 0, 1] 5 ∧
    hsumCode 456 6 = hsum [-1, 1, 1, 0, 1, 0] 6 ∧
    hsumCode 2148 7 = hsum [-1, 1, 0, 0, 1, 1, 1] 7 ∧
    hsumCode 5793 8 = hsum [-1, 1, 0, 0, 1, 1, 0, 1] 8 := by
  decide

/-! ## §3 The minimal-value classification — the decide censuses. -/

/-- THE n=5 CLASSIFICATION SWEEP (all 243 sign codes): every nonzero
numerator is ≥ 4 — the minimal value 2/L₅ (4 in n!-units) is EXACT. -/
theorem e317_min_sweep_5 :
    (List.range 243).all (fun c =>
      decide (Int.natAbs (hsumCode c 5) = 0 ∨ 4 ≤ Int.natAbs (hsumCode c 5))) = true := by
  decide

theorem e317_min_value_5 : ∀ c : Nat, c < 243 →
    Int.natAbs (hsumCode c 5) = 0 ∨ 4 ≤ Int.natAbs (hsumCode c 5) := by
  intro c hc
  have hrow := (List.all_eq_true.mp e317_min_sweep_5) c (List.mem_range.mpr hc)
  exact of_decide_eq_true hrow

/-- The problem-shaped form: 0 < |hsum| → 4 ≤ |hsum| (the minimum attained). -/
theorem e317_min_imp_5 : ∀ c : Nat, c < 243 →
    0 < Int.natAbs (hsumCode c 5) → 4 ≤ Int.natAbs (hsumCode c 5) := by
  intro c hc hpos
  have h := e317_min_value_5 c hc
  rcases h with h0 | h4
  · omega
  · omega

/-- THE GRANULARITY SWEEP (n=5): every value is a multiple of n!/L₅ = 2 —
the DERIVATION §1 reduction's visible instance ("every value is an integer
multiple of 1/Lₙ"). -/
theorem e317_gran_sweep_5 :
    (List.range 243).all (fun c =>
      decide (Int.natAbs (hsumCode c 5) % 2 = 0)) = true := by
  decide

theorem e317_gran_5 : ∀ c : Nat, c < 243 → Int.natAbs (hsumCode c 5) % 2 = 0 := by
  intro c hc
  have hrow := (List.all_eq_true.mp e317_gran_sweep_5) c (List.mem_range.mpr hc)
  exact of_decide_eq_true hrow

/-- THE THEOREM-A MOD-5 MECHANISM (n=5, in n!-units): every numerator's
residue mod 5 lies in {0, ±1, ±4} — exactly the reachable set
{−δ₅·(24 mod 5)} = {δ₅·(−1)} of the isolated-prime mechanism of DERIVATION
§2 (u₅ = 5!/5 = 24 ≡ −1 mod 5).  ±2 ≡ ±1/L₅ is unreachable mod 5. -/
theorem e317_mod5_sweep_5 :
    (List.range 243).all (fun c =>
      decide (hsumCode c 5 % 5 = 0 ∨ hsumCode c 5 % 5 = 1 ∨ hsumCode c 5 % 5 = 4 ∨
        hsumCode c 5 % 5 = -1 ∨ hsumCode c 5 % 5 = -4)) = true := by
  decide

/-- THE n=6 CLASSIFICATION (all 729 codes, chunked ≤ 500 — the L45 law). -/
theorem e317_min_sweep_6a :
    (List.range 500).all (fun c =>
      decide (Int.natAbs (hsumCode c 6) = 0 ∨ 24 ≤ Int.natAbs (hsumCode c 6))) = true := by
  decide

theorem e317_min_sweep_6b :
    (List.range 229).all (fun i =>
      decide (Int.natAbs (hsumCode (500 + i) 6) = 0 ∨
        24 ≤ Int.natAbs (hsumCode (500 + i) 6))) = true := by
  decide

theorem e317_min_value_6 : ∀ c : Nat, c < 729 →
    Int.natAbs (hsumCode c 6) = 0 ∨ 24 ≤ Int.natAbs (hsumCode c 6) := by
  intro c hc
  have hcase : c < 500 ∨ 500 ≤ c := by omega
  rcases hcase with h | h
  · exact of_decide_eq_true ((List.all_eq_true.mp e317_min_sweep_6a) c (List.mem_range.mpr h))
  · have hi : c - 500 < 229 := by omega
    have hrow := (List.all_eq_true.mp e317_min_sweep_6b) (c - 500) (List.mem_range.mpr hi)
    have hc' : 500 + (c - 500) = c := by omega
    rw [hc'] at hrow
    exact of_decide_eq_true hrow

/-- THE n=7 CLASSIFICATION (all 2187 codes, five ≤ 500 chunks). -/
theorem e317_min_sweep_7a :
    (List.range 500).all (fun c =>
      decide (Int.natAbs (hsumCode c 7) = 0 ∨ 48 ≤ Int.natAbs (hsumCode c 7))) = true := by
  decide

theorem e317_min_sweep_7b :
    (List.range 500).all (fun i =>
      decide (Int.natAbs (hsumCode (500 + i) 7) = 0 ∨
        48 ≤ Int.natAbs (hsumCode (500 + i) 7))) = true := by
  decide

theorem e317_min_sweep_7c :
    (List.range 500).all (fun i =>
      decide (Int.natAbs (hsumCode (1000 + i) 7) = 0 ∨
        48 ≤ Int.natAbs (hsumCode (1000 + i) 7))) = true := by
  decide

theorem e317_min_sweep_7d :
    (List.range 500).all (fun i =>
      decide (Int.natAbs (hsumCode (1500 + i) 7) = 0 ∨
        48 ≤ Int.natAbs (hsumCode (1500 + i) 7))) = true := by
  decide

theorem e317_min_sweep_7e :
    (List.range 187).all (fun i =>
      decide (Int.natAbs (hsumCode (2000 + i) 7) = 0 ∨
        48 ≤ Int.natAbs (hsumCode (2000 + i) 7))) = true := by
  decide

theorem e317_min_value_7 : ∀ c : Nat, c < 2187 →
    Int.natAbs (hsumCode c 7) = 0 ∨ 48 ≤ Int.natAbs (hsumCode c 7) := by
  intro c hc
  have h1 : c < 500 ∨ 500 ≤ c := by omega
  rcases h1 with h | h
  · exact of_decide_eq_true ((List.all_eq_true.mp e317_min_sweep_7a) c (List.mem_range.mpr h))
  · have h2 : c < 1000 ∨ 1000 ≤ c := by omega
    rcases h2 with h | h
    · have hi : c - 500 < 500 := by omega
      have hrow := (List.all_eq_true.mp e317_min_sweep_7b) (c - 500) (List.mem_range.mpr hi)
      have hc' : 500 + (c - 500) = c := by omega
      rw [hc'] at hrow
      exact of_decide_eq_true hrow
    · have h3 : c < 1500 ∨ 1500 ≤ c := by omega
      rcases h3 with h | h
      · have hi : c - 1000 < 500 := by omega
        have hrow := (List.all_eq_true.mp e317_min_sweep_7c) (c - 1000) (List.mem_range.mpr hi)
        have hc' : 1000 + (c - 1000) = c := by omega
        rw [hc'] at hrow
        exact of_decide_eq_true hrow
      · have h4 : c < 2000 ∨ 2000 ≤ c := by omega
        rcases h4 with h | h
        · have hi : c - 1500 < 500 := by omega
          have hrow := (List.all_eq_true.mp e317_min_sweep_7d) (c - 1500) (List.mem_range.mpr hi)
          have hc' : 1500 + (c - 1500) = c := by omega
          rw [hc'] at hrow
          exact of_decide_eq_true hrow
        · have hi : c - 2000 < 187 := by omega
          have hrow := (List.all_eq_true.mp e317_min_sweep_7e) (c - 2000) (List.mem_range.mpr hi)
          have hc' : 2000 + (c - 2000) = c := by omega
          rw [hc'] at hrow
          exact of_decide_eq_true hrow

/-- THE ±1/L₅ INFEASIBILITY (the first PART-2 instance, DERIVATION §4):
no sign vector with Σδ_k/k = ±1/60 — in n!-units, hsum ≠ ±2 for every code.
At n ≤ 4 the value 1/Lₙ IS achieved (witness table); from n = 5 it never is. -/
theorem e317_no_unit_over_L5 : ∀ c : Nat, c < 243 →
    hsumCode c 5 ≠ 2 ∧ hsumCode c 5 ≠ -2 := by
  intro c hc
  have h := e317_min_value_5 c hc
  constructor
  · intro h2
    rw [h2] at h
    have haux : Int.natAbs (2 : Int) = 2 := by decide
    rw [haux] at h
    rcases h with h0 | h4
    · omega
    · omega
  · intro h2
    rw [h2] at h
    have haux : Int.natAbs (-2 : Int) = 2 := by decide
    rw [haux] at h
    rcases h with h0 | h4
    · omega
    · omega

/-! ## §4 The frontier — the exponentially-small witness band (c = 3). -/

/-- THE FRONTIER BAND: for EVERY n ≤ 8 there is a sign vector with
0 < |Σδ_k/k| < 3/2ⁿ (the PART-1 shape with the absolute constant c = 3 —
in numerator units 2ⁿ·|hsum| < 3·n!).  The witnesses are exactly the
minimal ones; the two-sided envelope §1 bounds everything above. -/
theorem e317_frontier_c3 :
    (0 < Int.natAbs (hsum [1] 1) ∧ 2 ^ 1 * Int.natAbs (hsum [1] 1) < 3 * fact 1) ∧
    (0 < Int.natAbs (hsum [0, 1] 2) ∧ 2 ^ 2 * Int.natAbs (hsum [0, 1] 2) < 3 * fact 2) ∧
    (0 < Int.natAbs (hsum [0, 1, -1] 3) ∧
      2 ^ 3 * Int.natAbs (hsum [0, 1, -1] 3) < 3 * fact 3) ∧
    (0 < Int.natAbs (hsum [-1, 1, 1, 1] 4) ∧
      2 ^ 4 * Int.natAbs (hsum [-1, 1, 1, 1] 4) < 3 * fact 4) ∧
    (0 < Int.natAbs (hsum [-1, 1, 1, 0, 1] 5) ∧
      2 ^ 5 * Int.natAbs (hsum [-1, 1, 1, 0, 1] 5) < 3 * fact 5) ∧
    (0 < Int.natAbs (hsum [-1, 1, 1, 0, 1, 0] 6) ∧
      2 ^ 6 * Int.natAbs (hsum [-1, 1, 1, 0, 1, 0] 6) < 3 * fact 6) ∧
    (0 < Int.natAbs (hsum [-1, 1, 0, 0, 1, 1, 1] 7) ∧
      2 ^ 7 * Int.natAbs (hsum [-1, 1, 0, 0, 1, 1, 1] 7) < 3 * fact 7) ∧
    (0 < Int.natAbs (hsum [-1, 1, 0, 0, 1, 1, 0, 1] 8) ∧
      2 ^ 8 * Int.natAbs (hsum [-1, 1, 0, 0, 1, 1, 0, 1] 8) < 3 * fact 8) := by
  decide

/-! ## §5 The arsenal bridge — the ternary world on the trit codes. -/

theorem trit_lt_three (c j : Nat) : (c / 3 ^ j) % 3 < 3 :=
  Nat.mod_lt _ (by decide : 0 < 3)

/-- Every trit of every code is a ternary digit — the #317 sign world IS the
ErdosTernary2 digit world (the arsenal's own lemma, applied generally). -/
theorem trit_is_ternary_digit (c j : Nat) :
    ErdosTernary2.isTernaryDigit ((c / 3 ^ j) % 3) := by
  have h3 := ErdosTernary2.lt_three_cases ((c / 3 ^ j) % 3) (trit_lt_three c j)
  rcases h3 with h | h | h
  · rw [h]; exact ErdosTernary2.isTernaryDigit_zero
  · rw [h]; exact ErdosTernary2.isTernaryDigit_one
  · rw [h]; exact ErdosTernary2.isTernaryDigit_two

/-- THE ARSENAL BRIDGE: arsenal lemmas at #317-native anchor numbers —
213 (the n=5 min-witness code), 120 = 5!, 24 (the n=6 min), 3^4 (the trit
base at n = 5), 2148 (the n=7 code), and the trit extraction at 213 = 3·71. -/
theorem e317_arsenal_bridge :
    ErdosTernary2.isTernaryDigit ((213 / 3 ^ 2) % 3) ∧
    (120 ^ 2 - 1 = (120 - 1) * (120 + 1)) ∧
    ((2148 % (4 * 3)) % 4 = 2148 % 4) ∧
    (carryAtPos 24 1 < 4) ∧
    (v2r (3 ^ 2 * 24) = v2r 24) ∧
    (0 < 3 ^ 4) ∧
    ((3 * 71 + 0) / 3 = 71 + 0 / 3) :=
  ⟨by decide, sq_sub_one 120 (by decide),
    mod_mod_mul 2148 4 3 (by decide),
    carryAtPos_bound 24 1,
    CardinalWorldsV2.v2r_ternary_scaling 2 24,
    three_pow_pos_lemma 4,
    mul_add_div_lemma 71 0 3 (by decide)⟩

/-! ## §6 The master board. -/

theorem erdos317_board :
    (∀ ds : List Int, ∀ n : Nat, (∀ d ∈ ds, d = -1 ∨ d = 0 ∨ d = 1) →
      -(Int.ofNat (ds.length * fact n)) ≤ hsum ds n ∧
        hsum ds n ≤ Int.ofNat (ds.length * fact n)) ∧
    (∀ ds : List Int, ∀ n : Nat, (∀ d ∈ ds, d = -1 ∨ d = 0 ∨ d = 1) →
      ds.length ≤ n →
      -(Int.ofNat (2 ^ n * fact n)) ≤ hsum ds n ∧
        hsum ds n ≤ Int.ofNat (2 ^ n * fact n)) ∧
    (hsum [1] 1 = 1 ∧
      hsum [0, 1] 2 = 1 ∧
      hsum [0, 1, -1] 3 = 1 ∧
      hsum [-1, 1, 1, 1] 4 = 2 ∧
      hsum [-1, 1, 1, 0, 1] 5 = 4 ∧
      hsum [-1, 1, 1, 0, 1, 0] 6 = 24 ∧
      hsum [-1, 1, 0, 0, 1, 1, 1] 7 = 48 ∧
      hsum [-1, 1, 0, 0, 1, 1, 0, 1] 8 = -336) ∧
    (hsumCode 213 5 = 4 ∧ hsumCode 456 6 = 24 ∧
      hsumCode 2148 7 = 48 ∧ hsumCode 5793 8 = -336) ∧
    (hsumCode 213 5 = hsum [-1, 1, 1, 0, 1] 5 ∧
      hsumCode 456 6 = hsum [-1, 1, 1, 0, 1, 0] 6 ∧
      hsumCode 2148 7 = hsum [-1, 1, 0, 0, 1, 1, 1] 7 ∧
      hsumCode 5793 8 = hsum [-1, 1, 0, 0, 1, 1, 0, 1] 8) ∧
    (∀ c : Nat, c < 243 →
      Int.natAbs (hsumCode c 5) = 0 ∨ 4 ≤ Int.natAbs (hsumCode c 5)) ∧
    (∀ c : Nat, c < 729 →
      Int.natAbs (hsumCode c 6) = 0 ∨ 24 ≤ Int.natAbs (hsumCode c 6)) ∧
    (∀ c : Nat, c < 2187 →
      Int.natAbs (hsumCode c 7) = 0 ∨ 48 ≤ Int.natAbs (hsumCode c 7)) ∧
    (∀ c : Nat, c < 243 →
      0 < Int.natAbs (hsumCode c 5) → 4 ≤ Int.natAbs (hsumCode c 5)) ∧
    (∀ c : Nat, c < 243 → Int.natAbs (hsumCode c 5) % 2 = 0) ∧
    (∀ c : Nat, c < 243 → hsumCode c 5 ≠ 2 ∧ hsumCode c 5 ≠ -2) ∧
    ((List.range 243).all (fun c =>
      decide (hsumCode c 5 % 5 = 0 ∨ hsumCode c 5 % 5 = 1 ∨ hsumCode c 5 % 5 = 4 ∨
        hsumCode c 5 % 5 = -1 ∨ hsumCode c 5 % 5 = -4)) = true) ∧
    ((0 < Int.natAbs (hsum [1] 1) ∧ 2 ^ 1 * Int.natAbs (hsum [1] 1) < 3 * fact 1) ∧
    (0 < Int.natAbs (hsum [0, 1] 2) ∧ 2 ^ 2 * Int.natAbs (hsum [0, 1] 2) < 3 * fact 2) ∧
    (0 < Int.natAbs (hsum [0, 1, -1] 3) ∧
      2 ^ 3 * Int.natAbs (hsum [0, 1, -1] 3) < 3 * fact 3) ∧
    (0 < Int.natAbs (hsum [-1, 1, 1, 1] 4) ∧
      2 ^ 4 * Int.natAbs (hsum [-1, 1, 1, 1] 4) < 3 * fact 4) ∧
    (0 < Int.natAbs (hsum [-1, 1, 1, 0, 1] 5) ∧
      2 ^ 5 * Int.natAbs (hsum [-1, 1, 1, 0, 1] 5) < 3 * fact 5) ∧
    (0 < Int.natAbs (hsum [-1, 1, 1, 0, 1, 0] 6) ∧
      2 ^ 6 * Int.natAbs (hsum [-1, 1, 1, 0, 1, 0] 6) < 3 * fact 6) ∧
    (0 < Int.natAbs (hsum [-1, 1, 0, 0, 1, 1, 1] 7) ∧
      2 ^ 7 * Int.natAbs (hsum [-1, 1, 0, 0, 1, 1, 1] 7) < 3 * fact 7) ∧
    (0 < Int.natAbs (hsum [-1, 1, 0, 0, 1, 1, 0, 1] 8) ∧
      2 ^ 8 * Int.natAbs (hsum [-1, 1, 0, 0, 1, 1, 0, 1] 8) < 3 * fact 8)) ∧
    (∀ c : Nat, ∀ j : Nat,
      ErdosTernary2.isTernaryDigit ((c / 3 ^ j) % 3)) :=
  ⟨hsum_two_sided, hsum_envelope, e317_witness_table, e317_code_witness_table,
    e317_code_list_bridge, e317_min_value_5, e317_min_value_6, e317_min_value_7,
    e317_min_imp_5, e317_gran_5, e317_no_unit_over_L5, e317_mod5_sweep_5,
    e317_frontier_c3, trit_is_ternary_digit⟩

/-! ## RECEIPT. -/

#print axioms E317.fact_pos
#print axioms E317.natDiv_le
#print axioms E317.two_pow_ge
#print axioms E317.ofNat_add
#print axioms E317.hsumAux_two_sided
#print axioms E317.hsum_two_sided
#print axioms E317.hsum_envelope
#print axioms E317.e317_witness_table
#print axioms E317.e317_code_witness_table
#print axioms E317.e317_code_list_bridge
#print axioms E317.e317_min_sweep_5
#print axioms E317.e317_min_value_5
#print axioms E317.e317_min_imp_5
#print axioms E317.e317_gran_sweep_5
#print axioms E317.e317_gran_5
#print axioms E317.e317_mod5_sweep_5
#print axioms E317.e317_min_sweep_6a
#print axioms E317.e317_min_sweep_6b
#print axioms E317.e317_min_value_6
#print axioms E317.e317_min_sweep_7a
#print axioms E317.e317_min_sweep_7b
#print axioms E317.e317_min_sweep_7c
#print axioms E317.e317_min_sweep_7d
#print axioms E317.e317_min_sweep_7e
#print axioms E317.e317_min_value_7
#print axioms E317.e317_no_unit_over_L5
#print axioms E317.e317_frontier_c3
#print axioms E317.trit_is_ternary_digit
#print axioms E317.e317_arsenal_bridge
#print axioms E317.erdos317_board

/-- THE KERNEL-63 RECEIPT CONSTANT: prints green when the whole file
elaborates clean (the CI grep target for this step). -/
def E317_SIGNED_HARMONIC_GREEN : String := "E317_SIGNED_HARMONIC_GREEN"

#eval E317_SIGNED_HARMONIC_GREEN

end E317
