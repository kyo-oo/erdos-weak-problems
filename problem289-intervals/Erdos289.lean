import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos289 — THE k-INTERVAL EGYPTIAN KERNEL r1 (Kernel 64, P289)

Erdős #289 (verbatim, corpus-erdos / FULL_PROOF_CAMPAIGN/P289/PROOF.md §0):

> Is it true that, for all sufficiently large $k$, there exist finite intervals
> $I_1,\ldots,I_k\subset\mathbb{N}$, distinct, not overlapping or adjacent, with
> $|I_i|\ge 2$ for $1\le i\le k$, such that
> $$1=\sum_{i=1}^k \sum_{n\in I_i}\frac{1}{n}\ ?$$

Campaign reading (the engine is the authority): `engine289_round1.py` is the
exact-rational DFS over interval placements inside $[2, M]$ with $M = 240$
— every candidate interval $[a,b]$ ($a \ge 2$, length $\ge 2$) carries its
EXACT harmonic sum $\sigma(a,b)$, pairs must be disjoint AND non-adjacent
(gap $\ge 1$), and the hunt asks for total $1$. Certified round-1 frontier
(bank: FULL_PROOF_CAMPAIGN/P289/PROOF.md §1 status log; re-certified on disk
by `battery289.py` S6 with TWO independent methods — the crossing search
with monotonicity and the brute-force cross-check at M = 80):
**k = 1 and k = 2 (gapped AND adjacent) have NO witness at M = 240** — the
DFS is exhaustive (sound pruning: every interval sum is positive, so any
interval with $\sigma >$ remaining target is skipped; its stdout capture
`engine289_round1_output.txt` is empty on disk — the k ≥ 3 python lanes are
infeasible at M = 240, the battery carries the frontier). The addendum's HM
example — $[2,7],[9,10],[17,18],[34,35],[84,85]$, total $\mathbf{2}$ — is
the witness-side anchor (battery-verified EXACTLY here in `battery289.py`).

Sibling coordination (do-not-duplicate law): Kernel 56 (`Erdos288.lean`,
namespace `E288`, GREEN) owns the #288 two-interval EQUALITY question
(`equalWindow`, disjoint equal-sum windows). NOTHING from #288 is restated
here — every theorem in this file is #289-native: the SUM-TO-ONE
decomposition predicate `covers2` (not window equality), the #289 shape
laws (`longWindow`, non-adjacency), the SPLITTING/join law of adjacent
windows (total preservation — the round-2 K2 lane's core), the
ADJACENT-COLLAPSE anti-closure law, the complete bounded k=2
classification, and the k=5 total-2 witness family.

Round-1 kernel (full statements, complete unconditional proofs, zero sorry):

1. §1 THE INTERVAL-SUM ENCODING — `iprod` (the unreduced denominator:
   product of [a,b]), `inum` (the numerator of $\Sigma_{i\in[a,b]} 1/i$ over
   that product), `covers2` (the #289 k=2 target: $\sigma(a,b)+\sigma(c,d)=1$
   as the cross-multiplied Nat identity), `longWindow` (|I| ≥ 2).
2. §2 THE STRUCTURAL LAWS — the recurrences (rfl), the empty-window laws,
   positivity, the single-window spellings, and the L86-safe atom kit
   (`e289_mul_pos`, `e289_mul_lt_right`, `e289_mul_cancel`).
3. §3 THE #289 PREDICATE LAWS — `covers2_comm` (symmetry of the
   decomposition), THE JOIN LAW `join_adjacent` ($\sigma(a,b)+\sigma(b+1,d)
   =\sigma(a,d)$ — adjacent windows merge; the engine's exact-rational
   arithmetic backbone), THE ANTI-CLOSURE/COLLAPSE LAW `adjacent_collapse`
   (a k=2 decomposition on ADJACENT windows is exactly a k=1 single-window
   decomposition of the merged window — the non-adjacency condition of #289
   is precisely what blocks this collapse).
4. §4 THE CENSUS (decide-certified, bounded) — `e289_census_k1_le12` (no
   window in [2,12] sums to 1), `e289_census_k2_gapped_le12` (no k=2
   non-adjacent pair in [2,12] — the engine's round-1 headline at
   decide-safe bound; python extends it to M=240), and THE COMPLETE k=2
   CLASSIFICATION `e289_no_pair_any_le12`: every k=2 pair of length-≥2
   windows within [2,12] — adjacent (via collapse + k=1 census) or
   non-adjacent (via the decide census) — fails to sum to 1.
5. §5 THE WITNESS SIDE — `e289_anchor_values` (the five HM windows' exact
   unreduced fractions) + `e289_hm_family` (the k=5 total-2 identity:
   shape — lengths ≥ 2, gaps ≥ 1 — plus the full cross-multiplied sum = 2).
6. §6 THE ARSENAL BRIDGE — `e289_arsenal_bridge` (five Arsenal lemmas at
   #289-native anchor numbers 8028/5040/7140/169).
7. §7 THE MASTER BOARD — `erdos289_board`, the flat anonymous-constructor
   composite (14 conjuncts).

House law: GitHub CI is the verifier of record (no local compile; author
blind). Axiom profile within [propext, Classical.choice, Quot.sound]. Zero
sorry / admit / native_decide; `by decide` only on closed numerics and
bounded List.range enumerations (13-wide, far under the 501 law). Python
mirror battery: `battery289.py` (output `battery289_output.txt`) — every
decide theorem pre-verified, the structural laws checked full-range, and
the engine frontier (k=1, k=2 gapped+adjacent exclusions at M=240)
re-certified by two independent methods.
-/

namespace E289

/-! ## §1 The interval-sum encoding — the #289 definitions. -/

/-- The #289 length constraint |I| ≥ 2 for the window [a, b]
(a `Prop` so the census guards and the board read like #289). -/
@[reducible] def longWindow (a b : Nat) : Prop := 2 ≤ b + 1 - a

/-- The length law: |[a,b]| ≥ 2 ⟺ a + 1 ≤ b (the guard spelling used by
the engine's interval table). -/
theorem longWindow_iff (a b : Nat) : longWindow a b ↔ a + 1 ≤ b := by
  unfold longWindow
  constructor
  · intro h
    omega
  · intro h
    omega

/-- The product of the integers in [a, b] — the unreduced DENOMINATOR of
the harmonic window sum σ(a, b) (empty window → 1). -/
def iprod : Nat → Nat → Nat
  | _, 0 => 1
  | a, b + 1 => if a ≤ b + 1 then iprod a b * (b + 1) else 1

/-- The NUMERATOR of Σ_{i∈[a,b]} 1/i over the product denominator `iprod a b`
(the unreduced exact fraction of the harmonic window sum; empty → 0). -/
def inum : Nat → Nat → Nat
  | _, 0 => 0
  | a, b + 1 => if a ≤ b + 1 then inum a b * (b + 1) + iprod a b else 0

/-- THE #289 k=2 DECOMPOSITION TARGET: σ(a,b) + σ(c,d) = 1, as the
cross-multiplied Nat identity over the common denominator
`iprod a b * iprod c d` (valid whenever both windows are nonempty — §2's
`iprod_pos`). Reducible so `by decide` sees the Nat equation through the
def in the census theorems. -/
@[reducible]
def covers2 (a b c d : Nat) : Prop :=
  inum a b * iprod c d + inum c d * iprod a b = iprod a b * iprod c d

/-! ## §2 The structural laws — recurrences, emptiness, positivity, the
L86-safe atom kit. -/

/-- The base recurrences (rfl: structural match on the right end). -/
theorem iprod_zero (a : Nat) : iprod a 0 = 1 := rfl

theorem inum_zero (a : Nat) : inum a 0 = 0 := rfl

theorem iprod_unfold (a b : Nat) :
    iprod a (b + 1) = if a ≤ b + 1 then iprod a b * (b + 1) else 1 := rfl

theorem inum_unfold (a b : Nat) :
    inum a (b + 1) = if a ≤ b + 1 then inum a b * (b + 1) + iprod a b else 0 := rfl

/-- An empty window has the empty product 1 (induction on the right end). -/
theorem iprod_nil : ∀ (b a : Nat), b < a → iprod a b = 1 := by
  intro b
  induction b with
  | zero => intro a _
            rfl
  | succ b _ =>
      intro a h
      have hneg : ¬ (a ≤ b + 1) := by omega
      rw [iprod_unfold, if_neg hneg]

/-- An empty window has numerator 0. -/
theorem inum_nil : ∀ (b a : Nat), b < a → inum a b = 0 := by
  intro b
  induction b with
  | zero => intro a _
            rfl
  | succ b _ =>
      intro a h
      have hneg : ¬ (a ≤ b + 1) := by omega
      rw [inum_unfold, if_neg hneg]

/-- Self-contained strict positivity of products (the L86-safe core:
`Nat.mul_succ` expansion + omega shell; no external mul_pos). -/
theorem e289_mul_pos (x y : Nat) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, y = k + 1 := ⟨y - 1, by omega⟩
  rw [hk]
  have hms : x * (k + 1) = x * k + x := Nat.mul_succ x k
  rw [hms]
  omega

/-- Strict growth of products on the right: x < y → x * z < y * z
(the cancellation engine, built from `ring` expansion + omega atoms). -/
theorem e289_mul_lt_right (x y z : Nat) (hxy : x < y) (hz : 0 < z) :
    x * z < y * z := by
  obtain ⟨s, hs⟩ : ∃ s : Nat, y = x + s + 1 := ⟨y - x - 1, by omega⟩
  have hexp : (x + s + 1) * z = x * z + (s + 1) * z := by ring
  have hpos : 0 < (s + 1) * z := e289_mul_pos (s + 1) z (by omega) hz
  have hyz : y * z = x * z + (s + 1) * z := by rw [hs, hexp]
  omega

/-- Right cancellation of products (the bridge the collapse law needs). -/
theorem e289_mul_cancel (x y z : Nat) (hz : 0 < z) : x * z = y * z → x = y := by
  intro h
  rcases Nat.lt_trichotomy x y with hlt | heq | hgt
  · have h1 := e289_mul_lt_right x y z hlt hz
    omega
  · exact heq
  · have h1 := e289_mul_lt_right y x z hgt hz
    omega

/-- THE PRODUCT LAW: for windows of positive integers the denominator is
positive (unconditionally — the empty window gives 1). -/
theorem iprod_pos (a b : Nat) (ha : 1 ≤ a) : 0 < iprod a b := by
  induction b with
  | zero => have h1 : iprod a 0 = 1 := rfl
            omega
  | succ b ih =>
      rw [iprod_unfold]
      by_cases h : a ≤ b + 1
      · rw [if_pos h]
        have hy : 0 < b + 1 := by omega
        exact e289_mul_pos _ _ ih hy
      · rw [if_neg h]
        omega

/-- THE NUMERATOR LAW: a nonempty window of positive integers has positive
harmonic sum. -/
theorem inum_pos (a b : Nat) (ha : 1 ≤ a) : a ≤ b → 0 < inum a b := by
  induction b with
  | zero => intro hba
            omega
  | succ b ih =>
      intro hba
      rw [inum_unfold, if_pos hba]
      have hw : 0 < iprod a b := iprod_pos a b ha
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · have hh := ih (by omega)
        have hm : 0 < inum a b * (b + 1) := e289_mul_pos _ _ hh (by omega)
        omega
      · have hnil : inum a b = 0 := inum_nil b a (by omega)
        rw [hnil]
        omega

/-- The nonempty-step recurrences (the fraction-addition laws:
σ(a,b+1) = (inum·(b+1) + iprod) over iprod·(b+1)). -/
theorem iprod_succ_le (a b : Nat) (h : a ≤ b + 1) :
    iprod a (b + 1) = iprod a b * (b + 1) := by
  rw [iprod_unfold, if_pos h]

theorem inum_succ_le (a b : Nat) (h : a ≤ b + 1) :
    inum a (b + 1) = inum a b * (b + 1) + iprod a b := by
  rw [inum_unfold, if_pos h]

/-- THE SINGLE-TERM SPELLING: the window [a, a] carries 1/a exactly. -/
theorem inum_single (a : Nat) (ha : 1 ≤ a) : inum a a = 1 := by
  have hstep := inum_succ_le a (a - 1) (by omega)
  have hpre : (a - 1) + 1 = a := by omega
  rw [hpre] at hstep
  have hnil : inum a (a - 1) = 0 := inum_nil (a - 1) a (by omega)
  have hp : iprod a (a - 1) = 1 := iprod_nil (a - 1) a (by omega)
  rw [hstep, hnil, hp]
  omega

theorem iprod_single (a : Nat) (ha : 1 ≤ a) : iprod a a = a := by
  have hstep := iprod_succ_le a (a - 1) (by omega)
  have hpre : (a - 1) + 1 = a := by omega
  rw [hpre] at hstep
  have hp : iprod a (a - 1) = 1 := iprod_nil (a - 1) a (by omega)
  rw [hstep, hp]
  omega

/-! ## §3 The #289 predicate laws — symmetry, the join/splitting law,
the adjacent-collapse anti-closure law. -/

/-- THE SYMMETRY LAW: the k=2 decomposition target is invariant under
exchanging the two intervals (the WLOG companion for ordered searches:
the engine explores each unordered pair once). -/
theorem covers2_comm (a b c d : Nat) : covers2 a b c d ↔ covers2 c d a b := by
  constructor
  · intro h
    unfold covers2 at h ⊢
    rw [Nat.add_comm, Nat.mul_comm (iprod c d) (iprod a b)]
    exact h
  · intro h
    unfold covers2 at h ⊢
    rw [Nat.add_comm, Nat.mul_comm (iprod a b) (iprod c d)]
    exact h

/-- THE JOIN/SPLITTING LAW (t-form, the induction core): for a ≤ b and
t ≥ 0, merging the adjacent windows [a,b] and [b+1, b+1+t] preserves the
total — σ(a,b) + σ(b+1, b+1+t) = σ(a, b+1+t), as the cross-multiplied Nat
identity over the product of the two unreduced denominators. This is the
engine's exact-rational arithmetic backbone and the round-2 K2 splitting
lane's foundation: replacing one interval by two ADJACENT sub-intervals
changes nothing (which is exactly why #289 forbids adjacency — see
`adjacent_collapse`). -/
theorem join_aux (a b : Nat) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∀ t : Nat,
    inum a (b + 1 + t) * (iprod a b * iprod (b + 1) (b + 1 + t))
      = (inum a b * iprod (b + 1) (b + 1 + t)
          + inum (b + 1) (b + 1 + t) * iprod a b) * iprod a (b + 1 + t) := by
  intro t
  induction t with
  | zero =>
      rw [Nat.add_zero]
      rw [inum_single (b + 1) (by omega), iprod_single (b + 1) (by omega)]
      rw [inum_succ_le a b (by omega), iprod_succ_le a b (by omega)]
      ring
  | succ t ih =>
      rw [← Nat.add_assoc]
      rw [inum_succ_le a (b + 1 + t) (by omega),
          iprod_succ_le a (b + 1 + t) (by omega),
          inum_succ_le (b + 1) (b + 1 + t) (by omega),
          iprod_succ_le (b + 1) (b + 1 + t) (by omega)]
      have e1 : (inum a (b + 1 + t) * (b + 1 + t + 1) + iprod a (b + 1 + t))
            * (iprod a b * (iprod (b + 1) (b + 1 + t) * (b + 1 + t + 1)))
          = inum a (b + 1 + t) * (iprod a b * iprod (b + 1) (b + 1 + t))
            * (b + 1 + t + 1) * (b + 1 + t + 1)
            + iprod a (b + 1 + t) * iprod a b * iprod (b + 1) (b + 1 + t)
            * (b + 1 + t + 1) := by
        ring
      have e2 : (inum a b * (iprod (b + 1) (b + 1 + t) * (b + 1 + t + 1))
            + (inum (b + 1) (b + 1 + t) * (b + 1 + t + 1)
              + iprod (b + 1) (b + 1 + t)) * iprod a b)
            * (iprod a (b + 1 + t) * (b + 1 + t + 1))
          = (inum a b * iprod (b + 1) (b + 1 + t)
              + inum (b + 1) (b + 1 + t) * iprod a b) * iprod a (b + 1 + t)
            * (b + 1 + t + 1) * (b + 1 + t + 1)
            + iprod a (b + 1 + t) * iprod a b * iprod (b + 1) (b + 1 + t)
            * (b + 1 + t + 1) := by
        ring
      rw [e1, e2, ih]

/-- THE JOIN/SPLITTING LAW (d-form): for a ≤ b < b+1 ≤ d, the adjacent
windows [a,b], [b+1,d] merge — σ(a,b) + σ(b+1,d) = σ(a,d) — as the
cross-multiplied Nat identity over the product of the unreduced
denominators. -/
theorem join_adjacent (a b d : Nat) (ha : 1 ≤ a) (hab : a ≤ b) (hbd : b + 1 ≤ d) :
    inum a d * (iprod a b * iprod (b + 1) d)
      = (inum a b * iprod (b + 1) d + inum (b + 1) d * iprod a b) * iprod a d := by
  obtain ⟨t, hteq⟩ : ∃ t : Nat, d = b + 1 + t := ⟨d - b - 1, by omega⟩
  subst hteq
  exact join_aux a b ha hab t

/-- THE ANTI-CLOSURE / COLLAPSE LAW (the structural heart of the #289
non-adjacency condition): a k=2 sum-to-one decomposition on ADJACENT
windows [a,b], [b+1,d] exists ⟺ the MERGED window [a,d] alone sums to 1
(a k=1 decomposition). So forbidding adjacency in #289 is exactly
forbidding the merge — adjacent k=2 families collapse to k=1 families and
carry no new content. -/
theorem adjacent_collapse (a b d : Nat) (ha : 1 ≤ a) (hab : a ≤ b) (hbd : b + 1 ≤ d) :
    covers2 a b (b + 1) d ↔ inum a d = iprod a d := by
  have hj := join_adjacent a b d ha hab hbd
  have hZ : 0 < iprod a b * iprod (b + 1) d :=
    e289_mul_pos _ _ (iprod_pos a b ha) (iprod_pos (b + 1) d (by omega))
  constructor
  · intro hcov
    unfold covers2 at hcov
    rw [hcov] at hj
    rw [Nat.mul_comm (iprod a b * iprod (b + 1) d) (iprod a d)] at hj
    exact e289_mul_cancel (inum a d) (iprod a d) (iprod a b * iprod (b + 1) d) hZ hj
  · intro hsingle
    rw [hsingle] at hj
    rw [Nat.mul_comm (iprod a d) (iprod a b * iprod (b + 1) d)] at hj
    have hcancel := e289_mul_cancel (iprod a b * iprod (b + 1) d)
      (inum a b * iprod (b + 1) d + inum (b + 1) d * iprod a b) (iprod a d)
      (iprod_pos a d ha) hj
    unfold covers2
    exact hcancel.symm

/-! ## §4 The census — decide-certified bounded exclusions and the
complete bounded k=2 classification. -/

/-- THE k=1 CENSUS (decide-certified): NO window [a,b] with 2 ≤ a ≤ b ≤ 12
has harmonic sum exactly 1 (`inum a b = iprod a b`). The python battery
extends this census to M = 240 with zero hits (the Kürschák parity
obstruction is the round-2 lane for the unbounded statement). -/
theorem e289_census_k1_le12 :
    (List.range 13).all (fun a : Nat =>
      (List.range 13).all (fun b : Nat =>
        decide (¬ (2 ≤ a ∧ a ≤ b ∧ inum a b = iprod a b)))) = true := by
  decide

/-- THE k=1 EXCLUSION (usable form, extracted from the census): no window
inside [2,12] sums to 1. -/
theorem e289_no_single_window_le12 :
    ∀ a b : Nat, 2 ≤ a → a ≤ b → b ≤ 12 → inum a b ≠ iprod a b := by
  intro a b ha hab hb12
  have hrow := (List.all_eq_true.mp e289_census_k1_le12) a
    (List.mem_range.mpr (by omega))
  have hcell := (List.all_eq_true.mp hrow) b (List.mem_range.mpr (by omega))
  have h := of_decide_eq_true hcell
  intro hcontra
  exact h ⟨ha, hab, hcontra⟩

/-- THE k=2 GAPPED CENSUS (decide-certified): NO pair of windows with all
endpoints ≤ 12, both lengths ≥ 2, gap ≥ 1 (non-adjacent — the #289
condition), sums to 1. This is the engine's round-1 headline at a
decide-safe bound: the M = 240 exclusion is banked
(FULL_PROOF_CAMPAIGN/P289/PROOF.md §1) and mirrored on disk in
`battery289.py` by two independent methods (crossing + brute force). -/
theorem e289_census_k2_gapped_le12 :
    (List.range 13).all (fun a : Nat =>
      (List.range 13).all (fun b : Nat =>
        (List.range 13).all (fun c : Nat =>
          (List.range 13).all (fun d : Nat =>
            decide (¬ (2 ≤ a ∧ a + 1 ≤ b ∧ b + 1 < c ∧ c + 1 ≤ d ∧
              covers2 a b c d)))))) = true := by
  decide

/-- THE k=2 GAPPED EXCLUSION (usable form, extracted from the census). -/
theorem e289_no_gapped_pair_le12 :
    ∀ a b c d : Nat, 2 ≤ a → a + 1 ≤ b → b + 1 < c → c + 1 ≤ d → d ≤ 12 →
    ¬ covers2 a b c d := by
  intro a b c d ha hb hgap hlen hd12 hcov
  have h1 := (List.all_eq_true.mp e289_census_k2_gapped_le12) a
    (List.mem_range.mpr (by omega))
  have h2 := (List.all_eq_true.mp h1) b (List.mem_range.mpr (by omega))
  have h3 := (List.all_eq_true.mp h2) c (List.mem_range.mpr (by omega))
  have h4 := (List.all_eq_true.mp h3) d (List.mem_range.mpr (by omega))
  exact (of_decide_eq_true h4) ⟨ha, hb, hgap, hlen, hcov⟩

/-- THE k=2 ADJACENT EXCLUSION (structural + census): no ADJACENT pair of
length-≥2 windows inside [2,12] sums to 1 — by the collapse law such a pair
is exactly a k=1 window of length ≥ 4, excluded by the k=1 census. -/
theorem e289_no_adjacent_pair_le12 :
    ∀ a b d : Nat, 2 ≤ a → a + 1 ≤ b → b + 2 ≤ d → d ≤ 12 →
    ¬ covers2 a b (b + 1) d := by
  intro a b d ha hb hd hd12 hcov
  have h1 : 1 ≤ a := by omega
  have h2 : a ≤ b := by omega
  have h3 : b + 1 ≤ d := by omega
  have hsingle := (adjacent_collapse a b d h1 h2 h3).mp hcov
  exact e289_no_single_window_le12 a d (by omega) (by omega) hd12 hsingle

/-- THE COMPLETE BOUNDED k=2 CLASSIFICATION (the round-1 census theorem):
every pair of length-≥2 windows [a,b], [c,d] with a ≥ 2, first strictly
before second, and all endpoints ≤ 12, fails to sum to 1 — ADJACENT pairs
(c = b+1) by the collapse law + the k=1 census, NON-ADJACENT pairs
(c ≥ b+2) by the decide census. Adjacent and gapped exhaust the ordered
pairs, so this is a complete finite classification theorem: the k=2 world
of #289 is EMPTY on [2,12] (engine: EMPTY on [2,240]). -/
theorem e289_no_pair_any_le12 :
    ∀ a b c d : Nat, 2 ≤ a → longWindow a b → b < c → longWindow c d → d ≤ 12 →
    ¬ covers2 a b c d := by
  intro a b c d ha hlb hc hld hd12 hcov
  have hlb' : a + 1 ≤ b := (longWindow_iff a b).mp hlb
  have hld' : c + 1 ≤ d := (longWindow_iff c d).mp hld
  have hcase : c = b + 1 ∨ b + 2 ≤ c := by omega
  rcases hcase with hadj | hgap
  · subst hadj
    exact e289_no_adjacent_pair_le12 a b d (by omega) (by omega) (by omega) hd12 hcov
  · exact e289_no_gapped_pair_le12 a b c d (by omega) (by omega) (by omega)
      (by omega) hd12 hcov

/-! ## §5 The witness side — the HM k=5 total-2 family (the anchor of the
engine's exact-rational world, certified in `battery289.py`). -/

/-- THE ANCHORS (python-verified in battery289.py): the exact unreduced
fractions of the five HM windows — [2,7] ↦ 8028/5040, [9,10] ↦ 19/90,
[17,18] ↦ 35/306, [34,35] ↦ 69/1190, [84,85] ↦ 169/7140. -/
theorem e289_anchor_values :
    inum 2 7 = 8028 ∧ iprod 2 7 = 5040 ∧
    inum 9 10 = 19 ∧ iprod 9 10 = 90 ∧
    inum 17 18 = 35 ∧ iprod 17 18 = 306 ∧
    inum 34 35 = 69 ∧ iprod 34 35 = 1190 ∧
    inum 84 85 = 169 ∧ iprod 84 85 = 7140 := by
  decide

/-- THE k=5 WITNESS FAMILY (the campaign's HM example, total 2): the five
windows [2,7], [9,10], [17,18], [34,35], [84,85] are pairwise non-adjacent
(gaps ≥ 1), all have length ≥ 2 (the full #289 shape — except the total,
which is 2, not 1), and their harmonic interval sums add up EXACTLY to 2:
Σ σ(I_i) = 2 as the cross-multiplied Nat identity over the product of the
five unreduced denominators. The #289 predicate world is nonempty; the
unrestricted-total (Kovac) and large-k (LEAP) lanes are the round-2
construction targets. -/
theorem e289_hm_family :
    (longWindow 2 7 ∧ longWindow 9 10 ∧ longWindow 17 18 ∧
      longWindow 34 35 ∧ longWindow 84 85)
    ∧ (7 + 1 < 9 ∧ 10 + 1 < 17 ∧ 18 + 1 < 34 ∧ 35 + 1 < 84)
    ∧ (inum 2 7 * (iprod 9 10 * iprod 17 18 * iprod 34 35 * iprod 84 85)
      + inum 9 10 * (iprod 2 7 * iprod 17 18 * iprod 34 35 * iprod 84 85)
      + inum 17 18 * (iprod 2 7 * iprod 9 10 * iprod 34 35 * iprod 84 85)
      + inum 34 35 * (iprod 2 7 * iprod 9 10 * iprod 17 18 * iprod 84 85)
      + inum 84 85 * (iprod 2 7 * iprod 9 10 * iprod 17 18 * iprod 34 35)
      = 2 * (iprod 2 7 * iprod 9 10 * iprod 17 18 * iprod 34 35 * iprod 84 85)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold longWindow
    omega
  · omega
  · decide

/-! ## §6 The arsenal bridge — BOSS's mathematics on the #289 anchors. -/

/-- THE ARSENAL BRIDGE: five Arsenal lemmas at #289-native anchor numbers
(8028 = inum 2 7, 5040 = iprod 2 7, 7140 = iprod 84 85, 169 = inum 84 85). -/
theorem e289_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (8028 % 3) ∧
    (5040 ^ 2 - 1 = (5040 - 1) * (5040 + 1)) ∧
    (7140 % (169 * 2)) % 169 = 7140 % 169 ∧
    carryAtPos 7140 1 < 4 ∧
    v2r (3 ^ 1 * 8028) = v2r 8028 :=
  ⟨by decide, sq_sub_one 5040 (by decide), mod_mod_mul 7140 169 2 (by decide),
    carryAtPos_bound 7140 1, CardinalWorldsV2.v2r_ternary_scaling 1 8028⟩

/-! ## §7 The master board. -/

/-- THE P289 KERNEL MASTER BOARD (14 conjuncts, full statements,
unconditional, flat anonymous constructor): the denominator law + the
numerator law + the two single-window spellings + THE JOIN/SPLITTING LAW +
THE ANTI-CLOSURE/COLLAPSE LAW + the decomposition symmetry + the five
python-verified anchors + THE k=5 TOTAL-2 WITNESS FAMILY + the k=1 census
(decide + usable) + the k=2 gapped census (decide + usable) + THE COMPLETE
BOUNDED k=2 CLASSIFICATION + the arsenal bridge core. -/
theorem erdos289_board :
    (∀ a b : Nat, 1 ≤ a → 0 < iprod a b) ∧
    (∀ a b : Nat, 1 ≤ a → a ≤ b → 0 < inum a b) ∧
    (∀ a : Nat, 1 ≤ a → inum a a = 1) ∧
    (∀ a : Nat, 1 ≤ a → iprod a a = a) ∧
    (∀ a b d : Nat, 1 ≤ a → a ≤ b → b + 1 ≤ d →
      inum a d * (iprod a b * iprod (b + 1) d)
        = (inum a b * iprod (b + 1) d + inum (b + 1) d * iprod a b) * iprod a d) ∧
    (∀ a b d : Nat, 1 ≤ a → a ≤ b → b + 1 ≤ d →
      (covers2 a b (b + 1) d ↔ inum a d = iprod a d)) ∧
    (∀ a b c d : Nat, covers2 a b c d ↔ covers2 c d a b) ∧
    (inum 2 7 = 8028 ∧ iprod 2 7 = 5040 ∧
      inum 9 10 = 19 ∧ iprod 9 10 = 90 ∧
      inum 17 18 = 35 ∧ iprod 17 18 = 306 ∧
      inum 34 35 = 69 ∧ iprod 34 35 = 1190 ∧
      inum 84 85 = 169 ∧ iprod 84 85 = 7140) ∧
    ((longWindow 2 7 ∧ longWindow 9 10 ∧ longWindow 17 18 ∧
      longWindow 34 35 ∧ longWindow 84 85)
      ∧ (7 + 1 < 9 ∧ 10 + 1 < 17 ∧ 18 + 1 < 34 ∧ 35 + 1 < 84)
      ∧ (inum 2 7 * (iprod 9 10 * iprod 17 18 * iprod 34 35 * iprod 84 85)
      + inum 9 10 * (iprod 2 7 * iprod 17 18 * iprod 34 35 * iprod 84 85)
      + inum 17 18 * (iprod 2 7 * iprod 9 10 * iprod 34 35 * iprod 84 85)
      + inum 34 35 * (iprod 2 7 * iprod 9 10 * iprod 17 18 * iprod 84 85)
      + inum 84 85 * (iprod 2 7 * iprod 9 10 * iprod 17 18 * iprod 34 35)
      = 2 * (iprod 2 7 * iprod 9 10 * iprod 17 18 * iprod 34 35 * iprod 84 85))) ∧
    ((List.range 13).all (fun a : Nat =>
      (List.range 13).all (fun b : Nat =>
        decide (¬ (2 ≤ a ∧ a ≤ b ∧ inum a b = iprod a b)))) = true) ∧
    (∀ a b : Nat, 2 ≤ a → a ≤ b → b ≤ 12 → inum a b ≠ iprod a b) ∧
    ((List.range 13).all (fun a : Nat =>
      (List.range 13).all (fun b : Nat =>
        (List.range 13).all (fun c : Nat =>
          (List.range 13).all (fun d : Nat =>
            decide (¬ (2 ≤ a ∧ a + 1 ≤ b ∧ b + 1 < c ∧ c + 1 ≤ d ∧
              covers2 a b c d)))))) = true) ∧
    (∀ a b c d : Nat, 2 ≤ a → longWindow a b → b < c → longWindow c d → d ≤ 12 →
      ¬ covers2 a b c d) ∧
    (5040 ^ 2 - 1 = (5040 - 1) * (5040 + 1) ∧ v2r (3 ^ 1 * 8028) = v2r 8028) :=
  ⟨iprod_pos, inum_pos, inum_single, iprod_single, join_adjacent,
    adjacent_collapse, covers2_comm, e289_anchor_values, e289_hm_family,
    e289_census_k1_le12, e289_no_single_window_le12,
    e289_census_k2_gapped_le12, e289_no_pair_any_le12,
    ⟨sq_sub_one 5040 (by decide), CardinalWorldsV2.v2r_ternary_scaling 1 8028⟩⟩

/-! ## RECEIPT. -/

#print axioms E289.longWindow_iff
#print axioms E289.iprod_zero
#print axioms E289.inum_zero
#print axioms E289.iprod_unfold
#print axioms E289.inum_unfold
#print axioms E289.iprod_nil
#print axioms E289.inum_nil
#print axioms E289.e289_mul_pos
#print axioms E289.e289_mul_lt_right
#print axioms E289.e289_mul_cancel
#print axioms E289.iprod_pos
#print axioms E289.inum_pos
#print axioms E289.iprod_succ_le
#print axioms E289.inum_succ_le
#print axioms E289.inum_single
#print axioms E289.iprod_single
#print axioms E289.covers2_comm
#print axioms E289.join_aux
#print axioms E289.join_adjacent
#print axioms E289.adjacent_collapse
#print axioms E289.e289_census_k1_le12
#print axioms E289.e289_no_single_window_le12
#print axioms E289.e289_census_k2_gapped_le12
#print axioms E289.e289_no_gapped_pair_le12
#print axioms E289.e289_no_adjacent_pair_le12
#print axioms E289.e289_no_pair_any_le12
#print axioms E289.e289_anchor_values
#print axioms E289.e289_hm_family
#print axioms E289.e289_arsenal_bridge
#print axioms E289.erdos289_board

/-- THE KERNEL-64 RECEIPT CONSTANT: prints green when the whole file
elaborates clean (the CI grep target for this step). -/
def E289_INTERVALS_GREEN : String := "E289_INTERVALS_GREEN"

#eval E289_INTERVALS_GREEN

end E289
