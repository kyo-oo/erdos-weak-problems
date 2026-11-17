import Mathlib
import GSTTowerFire
import GSTDiagonalRead
import GSTTheAct
import GSTClimbInfiniteFamily

set_option maxHeartbeats 20000000

/-!
# THE GHOST-RAY EXCLUSION — terminal formalization

Formalization of `upload/WORLDTRACE_GHOST_RAY_EXCLUSION_PROOF.md`:
the terminal Worldtrace ghost-ray exclusion theorem, with the one
external input (Mahler's 3-adic exponential transcendence) stated as an
explicit hypothesis in **pure integer divisibility form** — no p-adic
analysis objects are needed anywhere.

The chain (document §17):

* a ghost ray is the stabilized middle-third condition
  `∀ k ≥ 3, 3^(k-1) ≤ (c (k-1) * u) % 3^k < 2 * 3^(k-1)`;
* the ghost forces the exact all-ones tail shape
  `2 * ((c (k-1) * u) % 3^k) + 9 = 2 * a + 3^k` with `a < 9`, `3 ∤ a`;
* hence the tower lock
  `2u(4^(3^s) - 1) - (2a - 9) * 3^(s+1) = 3^(2s+2) * m`;
* hence the Mahler witness
  `2u(4^(3^s) - 1) - (6a - 27) * 3^s = 3^(2s+2) * m` is divisible by
  every power of 3, i.e. the rational sequence `(4^(3^s) - 1) / 3^s`
  converges 3-adically to the rational `(6a - 27) / (2u)`;
* the external transcendence input denies exactly this;
* with the uniform compression bridge (every Cantorian counterexample's
  three-free core lies on a ghost ray) the act closes.

The tower coefficient is `GSTTowerFire.c s = (4^(3^s) - 1) / 3^(s+1)`,
the document's `C_s = lteCoeff s = ωCutWord s 1`.
-/

namespace GSTGhostRay

/-! ## §1 The ghost ray -/

/-- **THE GHOST RAY** (document (G)): the stabilized scaled LTE diagonal
of the three-free core `u` sits in the exact middle third at every
ternary depth `k ≥ 3` — every stabilized digit from position two on is
one. -/
def GhostRay (u : Nat) : Prop :=
  ∀ k : Nat, 3 ≤ k →
    3^(k-1) ≤ (GSTTowerFire.c (k-1) * u) % 3^k
    ∧ (GSTTowerFire.c (k-1) * u) % 3^k < 2 * 3^(k-1)

/-! ## §2 The tower bridge — `GSTTowerFire.c` is the canonical LTE tower -/

/-- The tower coefficient `c n = (4^(3^n) - 1) / 3^(n+1)` is the
canonical LTE coefficient `lteCoeff n`: both satisfy the same exact
LTE identity, so they are equal. -/
theorem c_eq_lteCoeff (n : Nat) :
    GSTTowerFire.c n = GSTCanonicalTailLTE.lteCoeff n := by
  have h1 := GSTTowerFire.four_pow_three_pow_eq n
  have h2 := GSTCanonicalTailLTE.pow4_three_power_lte_exact n
  have h3 : 3^(n+1) * GSTTowerFire.c n
      = 3^(n+1) * GSTCanonicalTailLTE.lteCoeff n := by
    linarith
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h3

/-- **Coefficient stabilization** for the tower: `c w ≡ c v [MOD 3^(v+1)]`
for `v ≤ w` — the document (2.2), through the repo's own green law. -/
theorem c_stable (v w : Nat) (hw : v ≤ w) :
    GSTTowerFire.c w % 3^(v+1) = GSTTowerFire.c v % 3^(v+1) := by
  rw [c_eq_lteCoeff, c_eq_lteCoeff]
  exact GSTDiagonalRead.lteCoeff_stable v w hw

/-! ## §3 Lemma A — the exact all-ones tail shape -/

/-- **LEMMA A (the exact ghost shape, doubled form).**  A ghost ray
forces the residue of `c (k-1) * u` modulo `3^k` to be the all-ones
tail `a + (3^k - 9) / 2` with the fixed head `a = (c 1 * u) % 9` —
stated free of division as
`2 * ((c (k-1) * u) % 3^k) + 9 = 2 * a + 3^k`.

The induction needs only the ghost condition at each depth plus
coefficient stabilization: the top digit is one, and the tail below is
the previous depth's shape. -/
theorem ghost_residue_shape (u : Nat) (hg : GhostRay u) :
    ∀ k : Nat, 3 ≤ k →
      2 * ((GSTTowerFire.c (k-1) * u) % 3^k) + 9
        = 2 * ((GSTTowerFire.c 1 * u) % 9) + 3^k := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by omega)
  | succ j ih =>
      intro hk
      rcases Nat.lt_or_ge j 3 with hj | hj
      · -- j = 2: the base shape at depth three
        have hj2 : j = 2 := by omega
        subst hj2
        norm_num
        obtain ⟨hlo, hhi⟩ := hg 3 (by omega)
        norm_num at hlo hhi
        have hm9 : (GSTTowerFire.c 2 * u) % 9 = (GSTTowerFire.c 1 * u) % 9 := by
          have hc : GSTTowerFire.c 2 % 9 = GSTTowerFire.c 1 % 9 := by
            simpa using c_stable 1 2 (by omega)
          rw [Nat.mul_mod, hc, ← Nat.mul_mod]
        have hmod : ((GSTTowerFire.c 2 * u) % 27) % 9
            = (GSTTowerFire.c 1 * u) % 9 := by
          rw [Nat.mod_mod_of_dvd _ (by decide : (9:Nat) ∣ 27)]
          exact hm9
        have ha : (GSTTowerFire.c 1 * u) % 9 < 9 := Nat.mod_lt _ (by decide)
        have hd := Nat.div_add_mod ((GSTTowerFire.c 2 * u) % 27) 9
        omega
      · -- j ≥ 3: the inductive lift through stabilization
        have ihj := ih hj
        rw [show j + 1 - 1 = j from by omega]
        obtain ⟨hlo, hhi⟩ := hg (j+1) (by omega)
        rw [show j + 1 - 1 = j from by omega] at hlo hhi
        set r' : Nat := (GSTTowerFire.c j * u) % 3^(j+1) with hr'
        have hsub : r' - 3^j < 3^j := by omega
        have hkey : r' - 3^j = r' % 3^j := by
          have e1 : r' = (r' - 3^j) + 1 * 3^j := by omega
          rw [e1, Nat.add_mul_mod_self_right, one_mul, Nat.add_sub_cancel,
            Nat.mod_eq_of_lt hsub]
        have hmodk : (GSTTowerFire.c j * u) % 3^(j+1) % 3^j
            = (GSTTowerFire.c j * u) % 3^j :=
          Nat.mod_mod_of_dvd _ (pow_dvd_pow (3 : ℕ) (by omega))
        rw [← hr'] at hmodk
        have hcs : GSTTowerFire.c j % 3^j = GSTTowerFire.c (j-1) % 3^j := by
          have h := c_stable (j-1) j (by omega)
          rw [show (j-1)+1 = j from by omega] at h
          exact h
        have hstab : (GSTTowerFire.c j * u) % 3^j
            = (GSTTowerFire.c (j-1) * u) % 3^j := by
          rw [Nat.mul_mod, hcs, ← Nat.mul_mod]
        rw [Nat.pow_succ]
        omega

/-! ## §4 Lemma B — the finite ghost congruence -/

/-- **LEMMA B (the fundamental finite ghost congruence, document (5.5)).**
A ghost ray satisfies
`2 * (c (k-1) * u) + 9 = 2 * a + 3^k * m` for every depth `k ≥ 3`
with the fixed head `a = (c 1 * u) % 9`: the infinite middle-third ray
compresses to one fixed signed constant approximated to arbitrarily
high 3-adic precision by the tower products. -/
theorem ghost_congruence (u : Nat) (hg : GhostRay u) (k : Nat) (hk : 3 ≤ k) :
    ∃ m : Nat, 2 * (GSTTowerFire.c (k-1) * u) + 9
      = 2 * ((GSTTowerFire.c 1 * u) % 9) + 3^k * m := by
  have hshape := ghost_residue_shape u hg k hk
  have hq := Nat.div_add_mod (GSTTowerFire.c (k-1) * u) (3^k)
  refine ⟨2 * (GSTTowerFire.c (k-1) * u / 3^k) + 1, ?_⟩
  linarith

/-! ## §5 Lemma C — the tower lock and the Mahler witness -/

/-- **LEMMA C (the tower lock, document (7.1)).**  A ghost ray locks the
LTE tower itself: for every `s ≥ 2`,
`2u(4^(3^s) - 1) - (2a - 9) * 3^(s+1) = 3^(2s+2) * m` over the
integers — pure ordinary arithmetic, the finite avatar of the ghost. -/
theorem ghost_tower_lock (u : Nat) (hg : GhostRay u) (s : Nat) (hs : 2 ≤ s) :
    ∃ m : ℤ, (2*(u:ℤ) * ((4:ℤ)^(3^s) - 1)
        - (2*(((GSTTowerFire.c 1 * u) % 9 : Nat) : ℤ) - 9) * (3:ℤ)^(s+1))
      = (3:ℤ)^(2*s+2) * m := by
  obtain ⟨m₀, hm₀⟩ := ghost_congruence u hg (s+1) (by omega)
  have h4ℤ : (4:ℤ)^(3^s)
      = 1 + (3:ℤ)^(s+1) * ((GSTTowerFire.c s : Nat) : ℤ) := by
    exact_mod_cast GSTTowerFire.four_pow_three_pow_eq s
  have hcongℤ : 2 * (((GSTTowerFire.c s : Nat) : ℤ) * (u:ℤ)) + 9
      = 2 * (((GSTTowerFire.c 1 * u) % 9 : Nat) : ℤ)
        + (3:ℤ)^(s+1) * (m₀ : ℤ) := by
    exact_mod_cast hm₀
  have hexpℤ : (3:ℤ)^(s+1) * (3:ℤ)^(s+1) = (3:ℤ)^(2*s+2) := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨(m₀ : ℤ), ?_⟩
  linear_combination (2*(u:ℤ)) * h4ℤ + (3:ℤ)^(s+1) * hcongℤ + (m₀:ℤ) * hexpℤ

/-- **The Mahler witness (document §6-§7).**  A ghost ray makes the
integer sequence
`W_s = 2u(4^(3^s) - 1) - (6a - 27) * 3^s`
divisible by `3^(2s+2)` at every depth `s ≥ 2`: the rational sequence
`(4^(3^s) - 1) / 3^s` converges 3-adically to the rational
`(6a - 27) / (2u)`. -/
theorem ghost_witness (u : Nat) (hg : GhostRay u) (s : Nat) (hs : 2 ≤ s) :
    ∃ m : ℤ, (2*(u:ℤ) * ((4:ℤ)^(3^s) - 1)
        - ((6*(((GSTTowerFire.c 1 * u) % 9 : Nat) : ℤ) - 27) * (3:ℤ)^s))
      = (3:ℤ)^(2*s+2) * m := by
  obtain ⟨m, hm⟩ := ghost_tower_lock u hg s hs
  refine ⟨m, ?_⟩
  have hring : ((6*(((GSTTowerFire.c 1 * u) % 9 : Nat) : ℤ) - 27) * (3:ℤ)^s)
      = (2*(((GSTTowerFire.c 1 * u) % 9 : Nat) : ℤ) - 9) * (3:ℤ)^(s+1) := by
    rw [pow_succ]
    ring
  linear_combination hring + hm

/-- **The witness convergence.**  For every target precision `k` there
is a depth `S` such that all deeper witnesses are divisible by `3^k`. -/
theorem ghost_convergence (u : Nat) (hg : GhostRay u) :
    ∀ (k : Nat), ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (2*(u:ℤ) * ((4:ℤ)^(3^s) - 1)
        - ((6*(((GSTTowerFire.c 1 * u) % 9 : Nat) : ℤ) - 27) * (3:ℤ)^s)) := by
  intro k
  refine ⟨max 2 k, ?_⟩
  intro s hs
  obtain ⟨m, hm⟩ := ghost_witness u hg s (by omega)
  exact (pow_dvd_pow (3:ℤ) (by omega)).trans ⟨m, hm⟩

/-- **GHOST RELATIVE-PRECISION AMPLIFICATION.**
A ghost ray yields more than ordinary 3-adic convergence: for every fixed
relative precision q, all sufficiently deep sheet-s witnesses are divisible
by 3^(s+q). -/
theorem ghost_relative_precision
    (u : Nat) (hg : GhostRay u) (q : Nat) :
    ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^(s+q) ∣
        (2*(u:ℤ) * ((4:ℤ)^(3^s) - 1)
          - ((6*(((GSTTowerFire.c 1 * u) % 9 : Nat) : ℤ) - 27)
            * (3:ℤ)^s)) := by
  refine ⟨max 2 q, ?_⟩
  intro s hs
  obtain ⟨m,hm⟩ := ghost_witness u hg s (by omega)
  have hexp : s+q ≤ 2*s+2 := by omega
  exact (pow_dvd_pow (3:ℤ) hexp).trans ⟨m,hm⟩

/-- The relative precision can be made arbitrarily far above the baseline
sheet precision, while retaining the same fixed ghost head. -/
theorem ghost_unbounded_relative_precision
    (u : Nat) (hg : GhostRay u) :
    ∀ q : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^(s+q) ∣
        (2*(u:ℤ) * ((4:ℤ)^(3^s) - 1)
          - ((6*(((GSTTowerFire.c 1 * u) % 9 : Nat) : ℤ) - 27)
            * (3:ℤ)^s)) :=
  ghost_relative_precision u hg

/-! ## §6 The canonical head is a three-adic unit -/

/-- The ghost head \`a = (c 1 * u) % 9\` is not divisible by three: the
tower coefficient is a 3-adic unit and the core is three-free. -/
theorem ghost_head_unit (u : Nat) (h3 : ¬ 3 ∣ u) :
    ¬ 3 ∣ (GSTTowerFire.c 1 * u) % 9 := by
  intro hd
  apply h3
  have hmod3 : ((GSTTowerFire.c 1 * u) % 9) % 3
      = (GSTTowerFire.c 1 * u) % 3 :=
    Nat.mod_mod_of_dvd (GSTTowerFire.c 1 * u) (by decide : (3:Nat) ∣ 9)
  have hcm : (GSTTowerFire.c 1 * u) % 3 = u % 3 := by
    rw [Nat.mul_mod, GSTTowerFire.c_mod3]
    omega
  have h0 : ((GSTTowerFire.c 1 * u) % 9) % 3 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp hd
  have : u % 3 = 0 := by omega
  exact Nat.dvd_iff_mod_eq_zero.mpr this

/-- A three-free ghost head lies in exactly one of the six nonzero
residue classes modulo nine. -/
theorem ghost_head_residue_spectrum
    (u : Nat) (h3 : ¬ 3 ∣ u) :
    let a := (GSTTowerFire.c 1 * u) % 9
    a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 7 ∨ a = 8 := by
  dsimp only
  have ha : (GSTTowerFire.c 1 * u) % 9 < 9 :=
    Nat.mod_lt _ (by decide)
  have hunit := ghost_head_unit u h3
  have hmod : (GSTTowerFire.c 1 * u) % 9 % 3 ≠ 0 := by
    intro h
    exact hunit (Nat.dvd_iff_mod_eq_zero.mpr h)
  omega

/-! ## §7 The three-free decomposition socket -/

/-- Every positive natural decomposes as \`3^s * u\` with \`u\` three-free.
This is retained as the finite bridge consumed by the relative-precision
Worldtrace–Mahler theory. -/
theorem exists_three_free_decomp :
    ∀ (fuel K : Nat), 1 ≤ K → K ≤ fuel →
      ∃ s u : Nat, K = 3^s * u ∧ ¬ 3 ∣ u := by
  intro fuel
  induction fuel with
  | zero => intro K hK hKF; omega
  | succ fuel ih =>
      intro K hK hKF
      by_cases h3 : 3 ∣ K
      · obtain ⟨K', hK'⟩ := h3
        have hK'1 : 1 ≤ K' := by omega
        have hlt : K' ≤ fuel := by omega
        obtain ⟨s, u, hsu, hu⟩ := ih K' hK'1 hlt
        refine ⟨s+1, u, ?_, hu⟩
        calc K = 3 * K' := hK'
          _ = 3 * (3^s * u) := by rw [hsu]
          _ = 3^(s+1) * u := by rw [Nat.pow_succ]; ring
      · exact ⟨0, K, by simp, h3⟩

/-! ## §8 Receipts

The obsolete fixed-precision/two-input terminal socket has been removed.
Its production replacement is the relative-precision Worldtrace–Mahler
theory in `GSTWorldtraceMahlerRelativePrecision`.

-/

#print axioms ghost_tower_lock
#print axioms ghost_witness
#print axioms ghost_convergence
#print axioms ghost_relative_precision
#print axioms ghost_unbounded_relative_precision
#print axioms ghost_head_unit
#print axioms ghost_head_residue_spectrum
#print axioms exists_three_free_decomp

end GSTGhostRay
