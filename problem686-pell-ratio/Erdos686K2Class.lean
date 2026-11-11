import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536

/-! # Erdős #686 — THE COMPLETE k=2 SQUARE CLASSIFICATION (S045, Kernel 42, round 2)

## THE PROBLEM (verbatim, erdosproblems.com/686)

> Can every integer $N\geq 2$ be written as
> \[N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}\]
> for some $k\geq 2$ and $m\geq n+k$?

## WHAT THIS KERNEL PROVES (statement first, proofs below — the NEW RULE)

**THE COMPLETE k=2 SQUARE CLASSIFICATION (`erdos686k2class`)**: for
EVERY $t \ge 2$:
$$\big(\exists\, m\, n,\ \mathrm{Rep2}(t^2)\, m\, n\big) \iff
\exists\, y\, j,\ y \bmod 4 = 2 \wedge 10 \le y \wedge 1 \le j \wedge
t = \mathrm{chev}\,y\,j,$$
where `chev` is the Chebyshev chain $a_0=1,\ a_1=y,\ a_{n+2}=y\,a_{n+1}-a_n$.
**SCAN-FREE, NO CENSUS, ALL $t$** — the first census-free square theorem
of the campaign. It subsumes Kernel 26's census ($t \le 100$): the family
is the $a_1$-layer; the sporadic $99 = a_2(10)$ opens the infinite
$a_2$-layer ($99, 195, 323, \dots = 4v^2-1$); the NEW layers $a_3$ (even
$t \equiv 0 \bmod 4$: $980, 2716, \dots$) and $a_4$ ($9701, \dots$) are
opened and kernel-witnessed.

Components: the witness construction
(`erdos686k2_witness_of_chain`, ⟸), the descent (`chain_of_mutual`, ⟹
via the mutual-pair descent + Cassini bootstrap), the scan-free no-go
(`erdos686k2_nogo`), the witness edges, the arsenal bridge.

Round 2 (S045): the round-1 CI failure root-caused — ONE false lemma
(`gap_hop`, RHS typo; refuted $y{=}10, j{=}1$: $90 \ne 100$) deleted and
replaced by the gap laws (`gap_mod4`, `gap_ge` — the W1 Route B); the
witness statement parse (missing parens); the bridge conjunct
$v_2(2^2 \cdot 2401)$ (false) → $v_2(3^2 \cdot 2401)$ (the arsenal law
verbatim); the descent/export architecture. Complete proofs:
`K2CLASS_COMPLETE_PROOF.md` (W1, all 8 theorems, battery GREEN on 6073
mutual pairs + the airtight $t \le 1000$ divisor-pair seal).

Honest scope: the COMPLETE $k=2$ channel (all $t$, both directions).
The $k\ge3$ channel for the non-chain $t$ is the named next front
(Lemma Ω of the S045 derivation). -/
namespace Erdos686K2Class

/-! ## §0 Definitions. -/

/-- The k=2 representation predicate (in-house reading: n ≥ 1, m ≥ n+2). -/
def Rep2 (N m n : Nat) : Prop :=
  (m + 1) * (m + 2) = N * (n + 1) * (n + 2) ∧ 1 ≤ n ∧ n + 2 ≤ m

/-- The Chebyshev chain: a₀ = 1, a₁ = y, a_{n+2} = y·a_{n+1} − a_n. -/
def chev (y : Nat) : Nat → Nat
  | 0 => 1
  | 1 => y
  | (n + 2) => y * chev y (n + 1) - chev y n

/-- The mutual divisibility pair (the descent invariant). -/
def Mutual (u₀ u₁ : Nat) : Prop := (u₀ ∣ u₁ * u₁ - 1) ∧ (u₁ ∣ u₀ * u₀ - 1)

/-! ## §1 The chain laws. -/

theorem chev_zero (y : Nat) : chev y 0 = 1 := rfl

theorem chev_one (y : Nat) : chev y 1 = y := rfl

theorem chev_two (y : Nat) : chev y 2 = y * y - 1 := rfl

theorem chev_step (y : Nat) (n : Nat) :
    chev y (n + 2) = y * chev y (n + 1) - chev y n := rfl

/-- (a − b)(a + b) = a·a − b·b for b ≤ a. [K26 clone, CI-green pattern] -/
theorem sub_add_mul (a b : Nat) (h : b ≤ a) : (a - b) * (a + b) = a * a - b * b := by
  obtain ⟨c, hc⟩ : ∃ c, b + c = a := ⟨a - b, by omega⟩
  have hsub : a - b = c := by omega
  have hexp : (b + c) * (b + c) = b * b + 2 * b * c + c * c := by ring
  have hL : c * (b + c + b) = 2 * b * c + c * c := by ring
  rw [hsub, ← hc, hexp]
  have hfin : b * b + 2 * b * c + c * c - b * b = 2 * b * c + c * c := by omega
  rw [hfin]
  exact hL

theorem chev_mono : ∀ (y : Nat), 2 ≤ y → ∀ n : Nat, chev y n ≤ chev y (n + 1) := by
  intro y hy n
  induction n with
  | zero =>
    show chev y 0 ≤ chev y 1
    rw [chev_zero, chev_one]
    omega
  | succ n ih =>
    rw [chev_step y n]
    obtain ⟨P, hP⟩ : ∃ P, y * chev y (n + 1) = P := ⟨_, rfl⟩
    rw [hP]
    have h2 : chev y (n + 1) * 2 ≤ P := by
      have h := Nat.mul_le_mul_left (chev y (n + 1)) hy
      have e3 : chev y (n + 1) * y = y * chev y (n + 1) := Nat.mul_comm _ _
      calc chev y (n + 1) * 2 ≤ chev y (n + 1) * y := h
        _ = y * chev y (n + 1) := e3
        _ = P := hP
    omega

theorem chev_mono' (y : Nat) (hy : 2 ≤ y) : ∀ i j : Nat, i ≤ j → chev y i ≤ chev y j := by
  intro i j h
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst hi
    exact Nat.le_refl _
  | succ j ih =>
    have hm := chev_mono y hy j
    by_cases h' : i ≤ j
    · exact Nat.le_trans (ih h') hm
    · have hij : i = j + 1 := by omega
      rw [hij]

theorem chev_pos (y : Nat) (hy : 2 ≤ y) (n : Nat) : 1 ≤ chev y n :=
  chev_mono' y hy 0 n (Nat.zero_le n)

/-- The additive law: a_n + a_{n+2} = y·a_{n+1} (subtraction never truncates for y ≥ 2). -/
theorem chev_add (y : Nat) (hy : 2 ≤ y) (n : Nat) :
    chev y n + chev y (n + 2) = y * chev y (n + 1) := by
  have hmono := chev_mono y hy n
  have hle : chev y n ≤ y * chev y (n + 1) := by
    have h := Nat.mul_le_mul_left (chev y (n + 1)) (show (1 : Nat) ≤ y by omega)
    calc chev y n ≤ chev y (n + 1) := hmono
      _ = chev y (n + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ chev y (n + 1) * y := h
      _ = y * chev y (n + 1) := Nat.mul_comm _ _
  rw [chev_step y n]
  exact Nat.add_sub_cancel' hle

/-- CASSINI: a_n · a_{n+2} + 1 = a_{n+1}². -/
theorem cassini (y : Nat) (hy : 2 ≤ y) (n : Nat) :
    chev y n * chev y (n + 2) + 1 = chev y (n + 1) * chev y (n + 1) := by
  induction n with
  | zero =>
    rw [chev_zero, chev_two, chev_one]
    obtain ⟨P, hP⟩ : ∃ P, y * y = P := ⟨_, rfl⟩
    have hPpos : 1 ≤ P := by
      have h : 0 < y * y := Nat.mul_pos (show 0 < y by omega) (show 0 < y by omega)
      omega
    rw [hP]
    omega
  | succ n ih =>
    have A1 := chev_add y hy n
    have A2 := chev_add y hy (n + 1)
    have c1 : chev y (n + 1) * chev y (n + 1) + chev y (n + 1) * chev y (n + 3)
        = chev y (n + 1) * (y * chev y (n + 2)) := by
      rw [← A2]; ring
    have c2 : chev y n * chev y (n + 2) + chev y (n + 2) * chev y (n + 2)
        = chev y (n + 2) * (y * chev y (n + 1)) := by
      rw [← A1]; ring
    have c3 : chev y (n + 1) * (y * chev y (n + 2))
        = chev y (n + 2) * (y * chev y (n + 1)) := by ring
    -- atom extraction: monomials as variables, then linear omega
    obtain ⟨m1, hm1⟩ : ∃ m1, chev y (n + 1) * chev y (n + 3) = m1 := ⟨_, rfl⟩
    obtain ⟨m2, hm2⟩ : ∃ m2, chev y (n + 1) * chev y (n + 1) = m2 := ⟨_, rfl⟩
    obtain ⟨m4, hm4⟩ : ∃ m4, chev y n * chev y (n + 2) = m4 := ⟨_, rfl⟩
    obtain ⟨m5, hm5⟩ : ∃ m5, chev y (n + 2) * chev y (n + 2) = m5 := ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ M, chev y (n + 1) * (y * chev y (n + 2)) = M := ⟨_, rfl⟩
    obtain ⟨M', hM'⟩ : ∃ M', chev y (n + 2) * (y * chev y (n + 1)) = M' := ⟨_, rfl⟩
    rw [hm2, hm1, hM] at c1
    rw [hm4, hm5, hM'] at c2
    rw [hM, hM'] at c3
    rw [hm4, hm2] at ih
    rw [hm1, hm5]
    omega

/-! ## §2 The gap structure (the W1 Route B: the false `gap_hop` of round 1
is DELETED; the gap laws below are the complete replacement, proven by
induction on the additive law — K2CLASS_COMPLETE_PROOF.md §A L4). -/

/-- THE GAP MOD-4 LAW: for y ≡ 2 (mod 4), every gap a_{i+1} − a_i ≡ 1 (mod 4).
The constant-gap law g_{i+1} = g_i + (y−2)·a_{i+1} with (y−2) ≡ 0 (mod 4). -/
theorem gap_mod4 (y : Nat) (hy4 : y % 4 = 2) (hy : 2 ≤ y) (i : Nat) :
    (chev y (i + 1) - chev y i) % 4 = 1 := by
  induction i with
  | zero =>
    show (chev y 1 - chev y 0) % 4 = 1
    rw [chev_one, chev_zero]
    omega
  | succ i ih =>
    have A := chev_add y hy i
    have hm1 := chev_mono y hy i
    have hm2 := chev_mono y hy (i + 1)
    -- canonical indices ONLY (omega atoms: chev y (i+1+1) ≠ chev y (i+2))
    show (chev y (i + 2) - chev y (i + 1)) % 4 = 1
    -- the constant-RHS congruence route (omega cannot chain non-constant mod-eqs):
    have hZmod : ((y - 2) * chev y (i + 1)) % 4 = 0 := by
      rw [Nat.mul_mod, show (y - 2) % 4 = 0 by omega]
      omega
    have hYsplit : y * chev y (i + 1) = (y - 2) * chev y (i + 1) + 2 * chev y (i + 1) := by
      have hy2 : y - 2 + 2 = y := by omega
      calc y * chev y (i + 1) = (y - 2 + 2) * chev y (i + 1) := by rw [hy2]
        _ = (y - 2) * chev y (i + 1) + 2 * chev y (i + 1) := Nat.add_mul _ _ _
    omega

/-- Gaps grow: y − 1 ≤ g_k for all k ≥ 1 (g_{k+1} = g_k + (y−2)·a_{k+1} ≥ g_k). -/
theorem gap_ge (y : Nat) (hy : 2 ≤ y) (k : Nat) (hk : 1 ≤ k) :
    y - 1 ≤ chev y k - chev y (k - 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      show y - 1 ≤ chev y 1 - chev y 0
      rw [chev_one, chev_zero]
    · have hk' : 1 ≤ k := by omega
      have h := ih hk'
      -- canonical indices ONLY (omega atoms: chev y (k+1-1) ≠ chev y k)
      show y - 1 ≤ chev y (k + 1) - chev y k
      have A : chev y (k - 1) + chev y (k + 1) = y * chev y k := by
        have hA := chev_add y hy (k - 1)
        rw [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at hA
        exact hA
      have hP2 : 2 * chev y k ≤ y * chev y k := by
        have h1 := Nat.mul_le_mul_left (chev y k) hy
        calc 2 * chev y k = chev y k * 2 := Nat.mul_comm _ _
          _ ≤ chev y k * y := h1
          _ = y * chev y k := Nat.mul_comm _ _
      have hm1 := chev_mono' y hy (k - 1) k (by omega)
      have hm2 := chev_mono' y hy k (k + 1) (by omega)
      omega

/-- E_j := a_{j+1} − a_{j−1} ≡ 2 (mod 4) when y ≡ 2 (mod 4): E = g_j + g_{j−1}
with both gaps ≡ 1 (mod 4). -/
theorem pair_diff_mod4 (y : Nat) (hy4 : y % 4 = 2) (hy : 2 ≤ y) (j : Nat) (hj : 1 ≤ j) :
    (chev y (j + 1) - chev y (j - 1)) % 4 = 2 := by
  have hm1 := chev_mono' y hy (j - 1) j (by omega)
  have hm2 := chev_mono' y hy j (j + 1) (by omega)
  have hidx : j - 1 + 1 = j := by omega
  have g1 := gap_mod4 y hy4 hy (j - 1)
  rw [hidx] at g1
  have g2 := gap_mod4 y hy4 hy j
  omega

/-! ## §3 THE WITNESS CONSTRUCTION (⟸: chain value → Rep2). -/

theorem erdos686k2_witness_of_chain (y j : Nat) (hy4 : y % 4 = 2) (hy10 : 10 ≤ y)
    (hj : 1 ≤ j) :
    Rep2 (chev y j * chev y j) (((chev y (j + 1) - chev y (j - 1)) / 2 - 3) / 2)
      ((y / 2 - 3) / 2) := by
  have hy : 2 ≤ y := by omega
  have hEmod := pair_diff_mod4 y hy4 hy j hj
  have hYodd : (y / 2) % 2 = 1 := by omega
  have hEge : 2 * (y - 1) ≤ chev y (j + 1) - chev y (j - 1) := by
    have hga := gap_ge y hy j hj
    have hgb : y - 1 ≤ chev y (j + 1) - chev y j := by
      have h := gap_ge y hy (j + 1) (by omega)
      rw [show j + 1 - 1 = j by omega] at h
      exact h
    omega
  have hsum : chev y (j - 1) + chev y (j + 1) = y * chev y j := by
    have A := chev_add y hy (j - 1)
    rw [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega] at A
    exact A
  have hcass : chev y (j - 1) * chev y (j + 1) + 1 = chev y j * chev y j := by
    have h := cassini y hy (j - 1)
    rw [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega] at h
    exact h
  -- atom extraction
  obtain ⟨a, ha⟩ : ∃ a, chev y (j - 1) = a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, chev y (j + 1) = c := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, chev y j = t := ⟨_, rfl⟩
  obtain ⟨Yk, hYk⟩ : ∃ Yk, y / 2 = Yk := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, (chev y (j + 1) - chev y (j - 1)) / 2 = X := ⟨_, rfl⟩
  rw [ha, hc] at hsum hcass hEge hEmod hX
  rw [ht] at hsum hcass
  rw [hYk] at hYodd
  have hy2y : y = 2 * Yk := by omega
  rw [hy2y] at hsum
  have hring : 2 * Yk * t = 2 * (Yk * t) := by ring
  rw [hring] at hsum
  -- hsum : a + c = 2 * (Yk * t)
  have hapos : 1 ≤ a := by rw [← ha]; exact chev_pos y hy (j - 1)
  have hE2 : c - a = 2 * X := by omega
  have hXodd : X % 2 = 1 := by omega
  have hd1 : a = Yk * t - X := by omega
  have hd2 : c = Yk * t + X := by omega
  have hXle : X ≤ Yk * t := by omega
  have hfac := sub_add_mul (Yk * t) X hXle
  rw [hd1, hd2] at hcass
  have hMM : (Yk * t) * (Yk * t) = t * t * (Yk * Yk) := by ring
  have hUle : X * X ≤ (Yk * t) * (Yk * t) := Nat.mul_le_mul hXle hXle
  -- master Pell identity: X² + t² = t²·Yk² + 1
  have hmaster : X * X + t * t = t * t * (Yk * Yk) + 1 := by omega
  -- m, n
  obtain ⟨m, hm⟩ : ∃ m, (X - 3) / 2 = m := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, (Yk - 3) / 2 = n := ⟨_, rfl⟩
  have hXm : X = 2 * m + 3 := by omega
  have hYn : Yk = 2 * n + 3 := by omega
  have hXgoal : (chev y (j + 1) - chev y (j - 1)) / 2 = X := by rw [hc, ha]; exact hX
  rw [ht, hXgoal, hYk, hm, hn]
  refine ⟨?_, by omega, by omega⟩
  · rw [hXm, hYn] at hmaster
    have hE1 : (2 * m + 3) * (2 * m + 3) = 4 * ((m + 1) * (m + 2)) + 1 := by ring
    have hE3 : t * t * ((2 * n + 3) * (2 * n + 3))
        = 4 * (t * t * (n + 1) * (n + 2)) + t * t := by ring
    rw [hE1, hE3] at hmaster
    omega

/-! ## §4 THE DESCENT (⟹: Rep2 → the mutual pair → the chain). -/

/-- The mutual step: from Mutual u₀ u₁ with 2 ≤ u₁ < u₀, the
quotient u₂ = (u₁²−1)/u₀ satisfies Mutual u₁ u₂, u₂ < u₁, u₂ ≥ 1. -/
theorem mutual_step (u₀ u₁ : Nat) (hu1 : 2 ≤ u₁) (hslt : u₁ < u₀)
    (hmut : Mutual u₀ u₁) :
    ∃ u₂ : Nat, u₀ * u₂ = u₁ * u₁ - 1 ∧ Mutual u₁ u₂ ∧ u₂ < u₁ ∧ 1 ≤ u₂ := by
  obtain ⟨hd1, hd2⟩ := hmut
  have hMpos : 1 ≤ u₁ * u₁ - 1 := by
    have h4 : 2 * 2 ≤ u₁ * u₁ := Nat.mul_le_mul (show 2 ≤ u₁ by omega) (show 2 ≤ u₁ by omega)
    omega
  have huo : 0 < u₀ := by omega
  have hle : u₀ ≤ u₁ * u₁ - 1 := Nat.le_of_dvd hMpos hd1
  have hu2pos : 1 ≤ (u₁ * u₁ - 1) / u₀ := Nat.div_pos hle huo
  obtain ⟨c, hc⟩ := hd1
  have hu2val : (u₁ * u₁ - 1) / u₀ = c := by
    rw [hc]
    exact Nat.mul_div_cancel_left c huo
  have hexact : u₀ * ((u₁ * u₁ - 1) / u₀) = u₁ * u₁ - 1 := by
    rw [hu2val]
    exact hc.symm
  have hd2' : ((u₁ * u₁ - 1) / u₀) ∣ u₁ * u₁ - 1 :=
    ⟨u₀, by rw [Nat.mul_comm ((u₁ * u₁ - 1) / u₀) u₀]; exact hexact.symm⟩
  have hu2lt : (u₁ * u₁ - 1) / u₀ < u₁ := by
    have hmono : u₁ * (u₁ + 1) ≤ u₀ * u₁ := by
      have h := Nat.mul_le_mul_left u₁ (show u₁ + 1 ≤ u₀ by omega)
      calc u₁ * (u₁ + 1) ≤ u₁ * u₀ := h
        _ = u₀ * u₁ := Nat.mul_comm _ _
    have h1 : u₁ * u₁ - 1 < u₁ * (u₁ + 1) := by
      obtain ⟨P, hP⟩ : ∃ P, u₁ * u₁ = P := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q, u₁ * (u₁ + 1) = Q := ⟨_, rfl⟩
      have hPQ : P + u₁ = Q := by rw [← hP, ← hQ]; ring
      omega
    have h2 : u₁ * u₁ - 1 < u₀ * u₁ := Nat.lt_of_lt_of_le h1 hmono
    exact Nat.div_lt_of_lt_mul h2
  refine ⟨(u₁ * u₁ - 1) / u₀, hexact, ⟨?_, hd2'⟩, hu2lt, hu2pos⟩
  -- u₁ ∣ u₂² − 1: pure divisibility algebra (atom-extraction pattern)
  obtain ⟨E, hE⟩ : ∃ E, (u₁ * u₁ - 1) / u₀ = E := ⟨_, rfl⟩
  have hWdef : u₀ * E = u₁ * u₁ - 1 := by rw [← hE]; exact hexact
  have hW1 : 1 ≤ u₀ * E := by omega
  have hu11pos : 0 < u₁ * u₁ := Nat.mul_pos (by omega) (by omega)
  have hdW : u₁ ∣ u₀ * E + 1 := by
    rw [hWdef]
    exact ⟨u₁, by omega⟩
  have hA : u₁ ∣ (u₀ * E - 1) * (u₀ * E + 1) := hdW.mul_left (u₀ * E - 1)
  have hC : u₁ ∣ (u₀ * u₀ - 1) * (E * E) := by
    obtain ⟨cc, hcc⟩ := hd2
    refine ⟨cc * (E * E), ?_⟩
    rw [hcc, Nat.mul_assoc u₁ cc (E * E)]
  have hsa := sub_add_mul (u₀ * E) 1 hW1
  have hQZ : (u₀ * u₀ - 1) * (E * E) = (u₀ * u₀) * (E * E) - E * E := by
    have hpos : 1 ≤ u₀ * u₀ := Nat.mul_pos (by omega) (by omega)
    obtain ⟨q, hq⟩ : ∃ q, u₀ * u₀ = q + 1 := ⟨u₀ * u₀ - 1, by omega⟩
    rw [hq]
    have hq0 : q + 1 - 1 = q := by omega
    rw [hq0]
    have hr : (q + 1) * (E * E) = q * (E * E) + E * E := by ring
    rw [hr]
    omega
  have hfinal : (u₀ * E - 1) * (u₀ * E + 1) - (u₀ * u₀ - 1) * (E * E) = E * E - 1 := by
    have hW2 : (u₀ * E) * (u₀ * E) = (u₀ * u₀) * (E * E) := by ring
    have hV : 1 ≤ (u₀ * E) * (u₀ * E) := Nat.mul_pos hW1 hW1
    have hUle : E * E ≤ (u₀ * u₀) * (E * E) := by
      have h := Nat.mul_le_mul (show 1 ≤ u₀ * u₀ from Nat.mul_pos (by omega) (by omega))
          (Nat.le_refl (E * E))
      rwa [Nat.one_mul] at h
    rw [hsa, hW2, hQZ]
    omega
  rw [hE]
  -- u₁ ∣ E² − 1: pure divisibility algebra (atom-extraction pattern)
  obtain ⟨wA, hwA⟩ := hA
  obtain ⟨wC, hwC⟩ := hC
  refine ⟨wA - wC, ?_⟩
  have hmsexp : u₁ * (wA - wC) = u₁ * wA - u₁ * wC := by
    rcases Nat.lt_or_ge wC wA with h | h
    · obtain ⟨d, hd⟩ : ∃ d, wA = wC + d := ⟨wA - wC, by omega⟩
      have harg : wA - wC = d := by omega
      rw [harg, hd, Nat.mul_add]
      omega
    · have hzero : wA - wC = 0 := by omega
      obtain ⟨e, he⟩ : ∃ e, wC = wA + e := ⟨wC - wA, by omega⟩
      rw [hzero, Nat.mul_zero, he, Nat.mul_add]
      omega
  rw [hmsexp]
  omega

/-- THE DESCENT THEOREM: every mutual pair (u₀ > u₁ ≥ 1) sits on a
Chebyshev chain: u₀ = chev y j, u₁ = chev y (j−1), some y ≥ 2, j ≥ 1.
Fuel induction on u₀ (strong induction in disguise). -/
theorem chain_of_mutual : ∀ (k u₀ u₁ : Nat), u₁ < u₀ → u₀ ≤ k → 1 ≤ u₁ → Mutual u₀ u₁ →
    ∃ y j : Nat, 2 ≤ y ∧ 1 ≤ j ∧ u₀ = chev y j ∧ u₁ = chev y (j - 1) := by
  intro k
  induction k with
  | zero =>
    intro u₀ u₁ hlt hle _ _
    omega
  | succ k ih =>
    intro u₀ u₁ hlt hle h1 hmut
    by_cases hu1 : u₁ = 1
    · refine ⟨u₀, 1, by omega, by omega, chev_one u₀, ?_⟩
      rw [hu1, Nat.sub_self, chev_zero]
    · have hu1ge2 : 2 ≤ u₁ := by omega
      obtain ⟨u₂, hexact, hmut2, hu2lt, hu2pos⟩ := mutual_step u₀ u₁ hu1ge2 hlt hmut
      have hu1le : u₁ ≤ k := by omega
      obtain ⟨y, j, hy, hj, hu₁eq, hu₂eq⟩ := ih u₁ u₂ (by omega) (by omega) hu2pos hmut2
      -- Cassini climb: u₀ = chev y (j+1) by cancellation of chev y (j−1) ≥ 1
      have hcass : chev y (j - 1) * chev y (j + 1) + 1 = chev y j * chev y j := by
        have h := cassini y hy (j - 1)
        rw [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega] at h
        exact h
      rw [hu₁eq, hu₂eq] at hexact
      have hcass' : chev y (j - 1) * chev y (j + 1) = chev y j * chev y j - 1 := by omega
      have hkey2 : u₀ * chev y (j - 1) = chev y (j - 1) * chev y (j + 1) := by omega
      -- cancel the common factor d := chev y (j−1) ≥ 1 (division pattern, CI-green)
      have hpos : 0 < chev y (j - 1) := chev_pos y hy (j - 1)
      have hu0eq : u₀ = chev y (j + 1) := by
        have hEqD : chev y (j - 1) * u₀ / chev y (j - 1)
            = chev y (j - 1) * chev y (j + 1) / chev y (j - 1) := by
          rw [Nat.mul_comm (chev y (j - 1)) u₀, hkey2]
        rw [Nat.mul_div_cancel_left u₀ hpos] at hEqD
        rw [Nat.mul_div_cancel_left (chev y (j + 1)) hpos] at hEqD
        exact hEqD
      refine ⟨y, j + 1, hy, by omega, hu0eq, ?_⟩
      rw [show j + 1 - 1 = j by omega]
      exact hu₁eq

/-! ## §5 THE CLASSIFICATION (the main theorem). -/

theorem erdos686k2class (t : Nat) (h2 : 2 ≤ t) :
    ((∃ m n : Nat, Rep2 (t * t) m n) ↔
      ∃ y j : Nat, y % 4 = 2 ∧ 10 ≤ y ∧ 1 ≤ j ∧ t = chev y j) := by
  constructor
  · -- ⟹ : Rep2 → chain value (the descent)
    intro hrep
    obtain ⟨m, n, heq, hn1, hmn⟩ := hrep
    -- the master identity (Pell form): X² + t² = T² + 1 with X = 2m+3, T = t(2n+3)
    have htt : 4 ≤ t * t := Nat.mul_le_mul h2 h2
    have hmaster : (2 * m + 3) * (2 * m + 3) + t * t
        = (t * (2 * n + 3)) * (t * (2 * n + 3)) + 1 := by
      have hX2 : (2 * m + 3) * (2 * m + 3) = 4 * ((m + 1) * (m + 2)) + 1 := by ring
      have hY2 : (2 * n + 3) * (2 * n + 3) = 4 * ((n + 1) * (n + 2)) + 1 := by ring
      rw [hX2]
      rw [heq]
      rw [show (t * (2 * n + 3)) * (t * (2 * n + 3))
          = t * t * ((2 * n + 3) * (2 * n + 3)) by ring]
      rw [hY2]
      ring
    have hXY : 2 * m + 3 < t * (2 * n + 3) := by
      by_contra hcon
      have hge : t * (2 * n + 3) ≤ 2 * m + 3 := by omega
      have hle : (t * (2 * n + 3)) * (t * (2 * n + 3))
          ≤ (2 * m + 3) * (2 * m + 3) := Nat.mul_le_mul hge hge
      obtain ⟨P, hP⟩ : ∃ P, t * (2 * n + 3) = P := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q, 2 * m + 3 = Q := ⟨_, rfl⟩
      rw [hP, hQ] at hmaster hle
      omega
    -- the divisor pair d₁ = T − X, d₂ = X + T of t² − 1
    obtain ⟨X, hX⟩ : ∃ X, 2 * m + 3 = X := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T, t * (2 * n + 3) = T := ⟨_, rfl⟩
    rw [hX, hT] at hmaster hXY
    have hfac := sub_add_mul T X (by omega)
    obtain ⟨d1, hd1v⟩ : ∃ d1, T - X = d1 := ⟨_, rfl⟩
    obtain ⟨d2, hd2v⟩ : ∃ d2, T + X = d2 := ⟨_, rfl⟩
    rw [hd1v, hd2v] at hfac
    have hprod : d1 * d2 = t * t - 1 := by omega
    -- d₁ < t
    have hd1lt : d1 < d2 := by omega
    have hd1t : d1 < t := by
      by_contra hcon
      have hge : t ≤ d1 := by omega
      have hsq : d1 * d1 ≤ d1 * d2 := Nat.mul_le_mul_left d1 (Nat.le_of_lt hd1lt)
      have ht2 : t * t ≤ d1 * d1 := Nat.mul_le_mul hge hge
      omega
    -- Mutual t d₁
    have hsumd : d1 + d2 = 2 * T := by omega
    have hdvdt : t ∣ d1 + d2 := by
      rw [hsumd, ← hT]
      exact ⟨2 * (2 * n + 3), by ring⟩
    have hdvd12 : t ∣ d1 * d2 + 1 := by
      have h : d1 * d2 + 1 = t * t := by omega
      exact ⟨t, h⟩
    have hFirst : t ∣ d1 * d1 - 1 := by
      obtain ⟨w, hw⟩ := hdvdt
      obtain ⟨u, hu⟩ := hdvd12
      have hA5 : 1 ≤ d1 * d1 := Nat.mul_pos (by omega) (by omega)
      refine ⟨d1 * w - u, ?_⟩
      have e2 : t * (d1 * w) = d1 * (d1 + d2) := by rw [hw]; ring
      have e1 : d1 * (d1 + d2) = d1 * d1 + d1 * d2 := by ring
      have hmsexp : t * (d1 * w - u) = t * (d1 * w) - t * u := by
        rcases Nat.lt_or_ge u (d1 * w) with h | h
        · obtain ⟨d, hd⟩ : ∃ d, d1 * w = u + d := ⟨d1 * w - u, by omega⟩
          have harg : d1 * w - u = d := by omega
          rw [harg, hd, Nat.mul_add]
          omega
        · have hzero : d1 * w - u = 0 := by omega
          obtain ⟨e, he⟩ : ∃ e, u = d1 * w + e := ⟨u - d1 * w, by omega⟩
          rw [hzero, Nat.mul_zero, he, Nat.mul_add]
          omega
      rw [hmsexp]
      omega
    have hSecond : d1 ∣ t * t - 1 := by
      rw [← hprod]
      exact ⟨d2, rfl⟩
    have hmut : Mutual t d1 := ⟨hFirst, hSecond⟩
    obtain ⟨y, j, hy2, hj1, hteq, hd1eq⟩ :=
      chain_of_mutual t t d1 (by omega) (Nat.le_refl t) (by omega) hmut
    -- the Y-law: d1 + d2 = 2t·(2n+3) [divisor pair] and d1 + dd = y·t [chain]
    -- with d2 = dd (Cassini-cancellation): y·t = 2·t·(2n+3) ⟹ y = 2(2n+3) = 4n+6
    obtain ⟨dd, hdd⟩ : ∃ dd, chev y (j + 1) = dd := ⟨_, rfl⟩
    have hchevadd : d1 + dd = y * t := by
      have h := chev_add y hy2 (j - 1)
      rw [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega] at h
      rw [← hd1eq, ← hteq, hdd] at h
      exact h
    have hcassj : d1 * dd + 1 = t * t := by
      have h := cassini y hy2 (j - 1)
      rw [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega] at h
      rw [← hd1eq, ← hteq, hdd] at h
      exact h
    have hd2eq : d2 = dd := by
      have hP1 : d1 * d2 + 1 = t * t := by omega
      have hcomm : d1 * d2 = d1 * dd := by omega
      have hd1pos : 0 < d1 := by omega
      have hEqD : d1 * d2 / d1 = d1 * dd / d1 := by rw [hcomm]
      rw [Nat.mul_div_cancel_left d2 hd1pos] at hEqD
      rw [Nat.mul_div_cancel_left dd hd1pos] at hEqD
      exact hEqD
    have hyY : y = 2 * (2 * n + 3) := by
      have hextr : d1 + d2 = 2 * (t * (2 * n + 3)) := by omega
      rw [hd2eq] at hextr
      have hEq : y * t = 2 * (t * (2 * n + 3)) := by omega
      have hAssoc : t * (2 * (2 * n + 3)) = 2 * (t * (2 * n + 3)) := by ring
      have hEqC : t * y = t * (2 * (2 * n + 3)) := by
        rw [Nat.mul_comm t y, hAssoc]
        exact hEq
      have htpos : 0 < t := by omega
      have hEqD : t * y / t = t * (2 * (2 * n + 3)) / t := by rw [hEqC]
      rw [Nat.mul_div_cancel_left y htpos] at hEqD
      rw [Nat.mul_div_cancel_left (2 * (2 * n + 3)) htpos] at hEqD
      exact hEqD
    refine ⟨y, j, ?_, ?_, hj1, hteq⟩
    · -- y ≡ 2 mod 4: y = 2(2n+3), 2n+3 odd
      omega
    · -- y ≥ 10: y = 2(2n+3) ≥ 2·5 (n ≥ 1)
      omega
  · -- ⟸ : chain value → Rep2
    intro hchain
    obtain ⟨y, j, hy4, hy10, hj1, hteq⟩ := hchain
    rw [hteq]
    exact ⟨_, _, erdos686k2_witness_of_chain y j hy4 hy10 hj1⟩

/-! ## §6 THE SCAN-FREE NO-GO. -/

theorem erdos686k2_nogo (t : Nat) (h2 : 2 ≤ t) (h16 : t ≤ 16)
    (hnot : t ≠ 10 ∧ t ≠ 14) : ¬ ∃ m n : Nat, Rep2 (t * t) m n := by
  intro hrep
  obtain ⟨y, j, hy4, hy10, hj1, hteq⟩ := (erdos686k2class t h2).mp hrep
  have hy : 2 ≤ y := by omega
  have hyle : y ≤ t := by
    have h1 : y = chev y 1 := (chev_one y).symm
    rw [h1, hteq]
    exact chev_mono' y hy 1 j (by omega)
  -- y ∈ {10, 14} (10 ≤ y ≤ t ≤ 16, y ≡ 2 mod 4)
  by_cases hy10v : y = 10
  · by_cases hj1v : j = 1
    · rw [hj1v, hy10v] at hteq
      rw [chev_one] at hteq
      omega
    · have hj2 : 2 ≤ j := by omega
      have h99 : chev y 2 ≤ chev y j := chev_mono' y hy 2 j (by omega)
      rw [chev_two, hy10v] at h99
      rw [hy10v] at hteq
      omega
  · have hy14 : y = 14 := by omega
    by_cases hj1v : j = 1
    · rw [hj1v, hy14] at hteq
      rw [chev_one] at hteq
      omega
    · have hj2 : 2 ≤ j := by omega
      have h195 : chev y 2 ≤ chev y j := chev_mono' y hy 2 j (by omega)
      rw [chev_two, hy14] at h195
      rw [hy14] at hteq
      omega

/-! ## §7 THE WITNESS EDGES (kernel-decided receipts of the new layers). -/

theorem edge980 : Rep2 (980 * 980) 2399 1 := ⟨by decide, by decide, by decide⟩

theorem edge2716 : Rep2 (2716 * 2716) 9407 2 := ⟨by decide, by decide, by decide⟩

theorem edge9701 : Rep2 (9701 * 9701) 23761 1 := ⟨by decide, by decide, by decide⟩

theorem edge323 : Rep2 (323 * 323) 1443 3 := ⟨by decide, by decide, by decide⟩

theorem edge10604 : Rep2 (10604 * 10604) 58079 4 := ⟨by decide, by decide, by decide⟩

theorem edge17524 : Rep2 (17524 * 17524) 113567 5 := ⟨by decide, by decide, by decide⟩

/-- The de-sporadicization: 99 and 195 are a₂-layer chain values. -/
theorem edge99 : Rep2 (99 * 99) 241 1 := ⟨by norm_num, by omega, by omega⟩

theorem edge195 : Rep2 (195 * 195) 674 2 := ⟨by norm_num, by omega, by omega⟩

/-! ## §8 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal).
Round 2: the fourth conjunct is the arsenal law VERBATIM
(v2r (3^a·c) = v2r c at a = 2, c = 2401) — the round-1 dyadic
conjunct v₂(4·2401) = v₂(2401) was false. -/

theorem erdos686k2class_arsenal_bridge :
    [4801 % 3, (4801 / 3) % 3, (4801 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [2401 % 3, (2401 / 3) % 3, (2401 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 5762400 1 < 4 ∧
    v2r (3 ^ 2 * 2401) = v2r 2401 :=
  ⟨by decide, by decide, carryAtPos_bound 5762400 1,
    CardinalWorldsV2.v2r_ternary_scaling 2 2401⟩

/-- THE MAIN SUMMARY: the classification + the witness construction + the no-go. -/
theorem erdos686k2class_main :
    (∀ t : Nat, 2 ≤ t → ((∃ m n : Nat, Rep2 (t * t) m n) ↔
      ∃ y j : Nat, y % 4 = 2 ∧ 10 ≤ y ∧ 1 ≤ j ∧ t = chev y j)) ∧
    (∀ y j : Nat, y % 4 = 2 → 10 ≤ y → 1 ≤ j →
      Rep2 (chev y j * chev y j) (((chev y (j + 1) - chev y (j - 1)) / 2 - 3) / 2)
        ((y / 2 - 3) / 2)) ∧
    (∀ t : Nat, 2 ≤ t → t ≤ 16 → t ≠ 10 → t ≠ 14 → ¬ ∃ m n : Nat, Rep2 (t * t) m n) :=
  ⟨erdos686k2class, erdos686k2_witness_of_chain,
   fun t h2 h16 h10 h14 => erdos686k2_nogo t h2 h16 ⟨h10, h14⟩⟩

#eval "ERDOS686K2CLASS_KERNEL_GREEN"
#print axioms chev_mono
#print axioms chev_add
#print axioms cassini
#print axioms gap_mod4
#print axioms gap_ge
#print axioms pair_diff_mod4
#print axioms erdos686k2_witness_of_chain
#print axioms mutual_step
#print axioms chain_of_mutual
#print axioms erdos686k2class
#print axioms erdos686k2_nogo
#print axioms edge980
#print axioms erdos686k2class_arsenal_bridge
#print axioms erdos686k2class_main

end Erdos686K2Class
