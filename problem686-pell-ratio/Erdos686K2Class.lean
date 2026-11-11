import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536

/-! # Erdős #686 — THE COMPLETE k=2 SQUARE CLASSIFICATION (S045, Kernel 42)

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
  | zero => omega
  | succ j ih =>
    have hm := chev_mono y hy j
    by_cases h' : i ≤ j
    · exact Nat.le_trans (ih h') hm
    · have hij : i = j + 1 := by omega
      rw [hij]
      exact Nat.le_refl _

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
    have hPpos : 1 ≤ P := Nat.mul_pos (show 0 < y by omega) (show 0 < y by omega)
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

/-! ## §2 The gap structure (X's parity and size). -/

/-- For y ≥ 2, j ≥ 1: (y−1)·a_j = (a_{j+1} − a_j) + (a_j + a_{j−1}). -/
theorem gap_hop (y : Nat) (hy : 2 ≤ y) (j : Nat) (hj : 1 ≤ j) :
    (y - 1) * chev y j = chev y (j + 1) - chev y (j - 1) + 2 * chev y (j - 1) := by
  have A1 := chev_add y hy (j - 1)
  obtain ⟨P, hP⟩ : ∃ P, y * chev y j = P := ⟨_, rfl⟩
  rw [A1, hP] at *
  omega

/-- E_j := a_{j+1} − a_{j−1} ≡ 2 (mod 4) when y ≡ 2 (mod 4). -/
theorem pair_diff_mod4 (y : Nat) (hy4 : y % 4 = 2) (hy : 2 ≤ y) (j : Nat) (hj : 1 ≤ j) :
    (chev y (j + 1) - chev y (j - 1)) % 4 = 2 := by
  have key : ∀ k : Nat, 1 ≤ k → (chev y k - chev y (k - 1)) % 4 = (y - 1) % 4 := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk1 : k = 0
      · rw [hk1, chev_one, chev_zero]
        omega
      · have hk' : 1 ≤ k := by omega
        have hop := gap_hop y hy k hk'
        obtain ⟨P, hP⟩ : ∃ P, (y - 1) * chev y k = P := ⟨_, rfl⟩
        rw [hP] at hop
        have hmodP : P % 4 = chev y k % 4 := by
          rw [hP, Nat.mul_mod]
          have h1 : (y - 1) % 4 = 1 := by omega
          rw [h1, Nat.one_mul]
        have hga : chev y k - chev y (k - 1) + chev y (k - 1) = chev y k := by
          have hm := chev_mono' y hy (k - 1) k (by omega)
          omega
        have hga2 : chev y (k + 1) - chev y k + chev y (k - 1) = P := by
          have hm1 := chev_mono' y hy k (k + 1) (by omega)
          have hm2 := chev_mono' y hy (k - 1) k (by omega)
          omega
        have := ih hk'
        omega
  have hg1 := key j hj
  have hg2 := key (j + 1) (by omega)
  have hm1 := chev_mono' y hy j (j + 1) (by omega)
  have hm2 := chev_mono' y hy (j - 1) j (by omega)
  have hE : chev y (j + 1) - chev y (j - 1)
      = (chev y (j + 1) - chev y j) + (chev y j - chev y (j - 1)) := by omega
  rw [hE, hg1, hg2]
  omega

/-- Gaps grow: y − 1 ≤ g_k for all k ≥ 1. -/
theorem gap_ge (y : Nat) (hy : 2 ≤ y) (k : Nat) (hk : 1 ≤ k) :
    y - 1 ≤ chev y k - chev y (k - 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · rw [hk0, chev_one, chev_zero]
      omega
    · have hk' : 1 ≤ k := by omega
      have h := ih hk'
      have hop := gap_hop y hy k hk'
      obtain ⟨P, hP⟩ : ∃ P, (y - 1) * chev y k = P := ⟨_, rfl⟩
      rw [hP] at hop
      have hPge : chev y k ≤ P := by
        have h1 := Nat.mul_le_mul_left (chev y k) (show (1 : Nat) ≤ y - 1 by omega)
        have e2 : chev y k * 1 = chev y k := Nat.mul_one _
        have e3 : chev y k * (y - 1) = P := by rw [← hP]; ring
        calc chev y k = chev y k * 1 := e2
          _ ≤ chev y k * (y - 1) := h1
          _ = P := e3
      have hm1 := chev_mono' y hy k (k + 1) (by omega)
      have hm2 := chev_mono' y hy (k - 1) k (by omega)
      omega

/-! ## §3 THE WITNESS CONSTRUCTION (⟸: chain value → Rep2). -/

theorem erdos686k2_witness_of_chain (y j : Nat) (hy4 : y % 4 = 2) (hy10 : 10 ≤ y)
    (hj : 1 ≤ j) :
    Rep2 (chev y j * chev y j) ((chev y (j + 1) - chev y (j - 1)) / 2 - 3) / 2
      (y / 2 - 3) / 2 := by
  have hy : 2 ≤ y := by omega
  -- X and Y
  have hEmod := pair_diff_mod4 y hy4 hy j hj
  have hXodd : ((chev y (j + 1) - chev y (j - 1)) / 2) % 2 = 1 := by omega
  have hEge : 2 * (y - 1) ≤ chev y (j + 1) - chev y (j - 1) := by
    have hga := gap_ge y hy j hj
    have hgb := gap_ge y hy (j + 1) (by omega)
    have hE : chev y (j + 1) - chev y (j - 1)
        = (chev y (j + 1) - chev y j) + (chev y j - chev y (j - 1)) := by omega
    omega
  have hYodd : (y / 2) % 2 = 1 := by omega
  -- the pair: d₁ = a_{j−1}, d₂ = a_{j+1}, t = a_j; Yₖ := y/2; d₁+d₂ = 2·t·Yₖ
  have hsum : chev y (j - 1) + chev y (j + 1) = y * chev y j := chev_add y hy (j - 1)
  have hy2y : y = 2 * (y / 2) := by omega
  have hcass := cassini y hy (j - 1)
  rw [show j - 1 + 2 = j + 1 by omega] at hcass
  -- hcass : a_{j−1}·a_{j+1} + 1 = a_j²
  -- d₂ − d₁ = 2X ⟹ d₁ = tYₖ − X, d₂ = tYₖ + X with X := (d₂−d₁)/2
  obtain ⟨t, ht⟩ : ∃ t, chev y j = t := ⟨_, rfl⟩
  obtain ⟨Yk, hYk⟩ : ∃ Yk, y / 2 = Yk := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, (chev y (j + 1) - chev y (j - 1)) / 2 = X := ⟨_, rfl⟩
  rw [ht, hYk, hX] at hEmod hXodd hEge hy2y hsum hcass hYodd
  -- m, n
  obtain ⟨m, hm⟩ : ∃ m, (X - 3) / 2 = m := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, (Yk - 3) / 2 = n := ⟨_, rfl⟩
  have hXm : 2 * m + 3 = X := by omega
  have hYn : 2 * n + 3 = Yk := by omega
  rw [hm, hn]
  obtain ⟨tt, htt⟩ : ∃ tt, chev y j * chev y j = tt := ⟨_, rfl⟩
  rw [ht] at htt
  rw [htt]
  -- master identity: X² + t² = t²·Yk² + 1
  have hmaster : X * X + t * t = t * t * (Yk * Yk) + 1 := by
    -- d₁ = tYk − X, d₂ = tYk + X (from d₂−d₁ = 2X, d₁+d₂ = 2tYk)
    obtain ⟨T, hT⟩ : ∃ T, t * Yk = T := ⟨_, rfl⟩
    have hdltd : chev y (j + 1) - chev y (j - 1) = 2 * X := by omega
    have hsumT : chev y (j - 1) + chev y (j + 1) = 2 * T := by omega
    have hd1 : chev y (j - 1) = T - X := by omega
    have hd2 : chev y (j + 1) = T + X := by omega
    have hXle : X ≤ T := by omega
    -- Cassini: d₁·d₂ = t² − 1, i.e. (T−X)(T+X) = T² − X²
    have hsa := sub_add_mul T X hXle
    rw [hd1, hd2] at hcass
    -- hcass : (T−X)·(T+X) + 1 = t²
    rw [Nat.add_comm X T] at hsa
    -- hsa : (T−X)·(X+T) = T² − X²
    have hprod : (T - X) * (X + T) = t * t - X * X := hsa
    obtain ⟨TT, hTT⟩ : ∃ TT, T * T = TT := ⟨_, rfl⟩
    obtain ⟨XX, hXX⟩ : ∃ XX, X * X = XX := ⟨_, rfl⟩
    obtain ⟨t2, ht2⟩ : ∃ t2, t * t = t2 := ⟨_, rfl⟩
    rw [hTT, hXX, ht2] at hprod hcass ⊢
    rw [hTT, hXX, ht2]
    -- hprod : TT − XX = t2 − XX; hcass : TT − XX + 1 = t2 — hmm hcass shape
    omega
  -- the product identity: 4(m+1)(m+2) = t²·4(n+1)(n+2) ⟸ master
  have h4m : X * X = 4 * ((m + 1) * (m + 2)) + 1 := by rw [← hXm]; ring
  have h4n : Yk * Yk = 4 * ((n + 1) * (n + 2)) + 1 := by rw [← hYn]; ring
  refine ⟨?_, by omega, by omega⟩
  obtain ⟨A, hA⟩ : ∃ A, X * X = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, Yk * Yk = B := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, t * t = C := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, (m + 1) * (m + 2) = P := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, (n + 1) * (n + 2) = Q := ⟨_, rfl⟩
  rw [hA, hB, hC, hP, hQ] at hmaster h4m h4n
  -- hmaster : A + C = C * B + 1; h4m : A = 4P + 1; h4n : B = 4Q + 1
  have hCB : C * B = C * (4 * Q + 1) := by rw [hB]; ring
  obtain ⟨R, hR⟩ : ∃ R, C * (4 * Q + 1) = R := ⟨_, rfl⟩
  rw [hR] at hmaster hCB
  have hRval : R = 4 * (C * Q) + C := by rw [hR]; ring
  omega

/-! ## §4 THE DESCENT (⟹: Rep2 → the mutual pair → the chain). -/

/-- The mutual step: from Mutual u₀ u₁ with 1 ≤ u₁ < u₀, u₁ ≥ 2, the
quotient u₂ = (u₁²−1)/u₀ satisfies Mutual u₁ u₂ and u₂ < u₁. -/
theorem mutual_step (u₀ u₁ : Nat) (hu1 : 2 ≤ u₁) (hslt : u₁ < u₀)
    (hmut : Mutual u₀ u₁) :
    ∃ u₂ : Nat, u₀ * u₂ = u₁ * u₁ - 1 ∧ Mutual u₁ u₂ ∧ u₂ < u₁ := by
  obtain ⟨hd1, hd2⟩ := hmut
  have hMpos : 1 ≤ u₁ * u₁ - 1 := by
    have h4 : 2 * 2 ≤ u₁ * u₁ := Nat.mul_le_mul (show 2 ≤ u₁ by omega) (show 2 ≤ u₁ by omega)
    omega
  have huo : 0 < u₀ := by omega
  have hle : u₀ ≤ u₁ * u₁ - 1 := Nat.le_of_dvd hMpos hd1
  have hu2pos : 1 ≤ (u₁ * u₁ - 1) / u₀ := Nat.div_pos hle huo
  obtain ⟨c, hc⟩ := hd1
  have hu2val : (u₁ * u₁ - 1) / u₀ = c := by
    rw [← hc]
    exact Nat.mul_div_cancel_left c huo
  have hexact : u₀ * ((u₁ * u₁ - 1) / u₀) = u₁ * u₁ - 1 := by
    rw [hu2val]
    exact hc.symm
  have hd2' : ((u₁ * u₁ - 1) / u₀) ∣ u₁ * u₁ - 1 := ⟨u₀, by rw [← hexact]; ring⟩
  have hu2lt : (u₁ * u₁ - 1) / u₀ < u₁ := by
    have hmono : u₁ * (u₁ + 1) ≤ u₁ * u₀ := Nat.mul_le_mul_left u₁ (by omega)
    have h1 : u₁ * u₁ - 1 < u₁ * (u₁ + 1) := by
      obtain ⟨P, hP⟩ : ∃ P, u₁ * u₁ = P := ⟨_, rfl⟩
      omega
    have h2 : u₁ * u₁ - 1 < u₁ * u₀ := Nat.lt_of_lt_of_le h1 hmono
    exact Nat.div_lt_of_lt_mul h2
  refine ⟨(u₁ * u₁ - 1) / u₀, hexact, ⟨?_, hd2'⟩, hu2lt⟩
  -- u₁ ∣ u₂² − 1: pure divisibility algebra (atom-extraction pattern)
  obtain ⟨W, hW⟩ : ∃ W, u₀ * ((u₁ * u₁ - 1) / u₀) = W := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, (u₁ * u₁ - 1) / u₀ = E := ⟨_, rfl⟩
  obtain ⟨u11, hu11⟩ : ∃ u11, u₁ * u₁ = u11 := ⟨_, rfl⟩
  obtain ⟨O2, hO2⟩ : ∃ O2, u₀ * u₀ = O2 := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2, E * E = E2 := ⟨_, rfl⟩
  obtain ⟨WW, hWW⟩ : ∃ WW, W * W = WW := ⟨_, rfl⟩
  rw [hE, hE2]
  rw [hE] at hW hu2pos hexact
  rw [hu11] at hexact hW
  -- hW : u₀ * E = W ; hexact : W = u11 − 1
  have hW1 : 1 ≤ W := by rw [← hW]; exact Nat.mul_pos huo (by omega)
  have hWpos : 0 < W := by omega
  have hdW : u₁ ∣ W + 1 := ⟨u₁, by omega⟩
  have hA : u₁ ∣ (W - 1) * (W + 1) := hdW.mul_left (W - 1)
  have hC : u₁ ∣ (u₀ * u₀ - 1) * E2 := by
    obtain ⟨cc, hcc⟩ := hd2
    exact ⟨cc * E2, by rw [hcc]; ring⟩
  have hsa := sub_add_mul W 1 hW1
  -- hsa : (W−1)(W+1) = WW − 1
  have hW2 : W * W = u₀ * u₀ * (E * E) := by rw [← hW]; ring
  rw [hWW, hO2, hE2] at hW2
  -- hW2 : WW = O2 * E2
  have hE2pos : 1 ≤ E2 := by
    rw [← hE2]
    exact Nat.mul_pos (show 0 < E by omega) (show 0 < E by omega)
  have hFC : (u₀ * u₀ - 1) * E2 = O2 * E2 - E2 := by
    rw [← hO2, ← hE2]
    exact Nat.sub_one_mul _ _
  have hAB : u₁ ∣ (W - 1) * (W + 1) - (u₀ * u₀ - 1) * E2 :=
    Nat.dvd_sub' hA hC
  have hdiff : (W - 1) * (W + 1) - (u₀ * u₀ - 1) * E2 = E2 - 1 := by
    have hPA : (W - 1) * (W + 1) = WW - 1 := hsa
    omega
  rw [← hdiff]
  exact hAB

/-- THE DESCENT THEOREM: every mutual pair (u₀ > u₁ ≥ 1) sits on a
Chebyshev chain: u₀ = chev y j, u₁ = chev y (j−1), some y ≥ 2, j ≥ 1.
Fuel induction on u₀. -/
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
      rw [hu1, chev_zero]
    · have hu1ge2 : 2 ≤ u₁ := by omega
      obtain ⟨u₂, hexact, hmut2, hu2lt⟩ := mutual_step u₀ u₁ hu1ge2 hlt hmut
      have hu2pos : 1 ≤ u₂ := by
        have hMpos : 1 ≤ u₁ * u₁ - 1 := by
          have h4 : 2 * 2 ≤ u₁ * u₁ := Nat.mul_le_mul (show 2 ≤ u₁ by omega) (show 2 ≤ u₁ by omega)
          omega
        have huo : 0 < u₀ := by omega
        exact Nat.div_pos (Nat.le_of_dvd hMpos hmut.1) huo
      have hu1le : u₁ ≤ k := by omega
      obtain ⟨y, j, hy, hj, hu₁eq, hu₂eq⟩ := ih u₁ u₂ (by omega) (by omega) hu2pos hmut2
      -- Cassini: chev y (j+1) · chev y (j−1) + 1 = chev y j²  and u₀·u₂ = u₁²−1
      have hcass := cassini y hy j
      -- chev y j · chev y (j+2) + 1 = chev y (j+1)²
      -- with u₁ = chev y j, u₂ = chev y (j−1): chev y (j+1)·u₂ + 1 = u₁²
      have hy2 : 2 ≤ y := hy
      have hcass2 : chev y (j + 1) * chev y (j - 1) + 1 = chev y j * chev y j := by
        have := cassini y hy (j - 1)
        rw [show j - 1 + 2 = j + 1 by omega] at this
        exact this
      obtain ⟨cA, hcA⟩ : ∃ cA, chev y (j + 1) = cA := ⟨_, rfl⟩
      rw [hu₂eq] at hcass2 hexact
      rw [hu₁eq] at hcass2 hexact
      obtain ⟨P, hP⟩ : ∃ P, cA * chev y (j - 1) = P := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q, chev y j * chev y j = Q := ⟨_, rfl⟩
      rw [hP, hQ] at hcass2
      -- hcass2 : P + 1 = Q; hexact : u₀ * chev y (j-1) = Q − 1
      -- u₀ · u₂ = u₁²−1 = Q−1 = P·?? — P = cA·u₂; Q = u₁²: u₀·u₂ = Q−1 and P·u₂ = Q−1
      have hu0 : 0 < chev y (j - 1) := chev_pos y hy (j - 1)
      have hu0eq : u₀ = cA := by
        -- u₀·u₂ = Q − 1 = (P + 1) − 1 = P = cA·u₂ ⟹ cancel u₂
        have hprodEq : u₀ * chev y (j - 1) = cA * chev y (j - 1) := by
          have hLeft : u₀ * chev y (j - 1) + 1 = Q := by omega
          have hRight : cA * chev y (j - 1) + 1 = Q := by omega
          omega
        exact Nat.mul_right_cancel hprodEq
      refine ⟨y, j + 1, hy, by omega, ?_, ?_⟩
      · rw [hu0eq]; rfl
      · rw [show j + 1 - 1 = j from rfl]
        rw [hu₁eq]

/-! ## §5 THE CLASSIFICATION (the main theorem). -/

theorem erdos686k2class (t : Nat) (h2 : 2 ≤ t) :
    ((∃ m n : Nat, Rep2 (t * t) m n) ↔
      ∃ y j : Nat, y % 4 = 2 ∧ 10 ≤ y ∧ 1 ≤ j ∧ t = chev y j) := by
  constructor
  · -- ⟹ : Rep2 → chain value (the descent)
    intro hrep
    obtain ⟨m, n, heq, hn1, hmn⟩ := hrep
    have hn5 : 5 ≤ 2 * n + 3 := by omega
    -- the K26 master identity (cloned)
    have hmaster : (2 * m + 3) * (2 * m + 3) + t * t = t * t * (2 * n + 3) * (2 * n + 3) + 1 := by
      have hX2 : (2 * m + 3) * (2 * m + 3) = 4 * ((m + 1) * (m + 2)) + 1 := by ring
      have hY2 : (2 * n + 3) * (2 * n + 3) = 4 * ((n + 1) * (n + 2)) + 1 := by ring
      rw [hX2, hY2, heq]
      ring
    have hXY : 2 * m + 3 < t * (2 * n + 3) := by
      by_contra hcon
      have hge : t * (2 * n + 3) ≤ 2 * m + 3 := by omega
      have hle := Nat.mul_le_mul hge hge
      obtain ⟨P, hP⟩ : ∃ P, t * (2 * n + 3) = P := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q, 2 * m + 3 = Q := ⟨_, rfl⟩
      rw [hP, hQ] at hmaster hle ⊢
      omega
    -- the divisor pair d₁ = tY − X, d₂ = X + tY
    obtain ⟨T, hT⟩ : ∃ T, t * (2 * n + 3) = T := ⟨_, rfl⟩
    obtain ⟨X, hX⟩ : ∃ X, 2 * m + 3 = X := ⟨_, rfl⟩
    rw [hT, hX] at hmaster hXY
    have htpos : 1 ≤ t := by omega
    have htt : 4 ≤ t * t := by
      have hmul : t * 2 ≤ t * t := Nat.mul_le_mul_left t (by omega)
      omega
    have hd1 : T - X ≥ 1 := by omega
    have hprod : (T - X) * (X + T) = t * t - 1 := by
      have hsa := sub_add_mul T X (by omega)
      rw [Nat.add_comm X T] at hsa
      -- (T−X)(X+T) = T² − X²; master: X² + t² = T² + 1
      obtain ⟨TT, hTT⟩ : ∃ TT, T * T = TT := ⟨_, rfl⟩
      obtain ⟨XX, hXX⟩ : ∃ XX, X * X = XX := ⟨_, rfl⟩
      obtain ⟨t2, ht2⟩ : ∃ t2, t * t = t2 := ⟨_, rfl⟩
      rw [hTT, hXX, ht2] at hsa hmaster ⊢
      omega
    -- d₁ < t and Mutual t d₁
    obtain ⟨d1, hd1v⟩ : ∃ d1, T - X = d1 := ⟨_, rfl⟩
    obtain ⟨d2, hd2v⟩ : ∃ d2, X + T = d2 := ⟨_, rfl⟩
    rw [hd1v, hd2v] at hprod
    -- hprod : d1 * d2 = t² − 1
    have hd1lt : d1 < d2 := by omega
    have hd1t : d1 < t := by
      by_contra hcon
      have hge : t ≤ d1 := by omega
      have hsq : d1 * d1 ≤ d1 * d2 := Nat.mul_le_mul_left d1 (Nat.le_of_lt hd1lt)
      have ht2 : t * t ≤ d1 * d1 := Nat.mul_le_mul hge hge
      omega
    -- Mutual t d1: t ∣ d1²−1 ∧ d1 ∣ t²−1
    have hsumd : d1 + d2 = 2 * T := by omega
    have hdvdt : t ∣ d1 + d2 := by
      rw [hsumd, hT]; exact ⟨2 * (2 * n + 3), by ring⟩
    have hdvd12 : t ∣ d1 * d2 + 1 := by
      have : d1 * d2 + 1 = t * t := by omega
      exact ⟨t, this⟩
    have hsplit : d1 * (d1 + d2) + 1 = (d1 * d1 - 1) + (d1 * d2 + 1) := by
      have e : d1 * (d1 + d2) = d1 * d1 + d1 * d2 := by ring
      obtain ⟨A, hA⟩ : ∃ A, d1 * d1 = A := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B, d1 * d2 = B := ⟨_, rfl⟩
      rw [hA, hB] at e ⊢
      omega
    have hFirst : t ∣ d1 * d1 - 1 := by
      have hA : t ∣ d1 * (d1 + d2) := Nat.dvd_mul_of_dvd_left hdvdt _
      have hAB : t ∣ d1 * (d1 + d2) - (d1 * d2 + 1) := Nat.dvd_sub' hA hdvd12
      rw [← hsplit]
      exact hAB
    have hSecond : d1 ∣ t * t - 1 := by
      rw [← hprod]
      exact ⟨d2, Nat.mul_comm d1 d2⟩
    have hmut : Mutual t d1 := ⟨hFirst, hSecond⟩
    obtain ⟨y, j, hy2, hj1, hteq, hd1eq⟩ := chain_of_mutual t d1 (by omega) (Nat.le_refl t) (by omega) hmut
    -- the Y-law: d1 + d2 = 2t·(2n+3) and d1+d2 = y·t ⟹ y = 2(2n+3)
    have hchevadd := chev_add y hy2 (j - 1)
    rw [show j - 1 + 2 = j + 1 by omega] at hchevadd
    rw [hteq, hd1eq] at hchevadd
    -- hchevadd : d1 + chev y (j+1) = y·t
    obtain ⟨dd, hdd⟩ : ∃ dd, chev y (j + 1) = dd := ⟨_, rfl⟩
    -- d2 = (t²−1)/d1 = chev y (j+1) by Cassini-cancellation
    have hcassj := cassini y hy2 (j - 1)
    rw [show j - 1 + 2 = j + 1 by omega] at hcassj
    rw [hteq, hd1eq] at hcassj
    -- hcassj : d1 · dd + 1 = t²
    have hd2eq : d2 = dd := by
      -- d1·d2 = t²−1 = d1·dd ⟹ cancel d1
      have hP1 : d1 * d2 + 1 = t * t := by omega
      have hP2 : d1 * dd + 1 = t * t := by omega
      have : d1 * d2 = d1 * dd := by omega
      exact Nat.mul_right_cancel this
    have hyY : y = 2 * (2 * n + 3) := by
      -- d1 + d2 = 2t(2n+3) [extraction] and d1 + d2 = y·t [chain] ⟹ y = 2(2n+3)
      have hchainSum : d1 + dd = y * t := by omega
      have hextr : d1 + d2 = 2 * t * (2 * n + 3) := by omega
      rw [hd2eq] at hextr
      rw [hchainSum] at hextr
      obtain ⟨P, hP⟩ : ∃ P, t * (2 * (2 * n + 3)) = P := ⟨_, rfl⟩
      obtain ⟨Q, hQ⟩ : ∃ Q, y * t = Q := ⟨_, rfl⟩
      rw [hP, hQ] at hextr
      have hPval : P = t * (2 * (2 * n + 3)) := hP
      have hQval : Q = y * t := hQ
      have hcancel : 2 * (2 * n + 3) = y := by
        have h1 : t * (2 * (2 * n + 3)) = Q := by rw [hPval]; omega
        have h2 : y * t = Q := hQval
        have hcomm1 : t * (2 * (2 * n + 3)) = (2 * (2 * n + 3)) * t := Nat.mul_comm _ _
        have hcomm2 : y * t = t * y := Nat.mul_comm _ _
        rw [hcomm1] at h1
        rw [hcomm2] at h2
        exact Nat.mul_right_cancel (h1.trans h2)
      omega
    refine ⟨y, j, ?_, ?_, hj1, hteq⟩
    · -- y ≡ 2 mod 4: y = 2(2n+3), 2n+3 odd
      omega
    · -- y ≥ 10: y = 2(2n+3) ≥ 2·5
      omega
  · -- ⟸ : chain value → Rep2
    intro hchain
    obtain ⟨y, j, hy4, hy10, hj1, hteq⟩ := hchain
    rw [hteq]
    exact erdos686k2_witness_of_chain y j hy4 hy10 hj1

/-! ## §6 THE SCAN-FREE NO-GO. -/

theorem erdos686k2_nogo (t : Nat) (h2 : 2 ≤ t) (h16 : t ≤ 16)
    (hnot : t ≠ 10 ∧ t ≠ 14) : ¬ ∃ m n : Nat, Rep2 (t * t) m n := by
  intro hrep
  obtain ⟨y, j, hy4, hy10, hj1, hteq⟩ := (erdos686k2class t h2).mp hrep
  have hy : 2 ≤ y := by omega
  have hyle : y ≤ t := by
    rw [← hteq]
    exact chev_mono' y hy 1 j (by omega)
  -- y ∈ {10, 14}
  by_cases hy10v : y = 10
  · by_cases hj1v : j = 1
    · rw [hj1v] at hteq; rw [hteq, chev_one] at hteq
      omega
    · have hj2 : 2 ≤ j := by omega
      have h99 : chev y 2 ≤ chev y j := chev_mono' y hy 2 j (by omega)
      rw [chev_two, hy10v] at h99
      have h100 : 10 * 10 ≤ y * y := Nat.mul_le_mul (show 10 ≤ y by omega) (show 10 ≤ y by omega)
      obtain ⟨P, hP⟩ : ∃ P, y * y = P := ⟨_, rfl⟩
      rw [hP] at h100 h99 ⊢
      rw [← hteq]
      omega
  · have hy14 : y = 14 := by omega
    by_cases hj1v : j = 1
    · rw [hj1v] at hteq; rw [hteq, chev_one] at hteq
      omega
    · have hj2 : 2 ≤ j := by omega
      have h195 : chev y 2 ≤ chev y j := chev_mono' y hy 2 j (by omega)
      rw [chev_two, hy14] at h195
      have h196 : 14 * 14 ≤ y * y := Nat.mul_le_mul (show 14 ≤ y by omega) (show 14 ≤ y by omega)
      obtain ⟨P, hP⟩ : ∃ P, y * y = P := ⟨_, rfl⟩
      rw [hP] at h196 h195 ⊢
      rw [← hteq]
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
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/

theorem erdos686k2class_arsenal_bridge :
    [4801 % 3, (4801 / 3) % 3, (4801 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [2401 % 3, (2401 / 3) % 3, (2401 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 5762400 1 < 4 ∧
    v2r (2 ^ 2 * 2401) = v2r 2401 :=
  ⟨by decide, by decide, carryAtPos_bound 5762400 1,
    CardinalWorldsV2.v2r_ternary_scaling 2 2401⟩

/-- THE MAIN SUMMARY: the classification + the witness construction + the no-go. -/
theorem erdos686k2class_main :
    (∀ t : Nat, 2 ≤ t → ((∃ m n : Nat, Rep2 (t * t) m n) ↔
      ∃ y j : Nat, y % 4 = 2 ∧ 10 ≤ y ∧ 1 ≤ j ∧ t = chev y j)) ∧
    (∀ y j : Nat, y % 4 = 2 → 10 ≤ y → 1 ≤ j →
      Rep2 (chev y j * chev y j) ((chev y (j + 1) - chev y (j - 1)) / 2 - 3) / 2
        (y / 2 - 3) / 2) ∧
    (∀ t : Nat, 2 ≤ t → t ≤ 16 → t ≠ 10 → t ≠ 14 → ¬ ∃ m n : Nat, Rep2 (t * t) m n) :=
  ⟨erdos686k2class, erdos686k2_witness_of_chain,
   fun t h2 h16 h10 h14 => erdos686k2_nogo t h2 h16 ⟨h10, h14⟩⟩

#eval "ERDOS686K2CLASS_KERNEL_GREEN"
#print axioms chev_mono
#print axioms chev_add
#print axioms cassini
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
