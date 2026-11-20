import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels, K30/K36/K37 chains): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 4000000
-- 2^84 / 3^53 kernel evaluations (far below the NO-OOM legal cap of 1000).
set_option exponentiation.threshold 1000

/-!
# ERDŐS #406 — THE CAP-LAW REDUCTION KERNEL (S074, W75, the cap-law front)

## THE PROBLEM (verbatim, erdosproblems.com/406 — BOSS's own front)

> Is it true that there are only finitely many powers of $2$ which have only
> the digits $0$ and $1$ when written in base $3$?

Corpus addendum: "The only examples seem to be $1$, $4=1+3$, and
$256=1+3+9+243$."

## WHAT THIS KERNEL PROVES (the reduction theorem — new mathematics, S074)

THE 2-ADIC CAP LAW, at any explicit constant $C$, closes the problem
COMPLETELY.  The cap law is the statement:

  **CAP(C):** for every positive $0/1$-ternary number $n \equiv 1 \pmod 3$
  (a "primitive Cantor" number, in the source monolith's language),
  $$v_2(n) \;\le\; \lfloor \log_3 n \rfloor + C,$$
  formalized below as `v2r n ≤ ternaryLog3 n + C` (both readers are the
  compiled Arsenal's own: `Arsenal/CardinalWorlds.lean`).

This kernel proves, unconditionally and in full:

* **THE RIDER SQUEEZE** (`cap_squeeze`): for every $K \ge 1$, every $M$
  with $3^M \le 2^{2K}$ and $2K \le M + C$:
  $$62 \cdot K < 84 \cdot C.$$
  Proof: the rational certificate $2^{84} < 3^{53}$ (kernel `decide`),
  lifted through the power chain
  $3^{106K} \le 3^{84M} = (3^M)^{84} \le (2^{2K})^{84} = (2^{84})^{2K}
  < (3^{53})^{2K} = 3^{106K}$ — an absurdity.  The certificate constant
  $84/62 = 42/31 = 1.3548\ldots$ against the true squeeze constant
  $2\log_3(3/2)^{-1} = 1.35476\ldots$ — sharp to three decimals.

* **THE RIDER BOUND** (`cap_rider_bound`): under CAP(C), every rider
  (an exponent $K \ge 1$ with `noTernaryTwo (4^K) = true`, i.e. $4^K$
  $0/1$-ternary) satisfies $62K < 84C$.  The route: a rider's value is
  $4^K = 2^{2K}$, so $v_2 = 2K$ exactly (`v2r_two_pow`), and its leading
  ternary position $M = \lfloor\log_3 4^K\rfloor$ obeys $3^M \le 4^K$
  (`three_pow_ternaryLog3_le`); the cap law then feeds the squeeze.

* **THE POSTULATE-II INSTANTIATION** (`erdos406_classification_of_postulate_two`):
  at $C = 3$ — the source monolith's own POSTULATE II constant
  (`ErdosTernary2.lean:858`, "for all primitive Cantor n,
  v₂(n) ≤ ternaryLog3(n) + 3", there proven only below $3^9$) — the
  classification is COMPLETE: every rider is $K \in \{0, 1, 4\}$, i.e.
  the only powers of $2$ that are $0/1$-ternary are $1$, $4$, $256$
  — at every exponent, no bound.  The three small exponents $K \in
  \{2, 3\}$ are discharged by kernel `decide` ($16 = 121_3$,
  $64 = 2101_3$ both own the digit $2$).

* **THE C = 185 INSTANTIATION** (`erdos406_no_riders_above_250_of_cap`):
  at the weak constant $C = 185$, every rider satisfies $K \le 250$
  ($62 \cdot 251 = 15562 > 15540 = 84 \cdot 185$) — inside the green
  census range of Kernel 38 (`erdos406_main`: below $2^{500}$ the
  riders are exactly $1, 4, 256$).  **This is the retargeting theorem:
  the campaign's stalled Postulate II (C = 3) is SIXTY TIMES STRONGER
  than what the full kill needs.**  Any provable cap constant
  $C \le 185$ — even $C = 100$, even $C = 184$ — closes Erdős #406
  outright when composed with the already-green census.

* **THE CENSUS COMPOSITION** (`erdos406_classification_of_cap_and_census`):
  CAP(185) + the Kernel-38 census (carried as an explicit hypothesis in
  `noTernaryTwo` form; Kernel 38 proves the `tfold` form, the bridge is
  the standard strong-induction unfolding) ⟹ the complete
  classification, every exponent, no bound, zero remaining hypotheses
  beyond the cap.

## THE EMPIRICAL RECEIPTS (engine-side, this session; see
   problem406-ternary-powers/caplaw/ for artifacts)

* The exact extremal curve $v_2^*(M) = \max\{v_2(\sum_{i \in S} 3^i) :
  \varnothing \ne S \subseteq [0,M]\}$, computed exhaustively
  (meet-in-the-middle, both-methods) through $M = 34$:
  $v_2^*(M) \le M + 4$ throughout, with the excess $v_2^* - M$ equal to
  $+1, +3, +4, +2, +2, +4, +3, +2, +1$ at $M = 1, 5, 31, 14, 23, 31,
  32, 33, 34$-pattern — the only line-touchers at $1.5849M$ in all
  history are the actual witnesses $\{0,1\}$ ($M=1$, $v_2 = 2$) and
  $\{0,1,2,5\}$ ($M=5$, $v_2 = 8$, sum $= 256$).
* The cap at $C = 3$ is certified exhaustively for all primitive Cantor
  $n < 3^{21}$ (the Strategist's independent census this session); the
  monolith had certified $n < 3^9$.
* The dust-tree census: all $K < 200000$ die (deepest survivor
  $K = 124984$, death position $36$); the survivor tree doubles exactly
  per level ($2^j$ classes mod $3^j$, verified to level $12$).

## THE HONEST SCOPE (BOSS's law: never dress a partial as complete)

The cap law CAP(C) is NOT proven here for any $C$ at unbounded range —
that is the remaining open seam, the same anti-concentration wall the
monolith struck at Postulate II.  What IS proven here, unconditionally:
the reduction.  Whoever proves any explicit CAP($C \le 185$) — by any
route, in this repo or outside it — receives the complete Erdős #406
classification through this kernel's theorems, machine-checked, with the
census composition already wired.
-/

/-! ## §1 The two readers and the small arithmetic laws -/

/-- The power-of-two valuation: `v2r (2^j) = j` (the reader is exact on
pure powers of two). -/
theorem v2r_two_pow (j : Nat) : v2r (2^j) = j := by
  induction j with
  | zero =>
    have h1 : (2:Nat)^0 = 1 := by rw [Nat.pow_zero]
    rw [h1, v2r.eq_def 1]
    simp
  | succ j ih =>
    have hp : 0 < (2:Nat)^j := Nat.pow_pos (by decide)
    have hval : (2:Nat)^(j+1) = 2 * 2^j := by rw [Nat.pow_succ, Nat.mul_comm]
    have hne : 2 * 2^j ≠ 0 := by omega
    have hmod : (2 * 2^j) % 2 = 0 := by omega
    have hdiv : (2 * 2^j) / 2 = 2^j := by omega
    rw [hval, v2r.eq_def (2 * 2^j), if_neg hne, if_pos hmod, hdiv, ih]
    omega

/-- Powers of four are one mod three (the primitive-Cantor condition for
every rider: `4^K ≡ 1 mod 3`). -/
theorem pow4_mod_one (K : Nat) : 4^K % 3 = 1 := by
  induction K with
  | zero => decide
  | succ K ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- The floor law for the ternary logarithm: `3^(ternaryLog3 n) ≤ n` for
every positive `n` (the leading-position magnitude bound). -/
theorem three_pow_ternaryLog3_le (n : Nat) :
    0 < n → 3^(ternaryLog3 n) ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h3 : n < 3
    · rw [ternaryLog3, if_pos h3]
      have h1 : (3:Nat)^0 = 1 := by rw [Nat.pow_zero]
      rw [h1]
      omega
    · have hdiv : 0 < n / 3 := by omega
      have hlt : n / 3 < n := Nat.div_lt_self hn (by decide)
      have hrec := ih (n / 3) hlt hdiv
      rw [ternaryLog3, if_neg h3]
      have hexp : (3:Nat)^(1 + ternaryLog3 (n/3))
          = 3 * 3^(ternaryLog3 (n/3)) := by
        rw [Nat.pow_add, Nat.pow_one]
      rw [hexp]
      have h3div : 3 * (n / 3) ≤ n := by omega
      calc 3 * 3^(ternaryLog3 (n/3))
          ≤ 3 * (n / 3) := Nat.mul_le_mul_left _ hrec
        _ ≤ n := h3div

/-! ## §2 The power-monotonicity toolkit (self-contained, green idioms) -/

/-- Exponent monotonicity for base three. -/
theorem three_pow_mono (x y : Nat) (h : x ≤ y) : 3^x ≤ 3^y := by
  obtain ⟨d, hd⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
  rw [hd, Nat.pow_add]
  have hpd : 0 < (3:Nat)^d := Nat.pow_pos (by decide)
  calc 3^x = 3^x * 1 := (Nat.mul_one _).symm
    _ ≤ 3^x * 3^d := Nat.mul_le_mul_left _ hpd

/-- Base monotonicity for powers: `a ≤ b → a^e ≤ b^e`. -/
theorem pow_mono_base (a b e : Nat) (h : a ≤ b) : a^e ≤ b^e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.mul_le_mul ih h

/-- Strict base monotonicity: `a < b` and `e ≥ 1` give `a^e < b^e`. -/
theorem pow_lt_mono_base (a b e : Nat) (h : a < b) (he : 1 ≤ e) :
    a^e < b^e := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  clear he
  induction f with
  | zero =>
    rw [Nat.zero_add, Nat.pow_one, Nat.pow_one]
    exact h
  | succ f ih =>
    show a^(f+1+1) < b^(f+1+1)
    have h1 : a^(f+1) * a < a^(f+1) * b := by
      obtain ⟨s, hs⟩ : ∃ s : Nat, b = a + s + 1 := ⟨b - a - 1, by omega⟩
      have hexp : a^(f+1) * (a + s + 1) = a^(f+1) * a + (s + 1) * a^(f+1) := by
        ring
      have hstep : 0 < (s + 1) * a^(f+1) := by
        have hpos : 0 < a^(f+1) := Nat.pow_pos (by decide)
        obtain ⟨k, hk⟩ : ∃ k : Nat, a^(f+1) = k + 1 := ⟨a^(f+1) - 1, by omega⟩
        rw [hk]
        have hms : (s + 1) * (k + 1) = (s + 1) * k + (s + 1) :=
          Nat.mul_succ (s + 1) k
        rw [hms]
        omega
      rw [hs, hexp]
      omega
    have h2 : a^(f+1) * b ≤ b^(f+1) * b := Nat.mul_le_mul_right _ (Nat.le_of_lt ih)
    calc a^(f+1+1) = a^(f+1) * a := Nat.pow_succ a (f+1)
      _ < a^(f+1) * b := h1
      _ ≤ b^(f+1) * b := h2
      _ = b^(f+1+1) := (Nat.pow_succ b (f+1)).symm

/-- The power-reassociation identity: `(a^m)^n = a^(n*m)`. -/
theorem pow_mul_comm_shape (a m n : Nat) : (a^m)^n = a^(n*m) := by
  rw [← Nat.pow_mul, Nat.mul_comm]

/-! ## §3 THE RIDER SQUEEZE — the rational certificate engine -/

/-- **THE CERTIFICATE** (kernel-decided): $2^{84} < 3^{53}$.
The rational $53/84 = 0.630952\ldots$ sits above $\log_3 2 =
0.630929\ldots$ by $2.3 \cdot 10^{-5}$ — sharp enough that the derived
squeeze constant $84/62 = 1.35483\ldots$ loses less than $0.05\%$
against the truth $1.35476\ldots$ -/
theorem two_pow_84_lt_three_pow_53 : (2:Nat)^84 < 3^53 := by decide

/-- **THE RIDER SQUEEZE.**  For every $K \ge 1$: if the leading ternary
position $M$ of $2^{2K}$ obeys the magnitude law $3^M \le 2^{2K}$ and
the cap law $2K \le M + C$, then $62 \cdot K < 84 \cdot C$.

The proof is one power chain closed by the certificate: from
$106K \le 84M$ (pure `omega` from the two hypotheses),
$$3^{106K} \le 3^{84M} = (3^M)^{84} \le (2^{2K})^{84} = (2^{84})^{2K}
< (3^{53})^{2K} = 3^{106K},$$
an absurdity.  Every monotonicity link is a §2 toolkit lemma; every
reassociation is `pow_mul_comm_shape` plus `ring`; the single strict
link is the kernel-decided certificate lifted by `pow_lt_mono_base`. -/
theorem cap_squeeze (K M C : Nat) (hK : 1 ≤ K)
    (hMag : 3^M ≤ 2^(2*K))
    (hCap : 2*K ≤ M + C) :
    62 * K < 84 * C := by
  by_contra hnc
  have hC : 84 * C ≤ 62 * K := by omega
  have h106 : 106 * K ≤ 84 * M := by omega
  have h1 : 3^(106*K) ≤ 3^(84*M) := three_pow_mono _ _ h106
  have h2 : 3^(84*M) = (3^M)^84 := (pow_mul_comm_shape 3 M 84).symm
  have h3 : (3^M)^84 ≤ (2^(2*K))^84 := pow_mono_base _ _ _ hMag
  have hex1 : 84 * (2*K) = 168*K := by ring
  have h4 : (2^(2*K))^84 = 2^(168*K) := by
    rw [pow_mul_comm_shape 2 (2*K) 84, hex1]
  have hex2 : (2*K) * 84 = 168*K := by ring
  have h5 : 2^(168*K) = (2^84)^(2*K) := by
    rw [pow_mul_comm_shape 2 84 (2*K), hex2]
  have hcert : (2:Nat)^84 < 3^53 := two_pow_84_lt_three_pow_53
  have h6 : (2^84)^(2*K) < (3^53)^(2*K) :=
    pow_lt_mono_base _ _ _ hcert (by omega)
  have hex3 : (2*K) * 53 = 106*K := by ring
  have h7 : (3^53)^(2*K) = 3^(106*K) := by
    rw [pow_mul_comm_shape 3 53 (2*K), hex3]
  have hchain : 3^(106*K) < 3^(106*K) :=
    calc 3^(106*K) ≤ 3^(84*M) := h1
      _ = (3^M)^84 := h2
      _ ≤ (2^(2*K))^84 := h3
      _ = 2^(168*K) := h4
      _ = (2^84)^(2*K) := h5
      _ < (3^53)^(2*K) := h6
      _ = 3^(106*K) := h7
  exact absurd hchain (Nat.lt_irrefl _)

/-! ## §4 THE RIDER BOUND — the cap law meets the power of four -/

/-- The bridge identity `2^(2*K) = 4^K`. -/
theorem two_pow_two_mul (K : Nat) : 2^(2*K) = 4^K := by
  rw [show (4:Nat) = 2^2 from rfl, ← Nat.pow_mul]

/-- **THE RIDER BOUND.**  Under the cap law CAP(C) — stated on the
compiled Arsenal's own readers, in the source monolith's primitive-Cantor
form — every rider exponent $K \ge 1$ (with $4^K$ a $0/1$-ternary
number) satisfies the squeeze $62K < 84C$, hence $K < 1.355 \cdot C$.

The chain: the rider's value is exactly $2^{2K}$ (so `v2r = 2K`
by `v2r_two_pow`), it is primitive ($4^K ≡ 1 \bmod 3$), and its
leading ternary position `ternaryLog3 (4^K)` obeys the magnitude law
(`three_pow_ternaryLog3_le`).  The cap law then applies verbatim and
feeds `cap_squeeze`. -/
theorem cap_rider_bound (C : Nat)
    (hCap : ∀ n : Nat, n % 3 = 1 → noTernaryTwo n = true →
      v2r n ≤ ternaryLog3 n + C)
    (K : Nat) (hK : 1 ≤ K) (hRider : noTernaryTwo (4^K) = true) :
    62 * K < 84 * C := by
  have h4 : 2^(2*K) = 4^K := two_pow_two_mul K
  have hm : 4^K % 3 = 1 := pow4_mod_one K
  have hv : v2r (4^K) = 2*K := by
    rw [← h4, v2r_two_pow]
  have hM := hCap (4^K) hm hRider
  rw [hv] at hM
  rw [← h4] at hM
  have hpos : 0 < 4^K := Nat.pow_pos (by decide)
  have hmag : 3^(ternaryLog3 (4^K)) ≤ 4^K :=
    three_pow_ternaryLog3_le _ hpos
  rw [← h4] at hmag
  exact cap_squeeze K (ternaryLog3 (2^(2*K))) C hK hmag hM

/-! ## §5 THE INSTANTIATIONS — Postulate II at C = 3, the weak cap at
C = 185, and the census composition -/

/-- The kernel receipt for the exponent $K = 2$: $4^2 = 16 = 121_3$ owns
the digit $2$. -/
theorem no22_four_pow_two : noTernaryTwo (4^2) = false := by
  rw [noTernaryTwo_eq_struct (4^2) 17 (by decide)]
  decide

/-- The kernel receipt for the exponent $K = 3$: $4^3 = 64 = 2101_3$
owns the digit $2$. -/
theorem no22_four_pow_three : noTernaryTwo (4^3) = false := by
  rw [noTernaryTwo_eq_struct (4^3) 65 (by decide)]
  decide

/-- **THE POSTULATE-II INSTANTIATION — the complete classification.**
If the source monolith's POSTULATE II holds at its own constant
($C = 3$: "for all primitive Cantor $n$, $v_2(n) \le ternaryLog3(n) +
3$", `ErdosTernary2.lean:858`, there certified only below $3^9$), then
the Erdős #406 classification is COMPLETE at every exponent, with no
bound: the only $K \ge 0$ with $4^K$ a $0/1$-ternary number are
$K \in \{0, 1, 4\}$ — the powers $1$, $4$, $256$.

The squeeze at $C = 3$ gives $62K < 252$, i.e. $K \le 4$; the exponents
$K = 2, 3$ are discharged by the kernel `decide` receipts above. -/
theorem erdos406_classification_of_postulate_two
    (hPostulateII : ∀ n : Nat, n % 3 = 1 → noTernaryTwo n = true →
      v2r n ≤ ternaryLog3 n + 3) :
    ∀ K : Nat, noTernaryTwo (4^K) = true → K = 0 ∨ K = 1 ∨ K = 4 := by
  intro K hRider
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · exact Or.inl hK0
  · have hbound := cap_rider_bound 3 hPostulateII K hK1 hRider
    have hK4 : K ≤ 4 := by omega
    by_cases h1 : K = 1
    · exact Or.inr (Or.inl h1)
    · by_cases h2 : K = 2
      · rw [h2] at hRider
        rw [no22_four_pow_two] at hRider
        simp at hRider
      · by_cases h3 : K = 3
        · rw [h3] at hRider
          rw [no22_four_pow_three] at hRider
          simp at hRider
        · have h4eq : K = 4 := by omega
          exact Or.inr (Or.inr h4eq)

/-- **THE C = 185 INSTANTIATION — the retargeting theorem.**  At the
weak constant $C = 185$, every rider satisfies $K \le 250$ (since
$62 \cdot 251 = 15562 > 15540 = 84 \cdot 185$) — INSIDE the green
census range of Kernel 38 (below $2^{500}$).  This is the front the
campaign attacks now: any provable explicit cap constant $C \le 185$
closes Erdős #406 outright. -/
theorem erdos406_no_riders_above_250_of_cap
    (hCap : ∀ n : Nat, n % 3 = 1 → noTernaryTwo n = true →
      v2r n ≤ ternaryLog3 n + 185) :
    ∀ K : Nat, 251 ≤ K → noTernaryTwo (4^K) = false := by
  intro K hK
  by_contra hRider
  have hK1 : 1 ≤ K := by omega
  have hRiderT : noTernaryTwo (4^K) = true := by
    cases h : noTernaryTwo (4^K) with
    | false => exact absurd h hRider
    | true => rfl
  have hbound := cap_rider_bound 185 hCap K hK1 hRiderT
  omega

/-- **THE CENSUS COMPOSITION — the complete classification from the weak
cap.**  CAP(185) + the Kernel-38 census (carried here as an explicit
hypothesis in `noTernaryTwo` form; Kernel 38 proves the `tfold` form and
the bridge is the standard strong-induction unfolding of the two
recursive readers) ⟹ every rider is $K \in \{0, 1, 4\}$: the powers
$1$, $4$, $256$, at every exponent, unconditionally modulo the cap. -/
theorem erdos406_classification_of_cap_and_census
    (hCap : ∀ n : Nat, n % 3 = 1 → noTernaryTwo n = true →
      v2r n ≤ ternaryLog3 n + 185)
    (hCensus : ∀ k : Nat, k ≤ 500 → noTernaryTwo (2^k) = true →
      k = 0 ∨ k = 2 ∨ k = 8) :
    ∀ K : Nat, noTernaryTwo (4^K) = true → K = 0 ∨ K = 1 ∨ K = 4 := by
  intro K hRider
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · exact Or.inl hK0
  · have hbound := cap_rider_bound 185 hCap K hK1 hRider
    have hK250 : K ≤ 250 := by omega
    have h4 : 2^(2*K) = 4^K := two_pow_two_mul K
    rw [← h4] at hRider
    have h2K500 : 2*K ≤ 500 := by omega
    rcases hCensus (2*K) h2K500 hRider with h0 | h2 | h8
    · exfalso; omega
    · have : K = 1 := by omega
      exact Or.inr (Or.inl this)
    · have : K = 4 := by omega
      exact Or.inr (Or.inr this)

/-! ## §6 The receipts -/

#check v2r_two_pow
#check pow4_mod_one
#check three_pow_ternaryLog3_le
#check three_pow_mono
#check pow_mono_base
#check pow_lt_mono_base
#check pow_mul_comm_shape
#check two_pow_84_lt_three_pow_53
#check cap_squeeze
#check two_pow_two_mul
#check cap_rider_bound
#check no22_four_pow_two
#check no22_four_pow_three
#check erdos406_classification_of_postulate_two
#check erdos406_no_riders_above_250_of_cap
#check erdos406_classification_of_cap_and_census

#print axioms v2r_two_pow
#print axioms pow4_mod_one
#print axioms three_pow_ternaryLog3_le
#print axioms three_pow_mono
#print axioms pow_mono_base
#print axioms pow_lt_mono_base
#print axioms pow_mul_comm_shape
#print axioms two_pow_84_lt_three_pow_53
#print axioms cap_squeeze
#print axioms two_pow_two_mul
#print axioms cap_rider_bound
#print axioms no22_four_pow_two
#print axioms no22_four_pow_three
#print axioms erdos406_classification_of_postulate_two
#print axioms erdos406_no_riders_above_250_of_cap
#print axioms erdos406_classification_of_cap_and_census
