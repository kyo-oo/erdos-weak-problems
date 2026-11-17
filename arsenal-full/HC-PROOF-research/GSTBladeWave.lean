import Mathlib
import GSTTheActConstruction

open GSTCanonicalSevenAxisBridge (digit3)

namespace GSTBladeWave

/-!
# THE BLADE AND THE WAVE — the dust root's exact laws and the wave's periodicity

Lane B (descent) and Lane C (omega) of the four-lane derivation volley,
landed in Lean.  One new file, zero monolith bytes.  Machine receipts
before landing (fresh run this session, exact big-int arithmetic):

* `L2 1500/1500  L3 1500/1500  L4 1500/1500`  (m ∈ [0, 1500))
* `PERIODICITY 3280/3280`  (a ∈ [0,4), n ∈ [0,5), core ∈ [0,41),
  t ∈ {0,1,2,7} — ALL cores, n ≥ 0, zero failures)

* **§1 THE DIGIT CONGRUENCE BACKBONE.**  `digit3_mod_pow`: the `j`-th
  ternary digit of any natural is fixed by its residue mod `3^(j+1)`;
  `digit3_congr`: congruent naturals share digits.

* **§2 THE DUST ROOT'S EXACT LAWS.**  Every dust-branch exponent is
  `K = 1 + 3*m` (row one reads `K % 3 = 1`).  The power
  `4^(1+3*m) = 4·64^m = 4·(1+63)^m` reads, at rows two and three, the
  PURE TRITS of `m` — and at row four the first binomial correction
  lands:

  `digit3 (4^(1+3*m)) 2 = m % 3`
  `digit3 (4^(1+3*m)) 3 = (m / 3) % 3`
  `digit3 (4^(1+3*m)) 4 = ((m / 9) % 3 + m.choose 2) % 3`

  **The blade's first correction is EXACTLY the binomial coefficient
  `C(m,2)`** — the accumulating-blade structure of the four-lane
  convergence, with its first three orders now exact in Lean.  The
  single engine is `dust_root_mod243`: the third-order truncation
  `4^(1+3*m) ≡ 4 + 252·m + 324·C(m,2) (mod 243)`, proved by induction
  on `m` (the step's difference is exactly `243·(64·m + 84·C(m,2))`).

* **§3 THE WAVE'S PERIODICITY.**  `wave_digit_periodic`: the wave digit
  `digit_(a+n)` of `4^(3^a·core)` depends only on `core mod 3^n` —
  for ALL cores and ALL `n`.  The proof is the cube-map tower:
  `cube_dvd_three` (cubing a one-plus gains exactly one three-adic
  order), `pow3_tower_dvd` (iterating gains `n` orders),
  `four_pow_three_pow_dvd` (`3^(a+n+1) ∣ 4^(3^(a+n)) − 1`), and
  `one_add_pow_dvd` (the shift factor `(4^(3^a))^(3^n·t)` is congruent
  to one modulo `3^(a+n+1)`).  This is the periodicity backbone the
  deep-wave cover (Lane C's named gap) reduces to cores mod `3^n`.
-/

set_option maxHeartbeats 400000

/-! ## §1 The digit congruence backbone -/

/-- The `j`-th ternary digit is fixed by the residue mod `3^(j+1)`. -/
theorem digit3_mod_pow (R j : Nat) :
    digit3 R j = (R % 3^(j+1)) / 3^j % 3 := by
  unfold digit3
  have hp : (0:Nat) < 3^j := by positivity
  have hq' : R = R % 3^(j+1) + 3 * (R / 3^(j+1)) * 3^j := by
    have h := Nat.div_add_mod R (3^(j+1))
    rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.add_comm] at h
    exact h.symm
  calc R / 3^j % 3
      = (R % 3^(j+1) + 3 * (R / 3^(j+1)) * 3^j) / 3^j % 3 := by
          rw [← hq']
    _ = (R % 3^(j+1) / 3^j + 3 * (R / 3^(j+1))) % 3 := by
          rw [Nat.add_mul_div_right _ _ hp]
    _ = (R % 3^(j+1)) / 3^j % 3 := Nat.add_mul_mod_self_left _ _ _

/-- Congruent naturals share ternary digits. -/
theorem digit3_congr {R₁ R₂ j : Nat}
    (h : R₁ % 3^(j+1) = R₂ % 3^(j+1)) :
    digit3 R₁ j = digit3 R₂ j := by
  rw [digit3_mod_pow R₁ j, digit3_mod_pow R₂ j, h]

/-! ## §2 The dust root's exact laws -/

/-- **The third-order truncation of the dust root's world.**
`4^(1+3*m) = 4·(1+63)^m`, and the binomial expansion truncates at the
second order modulo 243: the `C(m,2)·63²` term enters digit four and
no earlier.  One induction, three exact laws. -/
theorem dust_root_mod243 (m : Nat) :
    4^(1+3*m) % 243 = (4 + 252*m + 324*m.choose 2) % 243 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hpow : 4^(1+3*(m+1)) = 4^(1+3*m) * 64 := by
      have he : 1+3*(m+1) = (1+3*m)+3 := by ring
      rw [he, Nat.pow_add, (by decide : (4:Nat)^3 = 64)]
    have hpas : (m+1).choose 2 = m + m.choose 2 :=
      (Nat.choose_succ_succ m 1).trans (by rw [Nat.choose_one_right])
    have hsplit : (4 + 252*m + 324*m.choose 2) * 64
        = (4 + 252*(m+1) + 324*(m + m.choose 2))
          + 243*(64*m + 84*(m.choose 2)) := by
      ring
    calc 4^(1+3*(m+1)) % 243
        = (4^(1+3*m) * 64) % 243 := by rw [hpow]
      _ = ((4 + 252*m + 324*m.choose 2) * 64) % 243 :=
          Nat.ModEq.mul_right 64 ih
      _ = (4 + 252*(m+1) + 324*(m+1).choose 2) % 243 := by
          rw [hpas, hsplit, Nat.add_mul_mod_self_left]

/-- **Row two of the dust root reads `m`'s zeroth trit, bare.** -/
theorem digit_two_of_dust_root (m : Nat) :
    digit3 (4^(1+3*m)) 2 = m % 3 := by
  rw [digit3_mod_pow]
  norm_num
  have h := dust_root_mod243 m
  set A := 4^(1+3*m) with hA
  clear hA
  have h27 : A % 27 = (4 + 252*m + 324*m.choose 2) % 27 := by omega
  rw [h27]
  have hs : (4 + 252*m + 324*m.choose 2) % 27 = (4 + 9*m) % 27 := by omega
  rw [hs]
  omega

/-- **Row three of the dust root reads `m`'s first trit, bare.** -/
theorem digit_three_of_dust_root (m : Nat) :
    digit3 (4^(1+3*m)) 3 = (m / 3) % 3 := by
  rw [digit3_mod_pow]
  norm_num
  have h := dust_root_mod243 m
  set A := 4^(1+3*m) with hA
  clear hA
  have h81 : A % 81 = (4 + 252*m + 324*m.choose 2) % 81 := by omega
  rw [h81]
  have hs : (4 + 252*m + 324*m.choose 2) % 81 = (4 + 9*m) % 81 := by omega
  rw [hs]
  omega

/-- **Row four of the dust root: the blade's first correction is exactly
the binomial coefficient.**  `digit₄(4^(1+3m)) = trit₂(m) + C(m,2)`. -/
theorem digit_four_of_dust_root (m : Nat) :
    digit3 (4^(1+3*m)) 4 = ((m / 9) % 3 + m.choose 2) % 3 := by
  rw [digit3_mod_pow]
  norm_num
  rw [dust_root_mod243]
  have hs : (4 + 252*m + 324*m.choose 2) % 243
      = (4 + 9*m + 81*m.choose 2) % 243 := by omega
  rw [hs]
  omega

/-! ## §3 The wave's periodicity -/

/-- **The cube map.**  Cubing a one-plus gains exactly one three-adic
order of divisibility: if `3^(k+1) ∣ x` then `3^(k+2) ∣ (1+x)³ − 1`. -/
theorem cube_dvd_three (x k : Nat) (hx : 3^(k+1) ∣ x) :
    3^(k+2) ∣ (1+x)^3 - 1 := by
  have h3d : 3 ∣ 3^(k+1) := ⟨3^k, by rw [Nat.pow_succ]; ring⟩
  have h3 : 3 ∣ x := Nat.dvd_trans h3d hx
  obtain ⟨s, hs⟩ := h3
  have hS : 3 ∣ x*x + 3*(x+1) := ⟨3*s*s + (x+1), by rw [hs]; ring⟩
  obtain ⟨w, hw⟩ := hS
  obtain ⟨u, hu⟩ := hx
  have hexp : (1+x)^3 = 1 + x * (x*x + 3*(x+1)) := by ring
  have hsub : (1+x)^3 - 1 = x * (x*x + 3*(x+1)) := by omega
  have h32 : 3^(k+2) = 3^(k+1) * 3 := by rw [Nat.pow_succ]
  rw [hsub, hw, hu, h32]
  exact ⟨u * w, by ring⟩

/-- **The tower map.**  `(1+x)^(3^n)` gains `n` three-adic orders over
`x`: if `3^(a+1) ∣ x` then `3^(a+n+1) ∣ (1+x)^(3^n) − 1`. -/
theorem pow3_tower_dvd (x a n : Nat) (hx : 3^(a+1) ∣ x) :
    3^(a+n+1) ∣ (1+x)^(3^n) - 1 := by
  induction n with
  | zero =>
    rw [Nat.pow_zero, Nat.pow_one, Nat.add_zero, Nat.add_sub_cancel_left]
    exact hx
  | succ n ih =>
    have hp : a + (n+1) + 1 = (a+n) + 2 := by omega
    rw [hp]
    have hrew : (1+x)^(3^(n+1)) = ((1+x)^(3^n))^3 := by
      rw [Nat.pow_succ 3 n, Nat.pow_mul]
    have hpos : (0:Nat) < (1+x)^(3^n) := by positivity
    have hA : 1 ≤ (1+x)^(3^n) := hpos
    have h := cube_dvd_three ((1+x)^(3^n) - 1) (a+n) ih
    rw [Nat.add_sub_cancel' hA] at h
    rw [hrew]
    exact h

/-- **The one-plus power.**  Any power of a one-plus-divisible stays
one-plus-divisible at the same order. -/
theorem one_add_pow_dvd (y t k : Nat) (hy : 3^k ∣ y) :
    3^k ∣ (1+y)^t - 1 := by
  induction t with
  | zero =>
    rw [Nat.pow_zero, Nat.sub_self]
    exact Nat.dvd_zero _
  | succ t ih =>
    have hpos : (0:Nat) < (1+y)^t := by positivity
    have hA : 1 ≤ (1+y)^t := hpos
    have key : ∀ w yy : Nat, (w+1)*(1+yy) - 1 = w + yy + w*yy := by
      intro w yy
      have e1 : (w+1)*(1+yy) = w*yy + w + yy + 1 := by ring
      rw [e1, Nat.add_sub_cancel_right]
      ring
    have hexp : (1+y)^(t+1) - 1
        = ((1+y)^t - 1) + y + ((1+y)^t - 1)*y := by
      have h1 : (1+y)^(t+1) = (1+y)^t * (1+y) := Nat.pow_succ (1+y) t
      have h2 : (1+y)^t = ((1+y)^t - 1) + 1 :=
        (Nat.sub_add_cancel hA).symm
      rw [h1]
      conv_lhs => rw [h2]
      exact key _ _
    rw [hexp]
    obtain ⟨w, hw⟩ := ih
    obtain ⟨v, hv⟩ := hy
    exact ⟨w + v + 3^k*w*v, by rw [hw, hv]; ring⟩

/-- **The LTE cut for the three-power towers**, self-contained:
`3^(a+n+1) ∣ 4^(3^(a+n)) − 1` — the cube map applied to `4 = 1 + 3`. -/
theorem four_pow_three_pow_dvd (a n : Nat) :
    3^(a+n+1) ∣ 4^(3^(a+n)) - 1 := by
  have h4 : (1+3:Nat) = 4 := by decide
  have hx : 3^(0+1) ∣ (3:Nat) := ⟨1, by decide⟩
  have h := pow3_tower_dvd (3:Nat) 0 (a+n) hx
  rw [Nat.zero_add, h4] at h
  exact h

/-- **The wave congruence.**  Shifting the core by a multiple of `3^n`
does not move `4^(3^a·core)` modulo `3^(a+n+1)`. -/
theorem wave_mod (a n core t : Nat) :
    4^(3^a * (core + 3^n * t)) % 3^(a+n+1)
      = 4^(3^a * core) % 3^(a+n+1) := by
  have hsplit : 3^a * (core + 3^n * t) = 3^a * core + 3^(a+n) * t := by
    rw [Nat.pow_add]
    ring
  rw [hsplit, Nat.pow_add 4 (3^a * core) (3^(a+n) * t)]
  have hmul : 4^(3^(a+n) * t) = (4^(3^(a+n)))^t :=
    Nat.pow_mul 4 (3^(a+n)) t
  rw [hmul]
  have hpos4 : (0:Nat) < 4^(3^(a+n)) := by positivity
  have hle : 1 ≤ 4^(3^(a+n)) := hpos4
  have hy : 4^(3^(a+n)) = 1 + (4^(3^(a+n)) - 1) :=
    (Nat.add_sub_cancel' hle).symm
  rw [hy]
  obtain ⟨c, hc⟩ := one_add_pow_dvd (4^(3^(a+n)) - 1) t (a+n+1)
    (four_pow_three_pow_dvd a n)
  have hWpos : (0:Nat) < (1 + (4^(3^(a+n)) - 1))^t := by positivity
  have hW1 : (1:Nat) ≤ (1 + (4^(3^(a+n)) - 1))^t := hWpos
  have hpt : (1 + (4^(3^(a+n)) - 1))^t = 3^(a+n+1) * c + 1 := by
    rw [← hc, Nat.sub_add_cancel hW1]
  rw [hpt]
  have hexp : 4^(3^a * core) * (3^(a+n+1) * c + 1)
      = 4^(3^a * core) + 3^(a+n+1) * (c * 4^(3^a * core)) := by ring
  rw [hexp, Nat.add_mul_mod_self_left]

/-- **THE WAVE'S PERIODICITY.**  The wave digit `digit_(a+n)` of
`4^(3^a·core)` depends only on `core mod 3^n`: for every shift
`3^n·t`, the digit is unchanged.  All cores, all `a`, all `n`. -/
theorem wave_digit_periodic (a n core t : Nat) :
    digit3 (4^(3^a * (core + 3^n * t))) (a + n)
      = digit3 (4^(3^a * core)) (a + n) := by
  rw [digit3_mod_pow (4^(3^a * (core + 3^n * t))) (a + n),
    digit3_mod_pow (4^(3^a * core)) (a + n),
    wave_mod a n core t]

/-- **FULL PREFIX WAVE PERIODICITY.**
The residue theorem freezes every ternary digit at or below the wave height
a+n, not only the terminal digit. -/
theorem wave_prefix_digit_periodic
    (a n core t j : Nat) (hj : j ≤ a+n) :
    digit3 (4^(3^a * (core + 3^n * t))) j =
      digit3 (4^(3^a * core)) j := by
  let X := 4^(3^a * (core + 3^n * t))
  let Y := 4^(3^a * core)
  have hhigh : X % 3^(a+n+1) = Y % 3^(a+n+1) := by
    simpa [X,Y] using wave_mod a n core t
  have hdiv : 3^(j+1) ∣ 3^(a+n+1) :=
    pow_dvd_pow 3 (by omega)
  have hlow : X % 3^(j+1) = Y % 3^(j+1) := by
    calc
      X % 3^(j+1) =
          (X % 3^(a+n+1)) % 3^(j+1) :=
        (Nat.mod_mod_of_dvd X hdiv).symm
      _ = (Y % 3^(a+n+1)) % 3^(j+1) := by rw [hhigh]
      _ = Y % 3^(j+1) :=
        Nat.mod_mod_of_dvd Y hdiv
  exact digit3_congr hlow

/-- Complete visible wave prefix through height a+n. -/
def wavePrefix (a n core : Nat) :
    Fin (a+n+1) → Nat :=
  fun j => digit3 (4^(3^a*core)) j.1

/-- The entire visible wave-prefix vector depends only on the core modulo
3^n. -/
theorem wavePrefix_periodic
    (a n core t : Nat) :
    wavePrefix a n (core + 3^n*t) =
      wavePrefix a n core := by
  funext j
  exact wave_prefix_digit_periodic
    a n core t j.1 (by omega)

/-- Wave periodicity crown: residue, every visible digit, and the whole prefix
vector are one periodic object. -/
theorem wave_periodicity_crown :
    (∀ a n core t,
      4^(3^a*(core+3^n*t)) % 3^(a+n+1) =
        4^(3^a*core) % 3^(a+n+1))
    ∧
    (∀ a n core t j, j ≤ a+n →
      digit3 (4^(3^a*(core+3^n*t))) j =
        digit3 (4^(3^a*core)) j)
    ∧
    (∀ a n core t,
      wavePrefix a n (core+3^n*t) =
        wavePrefix a n core) := by
  exact ⟨wave_mod, wave_prefix_digit_periodic,
    wavePrefix_periodic⟩

#print axioms digit_two_of_dust_root
#print axioms digit_three_of_dust_root
#print axioms digit_four_of_dust_root
#print axioms wave_digit_periodic
#print axioms wave_prefix_digit_periodic
#print axioms wavePrefix_periodic
#print axioms wave_periodicity_crown

end GSTBladeWave
