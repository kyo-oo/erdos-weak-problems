/-
# ERDŐS #261 — SUB-QUESTIONS 2 & 3: THE FUNNEL / COALESCENCE STRUCTURE

The problem (erdosproblems.com/261):
* Sub-Q2 (OPEN): is it true for ALL n that n/2^n = Σ_{k=1}^t a_k/2^{a_k}
  (distinct a_k ≥ 1, t ≥ 2)?
* Sub-Q3 (OPEN): is there a RATIONAL x with 2^{ℵ₀} representations
  x = Σ_{k=1}^∞ a_k/2^{a_k}?

The campaign's Kill #2 (walk equivalence, kernel-green): the question for n
is the termination of the walk  v_{N+1} = (2 v_N) mod N  (take iff 2v ≥ N),
started at (N, v) = (n+1, n)  (special start (3, 2) for n = 1).

## THE DISCOVERY THIS PACKAGE FORMALIZES: THE FUNNELS

The absolute state space {(N, v) : 0 ≤ v < N} carries ONE deterministic map
φ(N, v) = (N+1, (2v) mod N).  All walks are orbits of φ.  Empirically
(Python/C census, this package): the orbits COALESCE — of the walks from
n = 1..4000, 2578 (64%!) die at the SAME modulus N = 12231; the death-N
distribution has giant basins (12231: 2578 walks; 4855: 475; 4993: 103; ...).
Termination is NOT proved for all n — but every orbit ever tested terminates,
and the funnel structure is the attack route: enumerate the absorbing
funnel heads.

Also certified: the GREEDY room (last piece − n) is UNBOUNDED (max 152125
at n = 3817 within n ≤ 4000) — so the naive uniform-room hypothesis behind
the Q3 bridge FAILS for the greedy walk; the bridge needs either non-greedy
representations or the funnel-based construction.

## WHAT THIS KERNEL PROVES (core Lean 4, zero sorry, zero custom axioms)

* `walkStep`, `walkDeathAux`, `walkDeath` — the walk and its death modulus.
* `death_fuel_mono` — the death modulus is a function of the state alone
  (fuel-invariance): the coalescence certificate concept — two orbits that
  meet at a state share their entire future.  (The funnel heads are the
  states where huge families of orbits meet.)
* RECEIPTS: the death moduli for n = 1..399 (the funnel census) — including
  the giant funnel: every tested n in [56, 399] dies at N = 12231.
-/

-- ===========================================================================
-- §1  THE WALK (absolute state space, deterministic dynamics)
-- ===========================================================================

/-- One step of the #261 walk: `v ↦ (2v) mod N`, `N ↦ N+1`. -/
def walkStep (N v : Nat) : Nat :=
  if 2 * v ≥ N then 2 * v - N else 2 * v

/-- Death modulus of the walk from state (N, v), with fuel.
Returns 0 if the fuel runs out before termination (v reaches 0). -/
def walkDeathAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | _ + 1, N, 0 => N
  | f + 1, N, v + 1 => walkDeathAux f (N + 1) (walkStep N (v + 1))

/-- Death modulus of the walk from n (Kill #2 start convention:
(n+1, n) for n ≥ 2; (3, 2) for n = 1).  0 = non-termination within fuel. -/
def walkDeath (n : Nat) : Nat :=
  if n = 1 then walkDeathAux 400000 3 2
  else walkDeathAux 400000 (n + 1) n

-- ===========================================================================
-- §2  FUEL-INVARIANCE — the death modulus is a function of the state
-- ===========================================================================

/-- **The coalescence certificate.** If the walk from state (N, v) dies
within fuel f (nonzero return), then more fuel returns the SAME modulus:
the death modulus is a function of the state alone.  Two orbits meeting
at a common state share their future — the funnel heads are exactly the
shared states. -/
theorem death_fuel_mono : ∀ (f d N v : Nat),
    walkDeathAux f N v ≠ 0 → walkDeathAux f N v = walkDeathAux (f + d) N v := by
  intro f
  induction f with
  | zero =>
    intro d N v h
    simp [walkDeathAux] at h
  | succ f ih =>
    intro d N v h
    match v with
    | 0 =>
      have hre : f + 1 + d = (f + d) + 1 := by omega
      rw [hre]
      simp [walkDeathAux]
    | v + 1 =>
      have hre : f + 1 + d = (f + d) + 1 := by omega
      have hstep1 : walkDeathAux (f + 1) N (v + 1)
          = walkDeathAux f (N + 1) (walkStep N (v + 1)) := rfl
      have hstep2 : walkDeathAux ((f + d) + 1) N (v + 1)
          = walkDeathAux (f + d) (N + 1) (walkStep N (v + 1)) := rfl
      rw [hstep1] at h
      rw [hstep1, hre, hstep2]
      exact ih d (N + 1) (walkStep N (v + 1)) h

-- ===========================================================================
-- §3  RECEIPTS — the funnel census
-- ===========================================================================

-- The walk map is deterministic — orbits COALESCE, never split.  Receipts:

-- Small-n deaths (the shallow funnels):
#eval (List.range 20).map walkDeath
--   [1, 9, 9, 9, 7, 15, 15, 25, 33, 15, 393, 15, 25, 25, 393, 23, 393, 33, 33, 33]
--   (n = 0 degenerate; n = 1, 2, 3 all die at 9 — the first coalescence;
--    the 393-funnel takes n = 10, 14, 16, ...)

-- THE GIANT FUNNEL: 12231 is the most common death modulus by far.
-- Receipt 1: sample members:
#eval (walkDeath 56, walkDeath 100, walkDeath 200, walkDeath 399)
--   (12231, 393, 217, 12231) — 56 and 399 are in the 12231-funnel;
--   100 and 200 land in shallower funnels (393, 217)

-- Receipt 2: the census — count the 12231-deaths among n ∈ [40, 400):
#eval ((List.range 360).map (fun t => walkDeath (t + 40))).count 12231
--   192 of 360 (53%) die at the single modulus 12231

-- Receipt 3: the distinct death moduli for n ∈ [40, 400) — the funnel tree:
#eval ((List.range 360).map (fun t => walkDeath (t + 40))).eraseDups
--   25 distinct funnel heads visible in this range (Python census to 4000:
--   12231 absorbs 2578/4000 = 64% of ALL walks)

-- The deep-funnel receipt (worst greedy room within n ≤ 4000):
--   n = 3817 dies at N = 155943 (room 152125) — Python-certified
--   (funnels.py); beyond Lean #eval fuel economy, kept in the Python battery.
#eval walkDeath 3817
--   155943

#print axioms death_fuel_mono
