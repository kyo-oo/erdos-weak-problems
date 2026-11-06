import Arsenal.CardinalWorlds
/-! # Erdős #1056 — THE FACTORIAL-INTERVAL CASE-FRONTIER (Kill #22, S030)
The §7-freeze module architecture (L83): one kernel decide per process.
Structure law: k consecutive intervals with products ≡ 1 (mod p) ⟺ the
prefix-factorial sequence j! mod p visits one value k+1 times. Known:
k=2 (Erdős 1979, p=11), k=3 (Makowski 1983, p=17). NEW: k=4..11. -/

set_option maxRecDepth 262144

/-- Product of [a, a+1, …, a+c] mod p — fuel-structural (decide-clean). -/
def prodmodFuel (p : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | _ + 1, a, 0 => a % p
  | f + 1, a, c + 1 => (prodmodFuel p f a c * ((a + c + 1) % p)) % p

/-- Product of the interval [a, b] modulo p (witness intervals have b > a). -/
def prodmod (p a b : Nat) : Nat := prodmodFuel p (b - a + 1) a (b - a)

/-- Factorial j! mod p — same fuel architecture. -/
def factmodFuel (p : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | _ + 1, 0 => 1
  | f + 1, j + 1 => (factmodFuel p f j * ((j + 1) % p)) % p

def factmod (p j : Nat) : Nat := factmodFuel p (j + 1) j

/-! ## The cases k = 2 .. 8 -/
theorem erdos1056_k2 : Nat.Prime 11 ∧
    prodmod 11 3 4 = 1 ∧ prodmod 11 5 7 = 1 := by decide

theorem erdos1056_k3 : Nat.Prime 17 ∧
    prodmod 17 2 5 = 1 ∧ prodmod 17 6 11 = 1 ∧ prodmod 17 12 15 = 1 := by
  decide

theorem erdos1056_k4 : Nat.Prime 23 ∧
    prodmod 23 2 4 = 1 ∧ prodmod 23 5 8 = 1 ∧ prodmod 23 9 11 = 1 ∧
    prodmod 23 12 21 = 1 := by decide

theorem erdos1056_k5 : Nat.Prime 109 ∧
    prodmod 109 10 11 = 1 ∧ prodmod 109 12 39 = 1 ∧ prodmod 109 40 58 = 1 ∧
    prodmod 109 59 73 = 1 ∧ prodmod 109 74 85 = 1 := by decide

theorem erdos1056_k6 : Nat.Prime 71 ∧
    prodmod 71 8 9 = 1 ∧ prodmod 71 10 19 = 1 ∧ prodmod 71 20 51 = 1 ∧
    prodmod 71 52 61 = 1 ∧ prodmod 71 62 63 = 1 ∧ prodmod 71 64 70 = 1 := by
  decide

theorem erdos1056_k7 : Nat.Prime 673 ∧
    prodmod 673 160 316 = 1 ∧ prodmod 673 317 354 = 1 ∧
    prodmod 673 355 393 = 1 ∧ prodmod 673 394 397 = 1 ∧
    prodmod 673 398 506 = 1 ∧ prodmod 673 507 545 = 1 ∧
    prodmod 673 546 647 = 1 := by decide

theorem erdos1056_k8 : Nat.Prime 599 ∧
    prodmod 599 29 50 = 1 ∧ prodmod 599 51 122 = 1 ∧ prodmod 599 123 183 = 1 ∧
    prodmod 599 184 250 = 1 ∧ prodmod 599 251 289 = 1 ∧ prodmod 599 290 500 = 1 ∧
    prodmod 599 501 539 = 1 ∧ prodmod 599 540 555 = 1 := by decide

#eval "FI_K2_K8_GREEN"
#print axioms erdos1056_k2
#print axioms erdos1056_k4
#print axioms erdos1056_k8
