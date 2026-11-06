import Arsenal.ErdosTernary2.Basic
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

/-! ## The case k = 10 — NEW (p = 27901) -/
theorem erdos1056_k10 : Nat.Prime 27901 ∧
    prodmod 27901 2452 2867 = 1 ∧ prodmod 27901 2868 4768 = 1 ∧
    prodmod 27901 4769 10383 = 1 ∧ prodmod 27901 10384 18707 = 1 ∧
    prodmod 27901 18708 19589 = 1 ∧ prodmod 27901 19590 19965 = 1 ∧
    prodmod 27901 19966 22981 = 1 ∧ prodmod 27901 22982 24673 = 1 ∧
    prodmod 27901 24674 26322 = 1 ∧ prodmod 27901 26323 27263 = 1 := by
  decide

#eval "FI_K10_GREEN"
#print axioms erdos1056_k10
