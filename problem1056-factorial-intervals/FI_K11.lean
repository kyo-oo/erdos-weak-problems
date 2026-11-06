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

/-! ## The case k = 11 — THE FRONTIER (p = 52163): eleven consecutive
intervals covering [2, 52161], every block product ≡ 1 (mod 52163). The
value-1 chain cut points: 1, 3924, 7291, 7427, 18519, 24931, 26081,
27231, 33643, 44735, 44871, 52161. -/
theorem erdos1056_k11 : Nat.Prime 52163 ∧
    prodmod 52163 2 3924 = 1 ∧ prodmod 52163 3925 7291 = 1 ∧
    prodmod 52163 7292 7427 = 1 ∧ prodmod 52163 7428 18519 = 1 ∧
    prodmod 52163 18520 24931 = 1 ∧ prodmod 52163 24932 26081 = 1 ∧
    prodmod 52163 26082 27231 = 1 ∧ prodmod 52163 27232 33643 = 1 ∧
    prodmod 52163 33644 44735 = 1 ∧ prodmod 52163 44736 44871 = 1 ∧
    prodmod 52163 44872 52161 = 1 := by decide

#eval "FI_K11_GREEN"
#print axioms erdos1056_k11
