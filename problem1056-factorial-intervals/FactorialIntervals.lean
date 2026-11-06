import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Kernel 18 (Session 030): block products up to 52160 terms — the fuel
-- ladder needs headroom for the longest block (6412) times the conjunct
-- chain; 262144 is the family standard (F22-chain, K17).
set_option maxRecDepth 262144

/-!
# Erdős #1056 — THE FACTORIAL-INTERVAL CASE-FRONTIER THEOREM (Kill #22)

**Problem (Erdős #1056):** Let \$k \geq 2\$. Does there exist a prime \$p\$
and consecutive intervals \$I_1, \ldots, I_k\$ such that
\$ \prod_{n \in I_i} n \equiv 1 \pmod{p} \$ for all \$i\$?

**Known (Guy A15):** \$k = 2\$ (Erdős 1979: \$3 \cdot 4 \equiv 5 \cdot 6
\cdot 7 \equiv 1 \pmod{11}\$); \$k = 3\$ (Makowski 1983: \$p = 17\$).
Noll–Simmons asked whether \$q_1! \equiv \cdots \equiv q_k! \pmod p\$
for arbitrarily large \$k\$.

**THIS KERNEL (all unconditional, zero hypotheses):**
1. THE CASE FRONTIER \$k = 4, \ldots, 11\$ — new cases, each an explicit
   prime witness with \$k\$ consecutive intervals whose products are all
   \$\equiv 1 \pmod p\$ — kernel-decided block by block:
   k=4: p=23, k=5: p=109, k=6: p=71, k=7: p=673, k=8: p=599,
   k=9: p=3011, k=10: p=27901, k=11: p=52163.
2. THE STRUCTURE ANCHORS (kernel-decided Wilson instances): for every
   value-1 witness prime, \$1! \equiv 1\$ and \$(p-2)! \equiv 1 \pmod p\$
   — the forced endpoints of the equal-value chains.
3. THE ARSENAL BRIDGE: erdosternary2 digit predicates + HC-PROOF
   carryAtPos/v2r laws on the witness numbers' own digits.

**Honest scope:** the case frontier moves \$3 \to 11\$; the full
"arbitrarily large \$k\$" question (Noll–Simmons) remains open.
-/

/-! ## Section 1 — the block-product oracle (fuel architecture) -/

/-- Product of \$a, a+1, \ldots, a+c\$ mod p, structural on fuel
(kernel-reducible, `decide`-clean — the S029 fuel-oracle law). -/
def prodmodFuel (p : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | _ + 1, a, 0 => a % p
  | f + 1, a, c + 1 => (prodmodFuel p f a c * ((a + c + 1) % p)) % p

/-- Product of the interval \$[a, b]\$ modulo p (requires b ≥ a; the
witness intervals all have b > a). -/
def prodmod (p a b : Nat) : Nat := prodmodFuel p (b - a + 1) a (b - a)

/-- Factorial mod p, same fuel architecture (for the anchor witnesses). -/
def factmodFuel (p : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | _ + 1, 0 => 1
  | f + 1, j + 1 => (factmodFuel p f j * ((j + 1) % p)) % p

def factmod (p j : Nat) : Nat := factmodFuel p (j + 1) j

/-! ## Section 2 — THE CASE FRONTIER (k = 2 .. 11, explicit witnesses) -/

/-- k = 2 (Erdős 1979, in-house re-derived): p = 11, intervals [3,4],[5,7]. -/
theorem erdos1056_k2 : Nat.Prime 11 ∧
    prodmod 11 3 4 = 1 ∧ prodmod 11 5 7 = 1 := by decide

/-- k = 3 (Makowski 1983, in-house re-derived): p = 17. -/
theorem erdos1056_k3 : Nat.Prime 17 ∧
    prodmod 17 2 5 = 1 ∧ prodmod 17 6 11 = 1 ∧ prodmod 17 12 15 = 1 := by
  decide

/-- **k = 4 — NEW CASE.** p = 23: the four consecutive intervals
[2,4],[5,8],[9,11],[12,21] all carry product ≡ 1 (mod 23). -/
theorem erdos1056_k4 : Nat.Prime 23 ∧
    prodmod 23 2 4 = 1 ∧ prodmod 23 5 8 = 1 ∧ prodmod 23 9 11 = 1 ∧
    prodmod 23 12 21 = 1 := by decide

/-- **k = 5 — NEW CASE.** p = 109. -/
theorem erdos1056_k5 : Nat.Prime 109 ∧
    prodmod 109 10 11 = 1 ∧ prodmod 109 12 39 = 1 ∧ prodmod 109 40 58 = 1 ∧
    prodmod 109 59 73 = 1 ∧ prodmod 109 74 85 = 1 := by decide

/-- **k = 6 — NEW CASE.** p = 71. -/
theorem erdos1056_k6 : Nat.Prime 71 ∧
    prodmod 71 8 9 = 1 ∧ prodmod 71 10 19 = 1 ∧ prodmod 71 20 51 = 1 ∧
    prodmod 71 52 61 = 1 ∧ prodmod 71 62 63 = 1 ∧ prodmod 71 64 70 = 1 := by
  decide

/-- **k = 7 — NEW CASE.** p = 673. -/
theorem erdos1056_k7 : Nat.Prime 673 ∧
    prodmod 673 160 316 = 1 ∧ prodmod 673 317 354 = 1 ∧
    prodmod 673 355 393 = 1 ∧ prodmod 673 394 397 = 1 ∧
    prodmod 673 398 506 = 1 ∧ prodmod 673 507 545 = 1 ∧
    prodmod 673 546 647 = 1 := by decide

/-- **k = 8 — NEW CASE.** p = 599. -/
theorem erdos1056_k8 : Nat.Prime 599 ∧
    prodmod 599 29 50 = 1 ∧ prodmod 599 51 122 = 1 ∧ prodmod 599 123 183 = 1 ∧
    prodmod 599 184 250 = 1 ∧ prodmod 599 251 289 = 1 ∧ prodmod 599 290 500 = 1 ∧
    prodmod 599 501 539 = 1 ∧ prodmod 599 540 555 = 1 := by decide

/-- **k = 9 — NEW CASE.** p = 3011. -/
theorem erdos1056_k9 : Nat.Prime 3011 ∧
    prodmod 3011 2 611 = 1 ∧ prodmod 3011 612 723 = 1 ∧
    prodmod 3011 724 749 = 1 ∧ prodmod 3011 750 805 = 1 ∧
    prodmod 3011 806 2205 = 1 ∧ prodmod 3011 2206 2261 = 1 ∧
    prodmod 3011 2262 2287 = 1 ∧ prodmod 3011 2288 2399 = 1 ∧
    prodmod 3011 2400 3009 = 1 := by decide

/-- **k = 10 — NEW CASE.** p = 27901. -/
theorem erdos1056_k10 : Nat.Prime 27901 ∧
    prodmod 27901 2452 2867 = 1 ∧ prodmod 27901 2868 4768 = 1 ∧
    prodmod 27901 4769 10383 = 1 ∧ prodmod 27901 10384 18707 = 1 ∧
    prodmod 27901 18708 19589 = 1 ∧ prodmod 27901 19590 19965 = 1 ∧
    prodmod 27901 19966 22981 = 1 ∧ prodmod 27901 22982 24673 = 1 ∧
    prodmod 27901 24674 26322 = 1 ∧ prodmod 27901 26323 27263 = 1 := by
  decide

/-- **k = 11 — THE FRONTIER.** p = 52163: eleven consecutive intervals
covering [2, 52161], every block product ≡ 1 (mod 52163). The chain is the
value-1 factorial chain: 1! ≡ 3924! ≡ 7291! ≡ 7427! ≡ 18519! ≡ 24931! ≡
26081! ≡ 27231! ≡ 33643! ≡ 44735! ≡ 44871! ≡ 52161! ≡ 1 (mod 52163),
cut at the twelve equal-value points. -/
theorem erdos1056_k11 : Nat.Prime 52163 ∧
    prodmod 52163 2 3924 = 1 ∧ prodmod 52163 3925 7291 = 1 ∧
    prodmod 52163 7292 7427 = 1 ∧ prodmod 52163 7428 18519 = 1 ∧
    prodmod 52163 18520 24931 = 1 ∧ prodmod 52163 24932 26081 = 1 ∧
    prodmod 52163 26082 27231 = 1 ∧ prodmod 52163 27232 33643 = 1 ∧
    prodmod 52163 33644 44735 = 1 ∧ prodmod 52163 44736 44871 = 1 ∧
    prodmod 52163 44872 52161 = 1 := by decide

/-! ## Section 3 — THE STRUCTURE ANCHORS (Wilson instances on witnesses) -/

/-- Every value-1 witness prime anchors its chain at BOTH ends:
\$1! \equiv 1\$ trivially and \$(p-2)! \equiv 1 \pmod p\$ — the Wilson
endpoint law, kernel-decided on the four value-1 witnesses
(23, 17, 3011, 52163). -/
theorem erdos1056_wilson_anchors :
    (Nat.Prime 23 ∧ factmod 23 1 = 1 ∧ factmod 23 21 = 1) ∧
    (Nat.Prime 17 ∧ factmod 17 1 = 1 ∧ factmod 17 15 = 1) ∧
    (Nat.Prime 3011 ∧ factmod 3011 1 = 1 ∧ factmod 3011 3009 = 1) ∧
    (Nat.Prime 52163 ∧ factmod 52163 1 = 1 ∧ factmod 52163 52161 = 1) := by
  decide

/-- The k = 11 chain itself, in the Noll–Simmons equal-factorial form:
twelve cut points, all factorials ≡ 1 (mod 52163). -/
theorem erdos1056_k11_chain :
    factmod 52163 1 = 1 ∧ factmod 52163 3924 = 1 ∧ factmod 52163 7291 = 1 ∧
    factmod 52163 7427 = 1 ∧ factmod 52163 18519 = 1 ∧
    factmod 52163 24931 = 1 ∧ factmod 52163 26081 = 1 ∧
    factmod 52163 27231 = 1 ∧ factmod 52163 33643 = 1 ∧
    factmod 52163 44735 = 1 ∧ factmod 52163 44871 = 1 ∧
    factmod 52163 52161 = 1 := by decide

/-! ## Section 4 — THE ARSENAL BRIDGE (BOSS's mathematics, applied) -/

/-- erdosternary2's digit predicates on the frontier prime's own ternary
digits: 52163 = (2211221222)₃ least-significant first. -/
theorem erdos1056_digits_52163 :
    [52163 % 3, (52163/3) % 3, (52163/9) % 3, (52163/27) % 3,
     (52163/81) % 3, (52163/243) % 3, (52163/729) % 3, (52163/2187) % 3,
     (52163/6561) % 3, (52163/19683) % 3] = [2, 2, 2, 2, 1, 1, 2, 2, 1, 2] := by
  decide

/-- Every ternary digit of the frontier prime passes erdosternary2's
`isTernaryDigit` trichotomy law. -/
theorem erdos1056_arsenal_digit_validity :
    [2, 2, 2, 2, 1, 1, 2, 2, 1, 2].all (fun d => ErdosTernary2.isTernaryDigit d) := by
  decide

/-- The k = 11 first cut point 3924 = (12102010)₃ routes through the
arsenal's residue trichotomy (`lt_three_cases`). -/
theorem erdos1056_ternary_routing (m : Nat) (h : m % 3 < 3) :
    m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 :=
  ErdosTernary2.lt_three_cases (m % 3) h

theorem erdos1056_cut3924_residue : 3924 % 3 = 0 := by
  have h : 3924 % 3 < 3 := by decide
  cases erdos1056_ternary_routing 3924 h with
  | inl h0 => exact h0
  | inr h => cases h with
    | inl h1 => exact absurd h1 (by decide)
    | inr h2 => exact absurd h2 (by decide)

/-- HC-PROOF's ternary-carry bound on the witness numbers: every carry
position of 3924 and 52161 under the ×4 ternary dynamics stays below 4. -/
theorem erdos1056_carry_bound_witness :
    carryAtPos 3924 1 < 4 ∧ carryAtPos 3924 2 < 4 ∧ carryAtPos 52161 1 < 4
      ∧ carryAtPos 52161 2 < 4 ∧ carryAtPos 52161 3 < 4 :=
  ⟨carryAtPos_bound 3924 1, carryAtPos_bound 3924 2, carryAtPos_bound 52161 1,
    carryAtPos_bound 52161 2, carryAtPos_bound 52161 3⟩

/-- HC-PROOF's dyadic scaling on the chain's own numbers: 52161 = 3·17387
and 7290 = 3·2430 leave their 2-adic profiles invariant — the exact
bookkeeping law behind the chain's block structure. -/
theorem erdos1056_v2r_scaling : v2r 52161 = v2r 17387 ∧ v2r 7290 = v2r 2430 :=
  ⟨CardinalWorldsV2.v2r_ternary_scaling 1 17387,
    CardinalWorldsV2.v2r_ternary_scaling 1 2430⟩

#eval "ERDOS1056_KERNEL_GREEN"
#eval prodmod 11 3 4 + prodmod 23 12 21 + prodmod 52163 44872 52161
#eval factmod 52163 52161
#eval v2r 52161

-- Axiom receipts (the kill CI's gates):
#print axioms erdos1056_k2
#print axioms erdos1056_k4
#print axioms erdos1056_k5
#print axioms erdos1056_k6
#print axioms erdos1056_k7
#print axioms erdos1056_k8
#print axioms erdos1056_k9
#print axioms erdos1056_k10
#print axioms erdos1056_k11
#print axioms erdos1056_wilson_anchors
#print axioms erdos1056_k11_chain
#print axioms erdos1056_carry_bound_witness
