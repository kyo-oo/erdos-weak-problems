import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# GST affine source-neighbor two-trit carry entropy bound

The exact original physical affine pair is X, 4*X+1 with
X = (4^K-1)/3.  The multiplication/addition carry is c=0,1,2,3.

For source trit a in {0,1,2}, the target trit is (4*a+c)%3 and
next carry is (4*a+c)/3.  Disallowing simultaneous trit two removes
a=2 precisely at carry c=0 or c=3.

This kernel-checked module proves the uniform two-trit 7/9 branching
bound for the four-state survival automaton.  Separate prefix
isometry links the abstract 3-adic source prefixes with the actual
perfect-power exponent residues.  Density zero does not imply
absence of an exceptional individual physical exponent.
-/

namespace GSTProblem406CarryEntropyBound

/-- Number of words of length n surviving the original affine
source-neighbor no-shared-two controller from incoming carry c.
The four concrete carry states are 0,1,2,3. -/
def survivingCount : Nat → Nat → Nat
  | 0, _ => 1
  | n+1, c =>
      if c = 0 then
        survivingCount n 0 + survivingCount n 1
      else if c = 1 then
        survivingCount n 0 + survivingCount n 1 + survivingCount n 3
      else if c = 2 then
        survivingCount n 0 + survivingCount n 2 + survivingCount n 3
      else
        survivingCount n 1 + survivingCount n 2

/-- The exact two-trit branch totals at all carry states,
with no universal-gate assumption. -/
theorem surviving_two_trit_totals :
    survivingCount 2 0 = 5 ∧
    survivingCount 2 1 = 7 ∧
    survivingCount 2 2 = 7 ∧
    survivingCount 2 3 = 6 := by
  decide

/-- If every state has <= M continuations of length n, then every
state has <= 7 M continuations of length n+2.  This is the crucial
uniform independent-of-depth contraction. -/
theorem two_trit_block_contracts (n M : Nat)
    (h0 : survivingCount n 0 ≤ M)
    (h1 : survivingCount n 1 ≤ M)
    (h2 : survivingCount n 2 ≤ M)
    (h3 : survivingCount n 3 ≤ M) :
    ∀ c : Nat, c < 4 → survivingCount (n+2) c ≤ 7*M := by
  intro c hc
  interval_cases c <;> simp [survivingCount] <;> omega

/-- Uniform finite survivor-tree count at every even ternary
prefix depth, for every one of the four carries. -/
theorem even_depth_contracts (m : Nat) :
    ∀ c : Nat, c < 4 → survivingCount (2*m) c ≤ 7^m := by
  induction m with
  | zero =>
      intro c hc
      simp [survivingCount]
  | succ m ih =>
      have h := two_trit_block_contracts (2*m) (7^m)
        (ih 0 (by omega)) (ih 1 (by omega))
        (ih 2 (by omega)) (ih 3 (by omega))
      intro c hc
      have hstep : survivingCount (2*m+2) c ≤ 7*(7^m) := h c hc
      have hindex : 2*(m+1) = 2*m+2 := by omega
      rw [hindex, pow_succ]
      simpa [Nat.mul_comm] using hstep

/-- An odd trailing trit has at most three choices. -/
theorem odd_depth_contracts (m : Nat) :
    ∀ c : Nat, c < 4 → survivingCount (2*m+1) c ≤ 3*7^m := by
  have h0 := even_depth_contracts m 0 (by omega)
  have h1 := even_depth_contracts m 1 (by omega)
  have h2 := even_depth_contracts m 2 (by omega)
  have h3 := even_depth_contracts m 3 (by omega)
  intro c hc
  interval_cases c <;> simp [survivingCount] <;> omega

/-- The physical affine pair always enters carry state one. -/
theorem original_affine_pair_survivor_bound (m : Nat) :
    survivingCount (2*m) 1 ≤ 7^m :=
  even_depth_contracts m 1 (by omega)

#check surviving_two_trit_totals
#check two_trit_block_contracts
#check even_depth_contracts
#check odd_depth_contracts
#check original_affine_pair_survivor_bound
#print axioms surviving_two_trit_totals
#print axioms two_trit_block_contracts
#print axioms even_depth_contracts
#print axioms odd_depth_contracts
#print axioms original_affine_pair_survivor_bound

end GSTProblem406CarryEntropyBound
