import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536

/-! # Erdős #686 — THE k=3 SQUARE WITNESS LAWS (S038, Kernel 32)

## THE PROBLEM (verbatim, erdosproblems.com/686)

> Can every integer $N\geq 2$ be written as
> \[N=\frac{\prod_{1\leq i\leq k}(m+i)}{\prod_{1\leq i\leq k}(n+i)}\]
> for some $k\geq 2$ and $m\geq n+k$?

(In-house reading consistent with Kill #20 / K16 and Kill #29 / K26:
$n \geq 1$. `Rep3 N m n` below is the $k=3$ case verbatim:
$\prod_{1\le i\le 3}(m+i) = N\prod_{1\le i\le 3}(n+i)$, $n\ge 1$,
$m \ge n+3$.)

## WHAT THIS KERNEL PROVES (statement first, proofs below — the NEW RULE)

1. **THE FIVE PRIMITIVE EDGES**: the five $k=3$ square witnesses
   $(t, m, n)$ — $(70, 47, 1)$, $(4, 13, 4)$, $(3, 25, 11)$,
   $(1189, 1679, 13)$, $(1798, 13453, 89)$ — each
   $\prod_{i\le 3}(m+i) = t^2\prod_{i\le 3}(n+i)$, kernel-decided
   exactly. The first two kernelize Theorem C of the derivation
   ($N=9, 16$); the last three are NEW (S037 engine discovery).
2. **THE CHAIN LAW** (`erdos686k3_chain`): the witness relation
   composes — if $\prod(m_1+i) = t_1^2\prod(n_1+i)$ and
   $\prod(m_2+i) = t_2^2\prod(n_2+i)$ with $n_1 = m_2$... concretely:
   $c_3(a) = t_1^2 c_3(b)$, $c_3(b) = t_2^2 c_3(c)$ $\Rightarrow$
   $c_3(a) = (t_1t_2)^2 c_3(c)$ (pure ring).
3. **THE COMPOSITE WITNESS** (`erdos686k3_rep4756`): $t = 4756 = 4\cdot
   1189$ at $(m, n) = (1679, 4)$ — the S037 "double hit" explained and
   PROVED: one product $1680\cdot1681\cdot1682$ serves two squares via
   the chain $4 \to 13 \to 1679$.
4. **THE k=3 SQUARE-CLASS THEOREM** (`erdos686k3_existence`): the six
   squares $9, 16, 4900, 1413721, 3232804, 22619536$ ALL have $k=3$
   representations — the first kernel-certified $k=3$ cases of the
   problem's square front.

Honest scope: these are witness theorems (unconditional existentials);
the general square classification at $k \geq 3$ remains open (engine
census: $t \leq 300$ exactly $\{3,4,70\}$; the full witness census
$t \leq 5000$ = exactly the six classes here — battery evidence).
$t = 3, 4$ are NOT $k=2$-representable (K26 census, kernel-certified);
$t = 70$ is $k=2$-family (both representations exist); $t = 1189, 1798,
4756$ exceed the kernelized $k=2$ census range. -/

namespace Erdos686K3

/-! ## §0 The definitions. -/

/-- The k=3 triple product c3(x) = (x+1)(x+2)(x+3). -/
def c3 (x : Nat) : Nat := (x + 1) * (x + 2) * (x + 3)

/-- The k=3 representation predicate (the problem's shape at k = 3):
∏_{1≤i≤3}(m+i) = N·∏_{1≤i≤3}(n+i) with n ≥ 1 and m ≥ n+3. -/
def Rep3 (N m n : Nat) : Prop :=
  c3 m = N * c3 n ∧ 1 ≤ n ∧ n + 3 ≤ m

/-! ## §1 THE FIVE PRIMITIVE EDGES (kernel-decided). -/

theorem edge70 : c3 47 = 70 * 70 * c3 1 := by decide

theorem edge4 : c3 13 = 4 * 4 * c3 4 := by decide

theorem edge3 : c3 25 = 3 * 3 * c3 11 := by decide

theorem edge1189 : c3 1679 = 1189 * 1189 * c3 13 := by decide

theorem edge1798 : c3 13453 = 1798 * 1798 * c3 89 := by decide

/-! ## §2 THE CHAIN LAW (the witness relation composes). -/

theorem erdos686k3_chain (a b c t1 t2 : Nat)
    (h1 : c3 a = t1 * t1 * c3 b) (h2 : c3 b = t2 * t2 * c3 c) :
    c3 a = (t1 * t2) * (t1 * t2) * c3 c := by
  rw [h1, h2]
  ring

/-! ## §3 THE COMPOSITE WITNESS (the 1679 double hit, proved). -/

theorem edge4756 : c3 1679 = 4756 * 4756 * c3 4 :=
  erdos686k3_chain 1679 13 4 1189 4 edge1189 edge4

/-! ## §4 THE SIX REPRESENTATIONS (the problem's own form). -/

theorem erdos686k3_rep70 : Rep3 (70 * 70) 47 1 := ⟨edge70, by decide, by decide⟩

theorem erdos686k3_rep4 : Rep3 (4 * 4) 13 4 := ⟨edge4, by decide, by decide⟩

theorem erdos686k3_rep3 : Rep3 (3 * 3) 25 11 := ⟨edge3, by decide, by decide⟩

theorem erdos686k3_rep1189 : Rep3 (1189 * 1189) 1679 13 := ⟨edge1189, by decide, by decide⟩

theorem erdos686k3_rep1798 : Rep3 (1798 * 1798) 13453 89 := ⟨edge1798, by decide, by decide⟩

theorem erdos686k3_rep4756 : Rep3 (4756 * 4756) 1679 4 := ⟨edge4756, by decide, by decide⟩

/-! ## §5 THE k=3 SQUARE-CLASS THEOREM (six squares, k=3 representations). -/

theorem erdos686k3_existence :
    (∃ m n, Rep3 9 m n) ∧ (∃ m n, Rep3 16 m n) ∧ (∃ m n, Rep3 4900 m n) ∧
    (∃ m n, Rep3 1413721 m n) ∧ (∃ m n, Rep3 3232804 m n) ∧
    (∃ m n, Rep3 22619536 m n) :=
  ⟨⟨25, 11, erdos686k3_rep3⟩, ⟨13, 4, erdos686k3_rep4⟩,
   ⟨47, 1, erdos686k3_rep70⟩, ⟨1679, 13, erdos686k3_rep1189⟩,
   ⟨13453, 89, erdos686k3_rep1798⟩, ⟨1679, 4, erdos686k3_rep4756⟩⟩

/-- THE MAIN SUMMARY: the five primitive edges + the composite. -/
theorem erdos686k3_main :
    Rep3 (3 * 3) 25 11 ∧ Rep3 (4 * 4) 13 4 ∧ Rep3 (70 * 70) 47 1 ∧
    Rep3 (1189 * 1189) 1679 13 ∧ Rep3 (1798 * 1798) 13453 89 ∧
    Rep3 (4756 * 4756) 1679 4 :=
  ⟨erdos686k3_rep3, erdos686k3_rep4, erdos686k3_rep70,
   erdos686k3_rep1189, erdos686k3_rep1798, erdos686k3_rep4756⟩

/-! ## §6 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal). -/
theorem erdos686k3_arsenal_bridge :
    [1679 % 3, (1679 / 3) % 3, (1679 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    [13453 % 3, (13453 / 3) % 3, (13453 / 9) % 3].all (fun d => ErdosTernary2.isTernaryDigit d) ∧
    carryAtPos 13456 1 < 4 ∧
    v2r (3 ^ 2 * 13456) = v2r 13456 :=
  ⟨by decide, by decide, carryAtPos_bound 13456 1,
    CardinalWorldsV2.v2r_ternary_scaling 2 13456⟩

#eval "ERDOS686K3_KERNEL_GREEN"
#print axioms erdos686k3_chain
#print axioms edge4756
#print axioms erdos686k3_rep1189
#print axioms erdos686k3_rep4756
#print axioms erdos686k3_existence
#print axioms erdos686k3_main
#print axioms erdos686k3_arsenal_bridge

end Erdos686K3
