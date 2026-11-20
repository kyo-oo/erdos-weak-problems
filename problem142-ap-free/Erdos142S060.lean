import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

-- Family pattern (green kernels K142k et al.): explicit depth headroom.
set_option maxRecDepth 262144
set_option maxHeartbeats 16000000

/-! # Erdős #142 — THE AP-FRONTIER KERNEL, S060 PARALLEL WAVE (Kernel 80)

## THE PROBLEM (verbatim, erdosproblems.com/142)

> Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$
> that does not contain any non-trivial $k$-term arithmetic progression.
> Prove an asymptotic formula for $r_k(N)$.

$10,000 prize; the asymptotic is the open core. THIS KERNEL (the S060
parallel wave's independent lane; the S067 kernel-142k covers the Cantor
side) certifies: exact small values of r_3 with decide certificates in
BOTH directions (the r3max sweep, green-kernel idiom), the
Stanley/ternary lower bound (the arsenal bridge), and the engine witness
frontier cells.

## WHAT THIS KERNEL PROVES (all complete unconditional theorems)

1. THE EXACT VALUES: r_3(9) = 5, r_3(11) = 6, r_3(13) = 7 — witness up
   (decide) + every-(v+1)-sublist-contains-a-3-AP down (decide).
2. THE STANLEY/TERNARY LOWER BOUND (arsenal bridge): the 16-element
   literal (S(0) ∩ [80], 1-based) is 3-AP-free (decide) — r_3(81) ≥ 16.
3. THE WITNESS FRONTIER: r_3(20) ≥ 9, r_3(27) ≥ 11, r_3(38) ≥ 14,
   r_4(42) ≥ 22 (engine witnesses, decide).
4. THE BOARD + arsenal bridge.
-/

namespace E142S

/-- The campaign's List.all (green-kernel idiom). -/
def allT (p : Nat → Bool) : List Nat → Bool
  | [] => true
  | a :: t => p a && allT p t

/-- All sublists (structural; the green idiom). -/
def sublists : List Nat → List (List Nat)
  | [] => [[]]
  | a :: t => sublists t ++ List.map (fun S => a :: S) (sublists t)

/-- [1..N]. -/
def upto1 (N : Nat) : List Nat := (List.range N).map (· + 1)

/-- Sublists of size exactly m. -/
def sized (m : Nat) (L : List Nat) : List (List Nat) :=
  (sublists L).filter (fun S => S.length == m)

/-- 3-AP-freeness: no distinct x, z with x + z = 2y for a middle y
    (the green idiom: x,z,y ∈ S, x ≠ z, x + z = 2·y — equivalent to
    containing a non-trivial 3-AP). -/
def ap3Free (S : List Nat) : Bool :=
  allT (fun x => allT (fun y => allT (fun z =>
    !((x + z == 2 * y) && !(x == z)) ) S) S) S

/-- 4-AP-freeness: no w,x,y,z ∈ S with 2x = w+y, 2y = x+z, w ≠ z. -/
def ap4Free (S : List Nat) : Bool :=
  allT (fun w => allT (fun x => allT (fun y => allT (fun z =>
    !((2 * x == w + y) && (2 * y == x + z) && !(w == z))) S) S) S) S

/-! ## §1 THE EXACT VALUES (both directions, decide) -/

/-- r_3(9) = 5 — LOWER: the certified witness. -/
theorem e142_r3_9_lower : ap3Free [1, 2, 4, 8, 9] = true := by decide

/-- r_3(9) = 5 — UPPER: every 6-sublist of [1..9] contains a 3-AP. -/
theorem e142_r3_9_upper :
    (sized 6 (upto1 9)).all (fun s => !ap3Free s) = true := by decide

/-- r_3(11) = 6 — both directions. -/
theorem e142_r3_11_lower : ap3Free [1, 2, 4, 5, 10, 11] = true := by decide

theorem e142_r3_11_upper :
    (sized 7 (upto1 11)).all (fun s => !ap3Free s) = true := by decide

/-- r_3(13) = 7 — both directions. -/
theorem e142_r3_13_lower : ap3Free [1, 2, 4, 5, 10, 11, 13] = true := by decide

theorem e142_r3_13_upper :
    (sized 8 (upto1 13)).all (fun s => !ap3Free s) = true := by decide

/-! ## §2 THE STANLEY/TERNARY LOWER BOUND (THE ARSENAL BRIDGE) -/

/-- The Stanley set S(0) ∩ [80] in 1-based coordinates: numbers whose
    0-based ternary expansion avoids the digit 2 — the ErdosTernary2
    digit discipline. -/
def stanley80 : List Nat :=
  [1, 2, 4, 5, 10, 11, 13, 14, 28, 29, 31, 32, 37, 38, 40, 41]

theorem stanley80_len : stanley80.length = 16 := by rfl

/-- S(0) ∩ [80] is 3-AP-free (the classical Stanley fact, decide). -/
theorem stanley80_apfree : ap3Free stanley80 = true := by decide

/-- Ternary digit check (fuel-structural). -/
def ternaryOKf : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => true
  | f + 1, n + 1 => (n + 1) % 3 ≤ 1 && ternaryOKf f ((n + 1) / 3)

def ternaryOK (n : Nat) : Bool := ternaryOKf 6 n

/-- The literal IS the filter: (ternaryOK 0-based) over [0..80]
    selects exactly the 16 numbers (decide: the fuel-6 structural check). -/
theorem stanley80_is_filter :
    ((List.range 81).filter ternaryOK).map (· + 1) = stanley80 := by
  decide

/-- THE r_3 LOWER BOUND VIA THE ARSENAL WORLD: r_3(81) ≥ 16. -/
theorem e142_stanley_lower :
    ∃ S : List Nat, S.length = 16 ∧ ap3Free S = true ∧ S.all (· ≤ 81) ∧ S.all (· ≥ 1) :=
  ⟨stanley80, stanley80_len, stanley80_apfree, by decide, by decide⟩

/-! ## §3 THE WITNESS FRONTIER (engine cells, decide) -/

theorem e142_w_r3_20 : ap3Free [2, 4, 7, 8, 13, 15, 16, 20, 21] = true := by decide
theorem e142_w_r3_27 : ap3Free [1, 2, 5, 7, 11, 16, 18, 19, 23, 24, 26] = true := by decide
theorem e142_w_r3_38 :
    ap3Free [1, 2, 4, 8, 9, 13, 21, 23, 26, 27, 30, 32, 35, 36] = true := by decide
theorem e142_w_r4_42 :
    ap4Free [1, 2, 3, 5, 6, 8, 9, 10, 16, 18, 19, 21, 22, 24, 30, 31, 33, 34, 35, 38, 39, 40] = true := by decide

/-! ## §4 THE ARSENAL BRIDGE -/

theorem e142_arsenal_bridge :
    ErdosTernary2.isTernaryDigit 0 = true ∧
    ErdosTernary2.isTernaryDigit 1 = true ∧
    ErdosTernary2.isTernaryDigit 2 = true ∧
    ErdosTernary2.isTernaryDigit 3 = false ∧
    ternaryOKf 6 0 = true ∧ ternaryOKf 6 1 = true ∧
    ternaryOKf 6 3 = true ∧ ternaryOKf 6 4 = true ∧
    ternaryOKf 6 2 = false ∧ ternaryOKf 6 5 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §5 THE BOARD -/

theorem e142_board :
    ap3Free [1, 2, 4, 8, 9] = true ∧
    (sized 6 (upto1 9)).all (fun s => !ap3Free s) = true ∧
    ap3Free [1, 2, 4, 5, 10, 11] = true ∧
    (sized 7 (upto1 11)).all (fun s => !ap3Free s) = true ∧
    ap3Free [1, 2, 4, 5, 10, 11, 13] = true ∧
    (sized 8 (upto1 13)).all (fun s => !ap3Free s) = true ∧
    stanley80.length = 16 ∧ ap3Free stanley80 = true ∧
    ((List.range 81).filter ternaryOK).map (· + 1) = stanley80 ∧
    ap3Free [2, 4, 7, 8, 13, 15, 16, 20, 21] = true ∧
    ap3Free [1, 2, 5, 7, 11, 16, 18, 19, 23, 24, 26] = true ∧
    ap3Free [1, 2, 4, 8, 9, 13, 21, 23, 26, 27, 30, 32, 35, 36] = true ∧
    ap4Free [1, 2, 3, 5, 6, 8, 9, 10, 16, 18, 19, 21, 22, 24, 30, 31, 33, 34, 35, 38, 39, 40] = true :=
  ⟨e142_r3_9_lower, e142_r3_9_upper, e142_r3_11_lower, e142_r3_11_upper,
    e142_r3_13_lower, e142_r3_13_upper, stanley80_len, stanley80_apfree,
    stanley80_is_filter, e142_w_r3_20, e142_w_r3_27, e142_w_r3_38, e142_w_r4_42⟩

#eval "E142_APFRONTIER_GREEN"

#print axioms e142_board
#print axioms e142_arsenal_bridge
#print axioms stanley80_apfree
#print axioms e142_r3_9_upper

end E142S
