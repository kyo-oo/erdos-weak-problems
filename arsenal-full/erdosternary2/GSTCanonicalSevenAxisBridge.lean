import GSTU2DExactCrossingCharge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTCanonicalSevenAxisBridge

open GST2DMixedEmergence
open GSTU2DEventTransport

/-- The three physical GST spaces carried by the seven-axis state. -/
inductive Space
  | null
  | altMinus
  | gstPlus
  deriving Repr, DecidableEq

def spaceOfCarry (C : Nat) : Space :=
  if C = 0 then .null else if C = 3 then .gstPlus else .altMinus

/-- Ternary information coordinate of one exact natural energy. -/
def digit3 (R p : Nat) : Nat := R / 3^p % 3

/-- x4 carry coordinate of one exact natural energy. -/
def carry4 (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p

/-- Canonical non-Euclidean seven-axis vertex.  The coordinates are arithmetic
state coordinates, not metric coordinates. -/
structure Vertex where
  horizontal : Nat
  horizontalNext : Nat
  vertical : Nat
  carry : Nat
  space : Space
  digit : Nat
  descent : Nat
  nextDescent : Nat
  deriving Repr

/-- The actual perfect-power sheet sampled in x4 horizontal stride. -/
def vertex (E t p : Nat) : Vertex where
  horizontal := t
  horizontalNext := t + 1
  vertical := p
  carry := carry4 (4^t * E) p
  space := spaceOfCarry (carry4 (4^t * E) p)
  digit := digit3 (4^t * E) p
  descent := (4^t * E) / 3^p
  nextDescent := (4^t * E) / 3^(p+1)

/-- The x4 carry regenerates exactly in the vertical ternary direction. -/
theorem carry4_forward_exact (R p : Nat) :
    carry4 R (p+1) = nextCarry (carry4 R p) (digit3 R p) := by
  simp only [carry4, digit3, nextCarry, Nat.pow_succ]
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : R % (3^p * 3) =
      R % 3^p + 3^p * (R / 3^p % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit]
  have hshape :
      4 * (R % 3^p + 3^p * (R / 3^p % 3)) =
        4 * (R % 3^p) + 3^p * (4 * (R / 3^p % 3)) := by ring
  rw [hshape, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ hp]

/-- Multiplication by four exposes the local x4 output trit exactly. -/
theorem digit3_mul_four_exact (R p : Nat) :
    digit3 (4 * R) p = outDigit (carry4 R p) (digit3 R p) := by
  unfold digit3 carry4 outDigit
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit : R = R % 3^p + 3^p * (R / 3^p) := by
    have h := Nat.mod_add_div R (3^p)
    omega
  have hscaled := congrArg (fun x : Nat => 4 * x) hsplit
  have hshape :
      4 * R = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by
    calc
      4 * R = 4 * (R % 3^p + 3^p * (R / 3^p)) := hscaled
      _ = 4 * (R % 3^p) + 3^p * (4 * (R / 3^p)) := by ring
  rw [hshape, Nat.add_mul_div_left _ _ hp]
  simp [Nat.add_mod, Nat.mul_mod]

/-- The canonical sheet is an exact x4/base3 cell lattice at every pair of
natural coordinates. -/
theorem canonical_cell_exact (E t p : Nat) :
    outDigit (vertex E t p).carry (vertex E t p).digit =
        (vertex E (t+1) p).digit ∧
      nextCarry (vertex E t p).carry (vertex E t p).digit =
        (vertex E t (p+1)).carry := by
  constructor
  · dsimp [vertex]
    have h := digit3_mul_four_exact (4^t * E) p
    rw [Nat.pow_succ]
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h.symm
  · dsimp [vertex]
    exact (carry4_forward_exact (4^t * E) p).symm

/-- The seven-axis carry always lies in the four physical GST spaces. -/
theorem vertex_carry_lt_four (E t p : Nat) : (vertex E t p).carry < 4 := by
  dsimp [vertex, carry4]
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hr : (4^t * E) % 3^p < 3^p := Nat.mod_lt _ hp
  exact (Nat.div_lt_iff_lt_mul hp).2 (by omega)

/-- Every seven-axis information digit is a physical ternary digit. -/
theorem vertex_digit_lt_three (E t p : Nat) : (vertex E t p).digit < 3 := by
  dsimp [vertex, digit3]
  exact Nat.mod_lt _ (by decide)

/-- The radix event coordinate of one x4 GST cell.  It records the input and
output trit in one number `0..8`; event eight is exactly `2 -> 2`. -/
def event (C d : Nat) : Nat := d + 3 * outDigit C d

/-- Exact seven-axis event balance.  The apparent x4/base3 exponential update
collapses to one linear arithmetic identity with a live upper carry. -/
theorem event_balance_exact (C d : Nat) :
    event C d + 9 * nextCarry C d = 13 * d + 3 * C := by
  have h := Nat.mod_add_div (C + 4*d) 3
  unfold event outDigit nextCarry
  omega

/-- Event eight is precisely the two physical Happy/SURVIVE realizations. -/
theorem happy_iff_event_eight
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ event C d = 8 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [HappyCell, event, outDigit]

/-- Canonical form: Happy is exactly event eight on the actual perfect-power
sheet, not on an exposed tail surrogate. -/
theorem canonical_happy_iff_event_eight (E t p : Nat) :
    HappyCell (vertex E t p).carry (vertex E t p).digit ↔
      event (vertex E t p).carry (vertex E t p).digit = 8 := by
  exact happy_iff_event_eight _ _ (vertex_carry_lt_four E t p)
    (vertex_digit_lt_three E t p)

#check canonical_cell_exact
#check event_balance_exact
#check canonical_happy_iff_event_eight
#print axioms canonical_cell_exact
#print axioms event_balance_exact
#print axioms canonical_happy_iff_event_eight

end GSTCanonicalSevenAxisBridge
