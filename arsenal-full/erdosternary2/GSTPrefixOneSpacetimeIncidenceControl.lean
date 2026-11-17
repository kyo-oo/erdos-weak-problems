import GSTPrefixOnePhaseIncidenceControl
import GSTResidueSpacetimeScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTSpacetimeV2

/-!
# Physical GST V2 spacetime rectangle

The horizontal coordinate is a genuine binary generation `r`; the vertical
coordinate is a genuine ternary position `p`.  No same-index child/parent
identification is made.  The local x2/base3 conservation law is summed over an
arbitrary rectangle, so the theorem is uniform in both depths and has no
terminal or finite-support hypothesis.
-/

/-- Binary carry word along a horizontal boundary. -/
def binaryBoundaryWord (a : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | L+1, p => 2 * binaryBoundaryWord a L p + a L p

/-- Ternary digit word below height `K` on one binary generation. -/
def ternaryBoundaryWord (d : Nat → Nat → Nat) (r : Nat) : Nat → Nat
  | 0 => 0
  | K+1 => ternaryBoundaryWord d r K + 3^K * d r K

/-- Exact microscopic x2/base3 cell law on an arbitrary rectangle. -/
def RectangleCells
    (a d : Nat → Nat → Nat) (L K : Nat) : Prop :=
  ∀ r p, r < L → p < K →
    a r p + 2 * d r p = d (r+1) p + 3 * a r (p+1)

/-- A horizontal row telescopes to its two digit endpoints and two carry words. -/
theorem rectangle_row_exact
    (a d : Nat → Nat → Nat) (L p : Nat)
    (hcell : ∀ r, r < L →
      a r p + 2 * d r p = d (r+1) p + 3 * a r (p+1)) :
    2^L * d 0 p + binaryBoundaryWord a L p =
      d L p + 3 * binaryBoundaryWord a L (p+1) := by
  induction L with
  | zero => simp [binaryBoundaryWord]
  | succ L ih =>
      have ih' :
          2^L * d 0 p + binaryBoundaryWord a L p =
            d L p + 3 * binaryBoundaryWord a L (p+1) :=
        ih (fun r hr => hcell r (by omega))
      have hlast := hcell L (by omega)
      calc
        2^(L+1) * d 0 p + binaryBoundaryWord a (L+1) p =
            2 * (2^L * d 0 p + binaryBoundaryWord a L p) + a L p := by
              simp only [binaryBoundaryWord, Nat.pow_succ]
              ring
        _ = 2 * (d L p + 3 * binaryBoundaryWord a L (p+1)) + a L p := by
              rw [ih']
        _ = d (L+1) p +
              3 * (2 * binaryBoundaryWord a L (p+1) + a L (p+1)) := by
              omega
        _ = d (L+1) p + 3 * binaryBoundaryWord a (L+1) (p+1) := by
              rfl

/-- Full two-dimensional cancellation.  Every interior term disappears; only
the four physical boundaries remain. -/
theorem rectangle_cancellation_exact
    (a d : Nat → Nat → Nat) (L K : Nat)
    (hgrid : RectangleCells a d L K) :
    binaryBoundaryWord a L 0 +
        2^L * ternaryBoundaryWord d 0 K =
      ternaryBoundaryWord d L K +
        3^K * binaryBoundaryWord a L K := by
  induction K with
  | zero => simp [ternaryBoundaryWord]
  | succ K ih =>
      have hprefix : RectangleCells a d L K := by
        intro r p hr hp
        exact hgrid r p hr (by omega)
      have ih' := ih hprefix
      have hrow := rectangle_row_exact a d L K
        (fun r hr => hgrid r K hr (by omega))
      calc
        binaryBoundaryWord a L 0 +
            2^L * ternaryBoundaryWord d 0 (K+1) =
          (binaryBoundaryWord a L 0 +
            2^L * ternaryBoundaryWord d 0 K) +
            3^K * (2^L * d 0 K) := by
              simp only [ternaryBoundaryWord]
              ring
        _ = (ternaryBoundaryWord d L K +
              3^K * binaryBoundaryWord a L K) +
              3^K * (2^L * d 0 K) := by
              rw [ih']
        _ = ternaryBoundaryWord d L K +
              3^K * (binaryBoundaryWord a L K + 2^L * d 0 K) := by
              ring
        _ = ternaryBoundaryWord d L K +
              3^K * (d L K + 3 * binaryBoundaryWord a L (K+1)) := by
              rw [show binaryBoundaryWord a L K + 2^L * d 0 K =
                  d L K + 3 * binaryBoundaryWord a L (K+1) by
                    simpa [Nat.add_comm] using hrow]
        _ = ternaryBoundaryWord d L (K+1) +
              3^(K+1) * binaryBoundaryWord a L (K+1) := by
              simp only [ternaryBoundaryWord, Nat.pow_succ]
              ring

/-- Binary-generation quotient recurrence at one ternary cut. -/
theorem physical_binary_quotient_succ
    (R r p : Nat) :
    (2^(r+1) * R) / 3^p =
      GSTPhysicalKernel.binaryColumnCarry R p r +
        2 * ((2^r * R) / 3^p) := by
  have hpow : 2^(r+1) * R = 2 * (2^r * R) := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [hpow]
  simpa [GSTPhysicalKernel.binaryColumnCarry] using
    GSTPhysicalKernel.binary_mul_two_quotient_decomposition (2^r * R) p

/-- Ternary quotient recurrence at one binary generation. -/
theorem physical_ternary_quotient_succ
    (X p : Nat) :
    X / 3^p = (X / 3^p) % 3 + 3 * (X / 3^(p+1)) := by
  calc
    X / 3^p = (X / 3^p) % 3 + 3 * ((X / 3^p) / 3) := by
      exact (Nat.mod_add_div (X / 3^p) 3).symm
    _ = (X / 3^p) % 3 + 3 * (X / 3^(p+1)) := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- The abstract rectangle cell is the literal GST physical binary column. -/
theorem physical_cell_exact
    (R r p : Nat) :
    GSTPhysicalKernel.binaryColumnCarry R p r +
        2 * GSTPhysicalKernel.binaryColumnDigit R p r =
      GSTPhysicalKernel.binaryColumnDigit R p (r+1) +
        3 * GSTPhysicalKernel.binaryColumnCarry R (p+1) r := by
  have hr := physical_binary_quotient_succ R r p
  have hr1 := physical_binary_quotient_succ R r (p+1)
  have hv := physical_ternary_quotient_succ (2^r * R) p
  have hv1 := physical_ternary_quotient_succ (2^(r+1) * R) p
  simp only [GSTPhysicalKernel.binaryColumnDigit] at hv hv1 ⊢
  omega

/-- Every finite window cut from the unbounded physical GST spacetime satisfies
the same uniform cell law. -/
theorem physical_rectangle_cells
    (R L K : Nat) :
    RectangleCells
      (fun r p => GSTPhysicalKernel.binaryColumnCarry R p r)
      (fun r p => GSTPhysicalKernel.binaryColumnDigit R p r) L K := by
  intro r p _hr _hp
  exact physical_cell_exact R r p

/-- A physical ternary boundary word is exactly the corresponding residue. -/
theorem physical_ternary_boundary_exact
    (R r K : Nat) :
    ternaryBoundaryWord
        (fun r p => GSTPhysicalKernel.binaryColumnDigit R p r) r K =
      (2^r * R) % 3^K := by
  induction K with
  | zero =>
      rw [ternaryBoundaryWord, Nat.pow_zero, Nat.mod_one]
  | succ K ih =>
      rw [ternaryBoundaryWord, ih]
      simpa [gstPrefixedModulusS, GSTPhysicalKernel.binaryColumnDigit,
        gstDigitS] using
        (gst_prefixed_residue_stepS 0 1 (2^r * R) K).symm

/-- A physical binary boundary word is exactly the wide carry across its
ternary cut. -/
theorem physical_binary_boundary_exact
    (R L p : Nat) :
    binaryBoundaryWord
        (fun r p => GSTPhysicalKernel.binaryColumnCarry R p r) L p =
      (2^L * (R % 3^p)) / 3^p := by
  induction L with
  | zero =>
      have hp : 0 < 3^p := Nat.pow_pos (by decide)
      have hr : R % 3^p < 3^p := Nat.mod_lt _ hp
      simp [binaryBoundaryWord, Nat.div_eq_of_lt hr]
  | succ L ih =>
      have hmod :
          (2^L * (R % 3^p)) % 3^p = (2^L * R) % 3^p := by
        simp only [Nat.mul_mod, Nat.mod_mod]
      have hcarry :
          GSTPhysicalKernel.binaryColumnCarry (R % 3^p) p L =
            GSTPhysicalKernel.binaryColumnCarry R p L := by
        simp only [GSTPhysicalKernel.binaryColumnCarry, hmod]
      have hstep := physical_binary_quotient_succ (R % 3^p) L p
      rw [binaryBoundaryWord, ih]
      rw [hcarry] at hstep
      omega

/-- Fully instantiated GST V2 rectangle.  It is valid for every binary width
and every ternary height, and retains the top wide-carry boundary instead of
assuming termination. -/
theorem physical_rectangle_exact
    (R L K : Nat) :
    2^L * (R % 3^K) =
      (2^L * R) % 3^K +
        3^K * ((2^L * (R % 3^K)) / 3^K) := by
  have h := rectangle_cancellation_exact
    (fun r p => GSTPhysicalKernel.binaryColumnCarry R p r)
    (fun r p => GSTPhysicalKernel.binaryColumnDigit R p r)
    L K (physical_rectangle_cells R L K)
  rw [physical_binary_boundary_exact,
      physical_ternary_boundary_exact,
      physical_ternary_boundary_exact,
      physical_binary_boundary_exact] at h
  simpa [Nat.mod_one] using h

/-!
The mass rectangle above is now refined by the physical signed kernel.  The
CREATE/DESTROY component is an exact horizontal boundary difference, while the
only interior source is a genuine common digit-two edge.  Summing over every
ternary row in an arbitrary window gives a two-dimensional event divergence,
not merely an unsigned value identity.
-/

/-- Signed GST V2 spacetime divergence.  The final double sum is the exact
interior x2 SURVIVE incidence charge. -/
theorem physical_signed_rectangle_incidence_exact
    (R L K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      Finset.sum (Finset.range L) (fun r =>
        GSTPhysicalKernel.signedKernelTwice
          (GSTPhysicalKernel.binaryColumnCarry R p r)
          (GSTPhysicalKernel.binaryColumnDigit R p r))) =
      14 *
        (Finset.sum (Finset.range K) (fun p =>
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R p L)) -
          Finset.sum (Finset.range K) (fun p =>
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R p 0))) +
      7 * Finset.sum (Finset.range K) (fun p =>
        Finset.sum (Finset.range L) (fun r =>
          GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R p r) *
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R p (r+1)))) := by
  calc
    Finset.sum (Finset.range K) (fun p =>
        Finset.sum (Finset.range L) (fun r =>
          GSTPhysicalKernel.signedKernelTwice
            (GSTPhysicalKernel.binaryColumnCarry R p r)
            (GSTPhysicalKernel.binaryColumnDigit R p r))) =
      Finset.sum (Finset.range K) (fun p =>
        14 *
          (GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R p L) -
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R p 0)) +
        7 * Finset.sum (Finset.range L) (fun r =>
          GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R p r) *
            GSTPhysicalKernel.twoIndicator
              (GSTPhysicalKernel.binaryColumnDigit R p (r+1)))) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact GSTPhysicalKernel.signedKernelTwice_physical_telescope R p L
    _ = 14 *
          (Finset.sum (Finset.range K) (fun p =>
              GSTPhysicalKernel.twoIndicator
                (GSTPhysicalKernel.binaryColumnDigit R p L)) -
            Finset.sum (Finset.range K) (fun p =>
              GSTPhysicalKernel.twoIndicator
                (GSTPhysicalKernel.binaryColumnDigit R p 0))) +
        7 * Finset.sum (Finset.range K) (fun p =>
          Finset.sum (Finset.range L) (fun r =>
            GSTPhysicalKernel.twoIndicator
                (GSTPhysicalKernel.binaryColumnDigit R p r) *
              GSTPhysicalKernel.twoIndicator
                (GSTPhysicalKernel.binaryColumnDigit R p (r+1)))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_sub_distrib]

/-- Positive interior incidence charge yields an actual spacetime cell whose
two consecutive physical binary columns both carry digit two. -/
theorem physical_incidence_exists_of_positive
    (R L K : Nat)
    (hpos : 0 < Finset.sum (Finset.range K) (fun p =>
      Finset.sum (Finset.range L) (fun r =>
        GSTPhysicalKernel.twoIndicator
            (GSTPhysicalKernel.binaryColumnDigit R p r) *
          GSTPhysicalKernel.twoIndicator
            (GSTPhysicalKernel.binaryColumnDigit R p (r+1))))) :
    ∃ p, p < K ∧ ∃ r, r < L ∧
      GSTPhysicalKernel.binaryColumnDigit R p r = 2 ∧
      GSTPhysicalKernel.binaryColumnDigit R p (r+1) = 2 := by
  by_contra hnone
  have hpoint : ∀ p, p < K → ∀ r, r < L →
      ¬ (GSTPhysicalKernel.binaryColumnDigit R p r = 2 ∧
        GSTPhysicalKernel.binaryColumnDigit R p (r+1) = 2) := by
    intro p hp r hr hpair
    apply hnone
    exact ⟨p, hp, r, hr, hpair⟩
  have hzero : Finset.sum (Finset.range K) (fun p =>
      Finset.sum (Finset.range L) (fun r =>
        GSTPhysicalKernel.twoIndicator
            (GSTPhysicalKernel.binaryColumnDigit R p r) *
          GSTPhysicalKernel.twoIndicator
            (GSTPhysicalKernel.binaryColumnDigit R p (r+1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro r hr
    have hpK : p < K := Finset.mem_range.mp hp
    have hrL : r < L := Finset.mem_range.mp hr
    have hno := hpoint p hpK r hrL
    by_cases hleft : GSTPhysicalKernel.binaryColumnDigit R p r = 2
    · have hright : GSTPhysicalKernel.binaryColumnDigit R p (r+1) ≠ 2 := by
        intro hright
        exact hno ⟨hleft, hright⟩
      simp [GSTPhysicalKernel.twoIndicator, hleft, hright]
    · simp [GSTPhysicalKernel.twoIndicator, hleft]
  omega

/-- Exact all-depth vertical flux of the handwritten U potential.  The identity
is valid at every observation height `K`; it keeps the live upper carry and
never replaces it by a terminal state. -/
theorem seeded_u_jump_flux_exact
    (D X K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      ((3^j : Nat) : Int) *
        gstHandwrittenUJumpS
          (gstAffineCarryS D X j) (gstDigitS X j)) =
      ((3^K : Nat) : Int) *
          (gstHandwrittenUChargeS (gstAffineCarryS D X K) : Int) -
        (gstHandwrittenUChargeS D : Int) -
        24 * (X % 3^K : Int) := by
  induction K with
  | zero => simp [gstAffineCarryS]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, gstHandwrittenUJumpS,
        gstAffineCarryS_forward_exact_all,
        gst_prefix_residue_succ_exactS, Nat.pow_succ]
      push_cast
      ring

/-! ## Canonical full-energy embedding

The affine tails are not external words.  After shifting past the exact
`3^(s+2)` prefix, they are four literal columns of one perfect-power binary
spacetime.
-/

def canonicalFullEnergy (s n : Nat) : Nat :=
  4^(3^(s+1) * n)

def canonicalBinaryWidth (s : Nat) : Nat :=
  2 * 3^s

def canonicalChildTail (s n : Nat) : Nat :=
  gstNavigationConstant (s+1) n

def canonicalParentTail (s n : Nat) : Nat :=
  c s / 3 + 4^(3^s) * canonicalChildTail s n

/-- If one physical column has a low prefix below `3^t`, every digit above the
cut is exactly the corresponding digit of its exposed tail. -/
theorem physical_column_tail_digit_exact
    (R r t q P Q : Nat)
    (hP : P < 3^t)
    (hdecomp : 2^r * R = P + 3^t * Q) :
    GSTPhysicalKernel.binaryColumnDigit R (t+q) r = gstDigit Q q := by
  unfold GSTPhysicalKernel.binaryColumnDigit gstDigit
  have ht : 0 < 3^t := Nat.pow_pos (by decide)
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hdecomp,
    Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt hP, Nat.zero_add]

/-- The full child energy exposes exactly the child Navigation tail after the
`s+2` prefix. -/
theorem canonical_full_energy_decomposition
    (s n : Nat) :
    canonicalFullEnergy s n =
      1 + 3^(s+2) * canonicalChildTail s n := by
  simpa [canonicalFullEnergy, canonicalChildTail, Nat.add_assoc] using
    gst_navigation_decomposition (s+1) n (by omega)

/-- The canonical horizontal phase multiplier has the exact phase-one low
prefix and affine tail offset. -/
theorem canonical_phase_multiplier_decomposition
    (s : Nat) (hs : 1 ≤ s) :
    4^(3^s) =
      1 + 3^(s+1) + 3^(s+2) * (c s / 3) := by
  have hcmod : c s % 3 = 1 := c_mod3 s hs
  have hc : c s = 1 + 3 * (c s / 3) := by
    have hsplit := Nat.mod_add_div (c s) 3
    rw [hcmod] at hsplit
    omega
  calc
    4^(3^s) = 1 + 3^(s+1) * c s := lte_identity s hs
    _ = 1 + 3^(s+1) * (1 + 3 * (c s / 3)) := by
      conv_lhs => rw [hc]
    _ = 1 + 3^(s+1) + 3^(s+2) * (c s / 3) := by
      rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
      ring

/-- Exact low-prefix decompositions of the child pair and the phase-one parent
pair inside one physical binary spacetime. -/
theorem canonical_full_energy_four_column_decompositions
    (s n : Nat) (hs : 1 ≤ s) :
    let E := canonicalFullEnergy s n
    let T := canonicalChildTail s n
    let X := canonicalParentTail s n
    let L := canonicalBinaryWidth s
    (2^0 * E = 1 + 3^(s+2) * T) ∧
    (2^2 * E = 4 + 3^(s+2) * (4*T)) ∧
    (2^L * E =
      (1 + 3^(s+1)) + 3^(s+2) * X) ∧
    (2^(L+2) * E =
      (4 + 3^(s+1)) + 3^(s+2) * (1 + 4*X)) := by
  dsimp only
  have hE := canonical_full_energy_decomposition s n
  have hA := canonical_phase_multiplier_decomposition s hs
  have hbridge := gpt56_parent_multiplier_is_binary_bridge s
  constructor
  · simpa using hE
  constructor
  · calc
      2^2 * canonicalFullEnergy s n = 4 * canonicalFullEnergy s n := by norm_num
      _ = 4 * (1 + 3^(s+2) * canonicalChildTail s n) := by rw [hE]
      _ = 4 + 3^(s+2) * (4 * canonicalChildTail s n) := by ring
  constructor
  · calc
      2^(canonicalBinaryWidth s) * canonicalFullEnergy s n =
          4^(3^s) * canonicalFullEnergy s n := by
            rw [canonicalBinaryWidth, ← hbridge]
      _ = 4^(3^s) *
          (1 + 3^(s+2) * canonicalChildTail s n) := by rw [hE]
      _ = (1 + 3^(s+1)) +
          3^(s+2) * canonicalParentTail s n := by
            unfold canonicalParentTail
            rw [hA]
            ring
  · calc
      2^(canonicalBinaryWidth s + 2) * canonicalFullEnergy s n =
          4 * (2^(canonicalBinaryWidth s) * canonicalFullEnergy s n) := by
            rw [Nat.pow_add]
            norm_num
            ring
      _ = 4 * ((1 + 3^(s+1)) +
          3^(s+2) * canonicalParentTail s n) := by
            rw [show 2^(canonicalBinaryWidth s) * canonicalFullEnergy s n =
              (1 + 3^(s+1)) +
                3^(s+2) * canonicalParentTail s n by
                  calc
                    2^(canonicalBinaryWidth s) * canonicalFullEnergy s n =
                        4^(3^s) * canonicalFullEnergy s n := by
                          rw [canonicalBinaryWidth, ← hbridge]
                    _ = 4^(3^s) *
                        (1 + 3^(s+2) * canonicalChildTail s n) := by rw [hE]
                    _ = (1 + 3^(s+1)) +
                        3^(s+2) * canonicalParentTail s n := by
                          unfold canonicalParentTail
                          rw [hA]
                          ring]
      _ = (4 + 3^(s+1)) +
          3^(s+2) * (1 + 4 * canonicalParentTail s n) := by
            rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
            ring

/-- The child Happy pair and the phase-one parent pair are the stride-two
boundary columns `(0,2)` and `(L,L+2)` of the same full-energy grid. -/
theorem canonical_full_energy_four_column_digits
    (s n q : Nat) (hs : 1 ≤ s) :
    let E := canonicalFullEnergy s n
    let T := canonicalChildTail s n
    let X := canonicalParentTail s n
    let L := canonicalBinaryWidth s
    GSTPhysicalKernel.binaryColumnDigit E (s+2+q) 0 = gstDigit T q ∧
    GSTPhysicalKernel.binaryColumnDigit E (s+2+q) 2 = gstDigit (4*T) q ∧
    GSTPhysicalKernel.binaryColumnDigit E (s+2+q) L = gstDigit X q ∧
    GSTPhysicalKernel.binaryColumnDigit E (s+2+q) (L+2) =
      gstDigit (1+4*X) q := by
  dsimp only
  obtain ⟨h0, h2, hL, hL2⟩ :=
    canonical_full_energy_four_column_decompositions s n hs
  have hD : 3 ≤ 3^(s+1) := by
    have h9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    omega
  have hB : 3^(s+2) = 3 * 3^(s+1) := by
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hp0 : 1 < 3^(s+2) := by
    rw [hB]
    omega
  have hp2 : 4 < 3^(s+2) := by
    rw [hB]
    omega
  have hpL : 1 + 3^(s+1) < 3^(s+2) := by
    rw [hB]
    omega
  have hpL2 : 4 + 3^(s+1) < 3^(s+2) := by
    rw [hB]
    omega
  exact ⟨
    physical_column_tail_digit_exact
      (canonicalFullEnergy s n) 0 (s+2) q 1
      (canonicalChildTail s n) hp0 h0,
    physical_column_tail_digit_exact
      (canonicalFullEnergy s n) 2 (s+2) q 4
      (4 * canonicalChildTail s n) hp2 h2,
    physical_column_tail_digit_exact
      (canonicalFullEnergy s n) (canonicalBinaryWidth s) (s+2) q
      (1 + 3^(s+1)) (canonicalParentTail s n) hpL hL,
    physical_column_tail_digit_exact
      (canonicalFullEnergy s n) (canonicalBinaryWidth s + 2) (s+2) q
      (4 + 3^(s+1)) (1 + 4 * canonicalParentTail s n) hpL2 hL2⟩

/-- The Navigation witness produces a stride-two child incidence on the
full-energy grid, while phase-one badness excludes every corresponding parent
incidence on the right boundary of that same grid. -/
theorem canonical_full_energy_boundary_events
    (s n : Nat) (hs : 1 ≤ s)
    (hchild : GSTNavigationWitness (canonicalChildTail s n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    let E := canonicalFullEnergy s n
    let L := canonicalBinaryWidth s
    (∃ q,
      GSTPhysicalKernel.binaryColumnDigit E (s+2+q) 0 = 2 ∧
      GSTPhysicalKernel.binaryColumnDigit E (s+2+q) 2 = 2) ∧
    (∀ q, ¬
      (GSTPhysicalKernel.binaryColumnDigit E (s+2+q) L = 2 ∧
       GSTPhysicalKernel.binaryColumnDigit E (s+2+q) (L+2) = 2)) := by
  dsimp only
  have hparentV2 :
      GSTV2.SeededBadTrace 1 (canonicalParentTail s n) := by
    simpa [canonicalParentTail, canonicalChildTail,
      GSTV2.CoupledState.parentWord, gpt56PhaseInitialState,
      gpt56PhaseA, gpt56PhaseT] using
      gpt56_phase_bad_to_v2_seeded s n hs hBad
  have hparentS :
      GSTSeededBadTraceS 1 (canonicalParentTail s n) := by
    simpa [GSTV2.SeededBadTrace, GSTV2.Happy, GSTV2.affineCarry,
      GSTV2.digit, GSTSeededBadTraceS, GSTBadPairS,
      gstAffineMulCarryS, gstDigitS] using hparentV2
  have hparentNo :=
    (gst_seeded_bad_iff_no_common_twoS
      1 (canonicalParentTail s n) (by decide)).1 hparentS
  have hchildCommon : ∃ q,
      gstDigitS (canonicalChildTail s n) q = 2 ∧
      gstDigitS (4 * canonicalChildTail s n) q = 2 := by
    obtain ⟨q, hnull | hplus⟩ :=
      gpt56_first_navigation_gate_exact_binary_chord
        (canonicalChildTail s n) hchild
    · have hhappy :
          gstDigitS (canonicalChildTail s n) q = 2 ∧
            (gstAffineMulCarryS 4 0 (canonicalChildTail s n) q = 0 ∨
             gstAffineMulCarryS 4 0 (canonicalChildTail s n) q = 3) := by
        exact ⟨
          by simpa [gstDigitS, gstDigit] using hnull.1,
          Or.inl (by simpa [gstAffineMulCarryS, gstCarry] using hnull.2.1)⟩
      have hcommon :=
        (gst_seeded_happy_iff_common_twoS
          0 (canonicalChildTail s n) q (by decide)).1 hhappy
      exact ⟨q, by simpa only [Nat.zero_add] using hcommon⟩
    · have hhappy :
          gstDigitS (canonicalChildTail s n) q = 2 ∧
            (gstAffineMulCarryS 4 0 (canonicalChildTail s n) q = 0 ∨
             gstAffineMulCarryS 4 0 (canonicalChildTail s n) q = 3) := by
        exact ⟨
          by simpa [gstDigitS, gstDigit] using hplus.1,
          Or.inr (by simpa [gstAffineMulCarryS, gstCarry] using hplus.2.1)⟩
      have hcommon :=
        (gst_seeded_happy_iff_common_twoS
          0 (canonicalChildTail s n) q (by decide)).1 hhappy
      exact ⟨q, by simpa only [Nat.zero_add] using hcommon⟩
  constructor
  · obtain ⟨q, hq0, hq2⟩ := hchildCommon
    obtain ⟨h0, h2, _hL, _hL2⟩ :=
      canonical_full_energy_four_column_digits s n q hs
    refine ⟨q, ?_, ?_⟩
    · rw [h0]
      simpa [gstDigitS, gstDigit] using hq0
    · rw [h2]
      simpa [gstDigitS, gstDigit] using hq2
  · intro q hright
    obtain ⟨_h0, _h2, hL, hL2⟩ :=
      canonical_full_energy_four_column_digits s n q hs
    have hx := hright.1
    have hx4 := hright.2
    rw [hL] at hx
    rw [hL2] at hx4
    apply hparentNo q
    exact ⟨
      by simpa [gstDigitS, gstDigit] using hx,
      by simpa [gstDigitS, gstDigit] using hx4⟩

end GSTSpacetimeV2

#check GSTSpacetimeV2.physical_cell_exact
#check GSTSpacetimeV2.physical_rectangle_exact
#check GSTSpacetimeV2.physical_signed_rectangle_incidence_exact
#check GSTSpacetimeV2.physical_incidence_exists_of_positive
#check GSTSpacetimeV2.seeded_u_jump_flux_exact
#check GSTSpacetimeV2.canonical_full_energy_four_column_digits
#check GSTSpacetimeV2.canonical_full_energy_boundary_events
#print axioms GSTSpacetimeV2.physical_rectangle_exact
#print axioms GSTSpacetimeV2.physical_signed_rectangle_incidence_exact
#print axioms GSTSpacetimeV2.physical_incidence_exists_of_positive
#print axioms GSTSpacetimeV2.seeded_u_jump_flux_exact
#print axioms GSTSpacetimeV2.canonical_full_energy_four_column_digits
#print axioms GSTSpacetimeV2.canonical_full_energy_boundary_events
