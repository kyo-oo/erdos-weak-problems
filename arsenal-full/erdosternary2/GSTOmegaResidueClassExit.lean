import GSTOmegaThreeTritMultiplierLaw

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact GST residue-class infinity exclusion, not finite core enumeration

For all L>=5 and ALL unbounded positive 3-free multipliers u,
the first three postcut trits of 4^(4+u*3^L) contain a digit two
unless u modulo 27 belongs to EXACTLY FOUR source classes:
    10, 13, 19, 22.
Hence 14 of the 18 3-free residue classes are covered uniformly.

The 27-state computation here is symbolic/finite-state classification
of arbitrary natural u, NOT a bound on the size of any exponent.
The four omitted residue classes are NOT counterexamples; they only
remain clean through this particular three-trit window.
-/

namespace GSTOmegaResidueClassExit

open GSTFourPowerDirectResidue

/-- The entire three-trit quotient block agrees with the 19u word. -/
theorem three_trit_digit_bridge
    (L u k : Nat) (hL : 5 ≤ L) (hk : k < 3) :
    digit3 (4^(4+u*3^L)) (L+1+k) = digit3 (19*u) k := by
  have hmod27 :=
    GSTOmegaThreeTritMultiplierLaw.quotient_mod27_all_multipliers L u hL
  have hdiv : 3^(k+1) ∣ 27 := by
    have hp : 3^(k+1) ∣ 3^3 :=
      Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^3=27 by decide] using hp
  have hmod :
      (4^(4+u*3^L)/3^(L+1))%3^(k+1) =
      (19*u)%3^(k+1) := by
    calc
      (4^(4+u*3^L)/3^(L+1))%3^(k+1) =
        ((4^(4+u*3^L)/3^(L+1))%27)%3^(k+1) :=
          (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((19*u)%27)%3^(k+1) := by rw [hmod27]
      _ = (19*u)%3^(k+1) := Nat.mod_mod_of_dvd _ hdiv
  have hread :=
    digit3_eq_of_mod_next
      (4^(4+u*3^L)/3^(L+1)) (19*u) k hmod
  calc
    digit3 (4^(4+u*3^L)) (L+1+k) =
      digit3 (4^(4+u*3^L)/3^(L+1)) k := by
        unfold digit3
        have hp : 3^(L+1+k)=3^(L+1)*3^k := by rw [pow_add]
        rw [hp, ← Nat.div_div_eq_div_mul]
    _ = digit3 (19*u) k := hread

/-- The 27-element arithmetic classification; the proof contains
no scan over unbounded multipliers. -/
private theorem mod27_kernel_classification :
    ∀ r : Fin 27, r.val%3≠0 →
      r.val≠10 → r.val≠13 → r.val≠19 → r.val≠22 →
      ∃ k : Fin 3, digit3 (19*r.val) k.val=2 := by decide

/-- Two inputs with the same residue modulo 27 have identical
lowest three trits, for every k<3. -/
theorem three_trit_same_residue
    (u k : Nat) (hk : k < 3) :
    digit3 (19*u) k = digit3 (19*(u%27)) k := by
  have hdiv : 3^(k+1) ∣ 27 := by
    have hp : 3^(k+1) ∣ 3^3 :=
      Nat.pow_dvd_pow 3 (by omega)
    simpa only [show (3:Nat)^3=27 by decide] using hp
  have hbig : (19*u)%27 = (19*(u%27))%27 := by
    simp [Nat.mul_mod]
  have hmod : (19*u)%3^(k+1) = (19*(u%27))%3^(k+1) := by
    calc
      (19*u)%3^(k+1) = ((19*u)%27)%3^(k+1) :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = ((19*(u%27))%27)%3^(k+1) := by rw [hbig]
      _ = (19*(u%27))%3^(k+1) := Nat.mod_mod_of_dvd _ hdiv
  exact digit3_eq_of_mod_next _ _ k hmod

/-- A global, size-unrestricted 14-of-18 natural-core theorem:
only the four clean three-trit residue classes remain outside
this WINDOW result. -/
theorem fourteen_of_eighteen_threefree_classes_exit
    (L u : Nat) (hL : 5 ≤ L) (hthree : u%3≠0)
    (h10 : u%27≠10) (h13 : u%27≠13)
    (h19 : u%27≠19) (h22 : u%27≠22) :
    ∃ p : Nat, L+1 ≤ p ∧ p ≤ L+3 ∧
      digit3 (4^(4+u*3^L)) p=2 := by
  let r : Fin 27 := ⟨u%27, Nat.mod_lt _ (by decide)⟩
  have h3 : r.val%3≠0 := by
    have h : (u%27)%3 = u%3 :=
      Nat.mod_mod_of_dvd u (by decide : 3 ∣ 27)
    simpa only [r] using (by
      rw [h]
      exact hthree)
  have hc10 : r.val ≠ 10 := h10
  have hc13 : r.val ≠ 13 := h13
  have hc19 : r.val ≠ 19 := h19
  have hc22 : r.val ≠ 22 := h22
  obtain ⟨k,hk⟩ :=
    mod27_kernel_classification r h3 hc10 hc13 hc19 hc22
  have hval : digit3 (19*u) k.val=2 := by
    rw [three_trit_same_residue u k.val k.isLt]
    exact hk
  refine ⟨L+1+k.val, by omega, by omega, ?_⟩
  rw [three_trit_digit_bridge L u k.val hL k.isLt]
  exact hval

#print axioms three_trit_digit_bridge
#print axioms mod27_kernel_classification
#print axioms three_trit_same_residue
#print axioms fourteen_of_eighteen_threefree_classes_exit

end GSTOmegaResidueClassExit
