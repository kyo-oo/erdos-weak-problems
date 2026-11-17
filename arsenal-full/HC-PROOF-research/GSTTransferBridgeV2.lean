import Mathlib
import GSTTransferBridge
import GSTHodgeAssaultV2
import GSTClayOfficialV2
import GSTUniversalAddressBridge
import GSTDimensionFreeHodgeDiagonal

/-!
# TRANSFER BRIDGE V2 — ALL-WEIGHT EXACT ADDRESS CLASSIFICATION

The address map remains the exact twelve-coordinate bridge.  This layer
strengthens its internal classification to every natural weight and makes
the live-sector coefficient unique.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace GSTTransferBridgeV2

open GSTWaveCohomology
open GSTLefschetzCrown
open GSTHodgeAssault
open GSTHodgeAssaultV2
open GSTClayOfficial
open GSTClayOfficialV2
open GSTTransferBridge

/-- Monomials whose address degree is outside the twelve-cell basis vanish. -/
theorem clMono_zero_of_twelve_le (n : Nat) (hn : 12 ≤ n) :
    clMono n = fun _ => 0 := by
  funext i
  have hi : (i : Nat) < 12 := i.isLt
  unfold clMono
  rw [if_neg]
  omega

/-- Above weight two, the classical-address Hodge condition forces zero. -/
theorem clHodge_zero_of_three_le
    (p : Nat) (hp : 3 ≤ p) (φ : ClRing)
    (hφ : isClHodge p φ) :
    φ = fun _ => 0 := by
  funext i
  have hi : (i : Nat) < 12 := i.isLt
  exact hφ i (by omega)

/-- Zero belongs to every classical-address Hodge sector. -/
theorem zero_isClHodge (p : Nat) :
    isClHodge p (fun _ => 0) := by
  intro i hi
  rfl

/-- The address of the zero wave is the zero address. -/
theorem addr_zero :
    addr (fun _ : WaveCell => (0 : ℤ)) = (fun _ => 0) := by
  funext i
  rcases i with ⟨i, hi⟩
  unfold addr
  interval_cases i <;> rfl

/-- **ALL-WEIGHT HODGE TRANSPORT.**  The address support condition and the
GST diagonal support condition agree for every natural weight. -/
theorem transfer_hodge_iff_all_weights (p : Nat) (f : WaveCoef) :
    isClHodge p (addr f) ↔ isHodgeClass p f := by
  by_cases hp : p < 3
  · exact transfer_hodge_iff p hp f
  · have hp3 : 3 ≤ p := by omega
    constructor
    · intro hcl
      have hazero := clHodge_zero_of_three_le p hp3 (addr f) hcl
      have haddr0 : addr f = addr (fun _ : WaveCell => (0:ℤ)) :=
        hazero.trans addr_zero.symm
      have hf0 := addr_injective haddr0
      rw [hf0]
      exact zero_isHodgeClass p
    · intro hf
      have hf0 := hodge_class_zero_of_three_le p hp3 f hf
      rw [hf0, addr_zero]
      exact zero_isClHodge p

/-- **ALL-WEIGHT ADDRESS CLASSIFICATION.**  Every address-Hodge class is
exactly a scalar multiple of its degree-4p monomial.  For p >= 3 this is
the zero-sector statement. -/
theorem transferred_hodge_all_weights (p : Nat) (φ : ClRing) :
    isClHodge p φ ↔
      ∃ z : ℤ, ∀ i : Fin 12, φ i = z * clMono (4*p) i := by
  by_cases hp : p < 3
  · constructor
    · intro hφ
      exact transferred_hodge_conjecture p hp φ hφ
    · rintro ⟨z,hz⟩
      intro i hine
      rw [hz i]
      unfold clMono
      rw [if_neg hine, mul_zero]
  · have hp3 : 3 ≤ p := by omega
    constructor
    · intro hφ
      have hzero := clHodge_zero_of_three_le p hp3 φ hφ
      refine ⟨0, ?_⟩
      intro i
      rw [hzero]
      simp
    · rintro ⟨z,hz⟩
      have hm0 : clMono (4*p) = fun _ => 0 :=
        clMono_zero_of_twelve_le (4*p) (by omega)
      have hzero : φ = fun _ => 0 := by
        funext i
        rw [hz i, hm0]
        simp
      rw [hzero]
      exact zero_isClHodge p

/-- On a live address sector, the coefficient is read directly at degree 4p. -/
theorem transferred_coefficient_exact
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (hφ : isClHodge p φ) :
    ∀ i : Fin 12,
      φ i = φ ⟨4*p, by omega⟩ * clMono (4*p) i := by
  obtain ⟨z,hz⟩ := transferred_hodge_conjecture p hp φ hφ
  have hdiag := hz ⟨4*p, by omega⟩
  have hmono : clMono (4*p) ⟨4*p, by omega⟩ = (1:ℤ) := by
    simp [clMono]
  rw [hmono, mul_one] at hdiag
  intro i
  rw [hz i, hdiag]

/-- The live-sector coefficient is unique. -/
theorem transferred_coefficient_unique
    (p : Nat) (hp : p < 3) (φ : ClRing)
    (z w : ℤ)
    (hz : ∀ i : Fin 12, φ i = z * clMono (4*p) i)
    (hw : ∀ i : Fin 12, φ i = w * clMono (4*p) i) :
    z = w := by
  have hz0 := hz ⟨4*p, by omega⟩
  have hw0 := hw ⟨4*p, by omega⟩
  simp [clMono] at hz0 hw0
  omega

/-- Above weight two every address-Hodge class is zero and its rationalization
is therefore zero as well. -/
theorem transferred_zero_sector
    (p : Nat) (hp : 3 ≤ p) (φ : ClRing)
    (hφ : isClHodge p φ) :
    φ = fun _ => 0 :=
  clHodge_zero_of_three_le p hp φ hφ

/-- Cup transport can be iterated simultaneously along both native axes. -/
theorem addr_mixed_cup_iterate
    (a b : Nat) (g : WaveCoef) :
    addr ((Nat.iterate cupDigit a) ((Nat.iterate cupCarry b) g)) =
      (Nat.iterate clCupD a) ((Nat.iterate clCupV b) (addr g)) := by
  rw [addr_cupDigit_iterate, addr_cupCarry_iterate]

theorem transfer_v2_crown :
    (∀ p f, isClHodge p (addr f) ↔ isHodgeClass p f)
    ∧ (∀ p φ, isClHodge p φ ↔
      ∃ z : ℤ, ∀ i : Fin 12, φ i = z * clMono (4*p) i)
    ∧ (∀ p (hp : p < 3) (φ : ClRing), isClHodge p φ →
      ∀ i : Fin 12,
        φ i = φ ⟨4*p, by omega⟩ * clMono (4*p) i) := by
  exact ⟨transfer_hodge_iff_all_weights,
    transferred_hodge_all_weights,
    transferred_coefficient_exact⟩

/-! ## Limitless compact address classification

The historical `Fin 12` address ring remains an exact finite chart.  The
stronger carrier below is countable and finitely supported, so no global
address rank or terminal Hodge weight is built into the transfer layer.
-/

abbrev CompactClRing : Type := ℕ →₀ ℤ

def compactClCode (p : Nat) : Nat := Nat.pair p p

noncomputable def compactClMono (p : Nat) : CompactClRing :=
  Finsupp.single (compactClCode p) 1

/-- Weight-p compact address classes are supported only at the unique
unbounded diagonal code attached to p. -/
def isCompactClHodge (p : Nat) (φ : CompactClRing) : Prop :=
  ∀ i : Nat, i ≠ compactClCode p → φ i = 0

/-- The compact transfer code is literally the universal address of the
weight-p cosmic diagonal cell.  There is no parallel address convention. -/
theorem compactClCode_eq_cosmicAddress (p : Nat) :
    compactClCode p =
      GSTUniversalAddressBridge.cosmicAddressEquiv (p, p) := by
  rfl

/-- The limitless transfer generator is exactly the universal-address image
of the genuine compact cosmic diagonal class.  Thus the transfer layer and
the dimension-free Hodge cosmology use one and the same unbounded object. -/
theorem compactClMono_eq_cosmicDiagonalAddress (p : Nat) :
    compactClMono p =
      GSTUniversalAddressBridge.compactAddressEquiv
        (GSTDimensionFreeHodgeDiagonal.cosmicDiagonalClass p) := by
  ext i
  simp [compactClMono, compactClCode,
    GSTUniversalAddressBridge.compactAddressEquiv,
    GSTUniversalAddressBridge.cosmicAddressEquiv,
    GSTDimensionFreeHodgeDiagonal.cosmicDiagonalClass]

/-- Every natural weight has a nonzero compact-address Hodge generator. -/
theorem compactClMono_isHodge (p : Nat) :
    isCompactClHodge p (compactClMono p) := by
  intro i hi
  simp [compactClMono, hi]

/-- **RANK-FREE COMPACT ADDRESS CLASSIFICATION.**  At every natural weight,
the compact Hodge sector is rank one, with no `Fin 12` or `p < 3` ceiling. -/
theorem compactClHodge_rank_one (p : Nat) (φ : CompactClRing) :
    isCompactClHodge p φ ↔
      ∃! z : ℤ, φ = z • compactClMono p := by
  constructor
  · intro hφ
    refine ⟨φ (compactClCode p), ?_, ?_⟩
    · ext i
      by_cases hi : i = compactClCode p
      · subst i
        simp [compactClMono]
      · simp [compactClMono, hi, hφ i hi]
    · intro z hz
      have hread := congrArg
        (fun ψ : CompactClRing => ψ (compactClCode p)) hz
      simpa [compactClMono] using hread.symm
  · rintro ⟨z, hz, _⟩
    intro i hi
    rw [hz]
    simp [compactClMono, hi]

/-- The unique scalar is read directly at the unbounded diagonal code. -/
theorem compactClHodge_coefficient_exact
    (p : Nat) (φ : CompactClRing)
    (hφ : isCompactClHodge p φ) :
    φ = (φ (compactClCode p)) • compactClMono p := by
  rcases (compactClHodge_rank_one p φ).1 hφ with ⟨z, hz, _⟩
  have hread := congrArg
    (fun ψ : CompactClRing => ψ (compactClCode p)) hz
  have hzread : z = φ (compactClCode p) := by
    simpa [compactClMono] using hread.symm
  simpa [hzread] using hz

/-- Limitless transfer crown: the finite twelve-coordinate theorem survives
as a specialization, while the strongest address classification is now
countable, finitely supported, and valid at every natural weight. -/
theorem transfer_v2_limitless_crown :
    (∀ p : Nat, isCompactClHodge p (compactClMono p))
    ∧ (∀ p : Nat, ∀ φ : CompactClRing,
      isCompactClHodge p φ ↔
        ∃! z : ℤ, φ = z • compactClMono p)
    ∧ (∀ p : Nat, ∀ φ : CompactClRing,
      isCompactClHodge p φ →
        φ = (φ (compactClCode p)) • compactClMono p) := by
  exact ⟨compactClMono_isHodge,
    compactClHodge_rank_one,
    compactClHodge_coefficient_exact⟩

/-- Cosmic integration crown: every limitless transfer generator is the
universal address of the corresponding cosmic Hodge generator. -/
theorem transfer_v2_cosmic_integration_crown :
    ∀ p : Nat,
      compactClCode p =
        GSTUniversalAddressBridge.cosmicAddressEquiv (p, p)
      ∧ compactClMono p =
        GSTUniversalAddressBridge.compactAddressEquiv
          (GSTDimensionFreeHodgeDiagonal.cosmicDiagonalClass p) := by
  intro p
  exact ⟨compactClCode_eq_cosmicAddress p,
    compactClMono_eq_cosmicDiagonalAddress p⟩

#check addr_zero
#check clMono_zero_of_twelve_le
#check clHodge_zero_of_three_le
#check transfer_hodge_iff_all_weights
#check transferred_hodge_all_weights
#check transferred_coefficient_exact
#check transferred_coefficient_unique
#check transferred_zero_sector
#check addr_mixed_cup_iterate
#check transfer_v2_crown
#check compactClCode_eq_cosmicAddress
#check compactClMono_eq_cosmicDiagonalAddress
#check transfer_v2_limitless_crown
#check transfer_v2_cosmic_integration_crown

#print axioms transfer_hodge_iff_all_weights
#print axioms transferred_hodge_all_weights
#print axioms transferred_coefficient_exact
#print axioms transferred_coefficient_unique
#print axioms transfer_v2_crown
#print axioms compactClMono_eq_cosmicDiagonalAddress
#print axioms transfer_v2_cosmic_integration_crown

end GSTTransferBridgeV2