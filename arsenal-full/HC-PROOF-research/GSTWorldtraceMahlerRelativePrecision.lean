import MonolithBoundary
import GSTGhostRayExclusion
import GSTClimbInfiniteFamily
import GSTTheAct

namespace GSTWorldtraceMahler

set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

/-!
# WORLDTRACE–MAHLER RELATIVE-PRECISION THEORY

This file is the production replacement for the former two terminal
interfaces in `GSTGhostRayExclusion`: one exact moving-precision
Worldtrace arithmetic theory object and its crown.

The internal witness is

  W_s(u) =
    2u(4^(3^s)-1) - (6 A(u)-27)3^s,

where A(u) = (c_1 u) mod 9.

The correct 3-adic precision is relative to the visible factor 3^s:
a rational lock means divisibility by 3^(s+q) for every target q,
eventually in s.
-/

/-- The canonical low Worldtrace head of a three-free core. -/
def worldtraceHead (u : Nat) : Nat :=
  (GSTTowerFire.c 1 * u) % 9

/-- The pure-integer Worldtrace/Mahler witness. -/
def worldtraceWitness (u s : Nat) : ℤ :=
  2 * (u : ℤ) * ((4 : ℤ)^(3^s) - 1)
    - (6 * (worldtraceHead u : ℤ) - 27) * (3 : ℤ)^s

/-- The correct moving-precision rational lock.  The exponent `s+q`
removes the automatic baseline factor `3^s` and asks for `q`
additional 3-adic digits of precision. -/
def RelativeLock (u : Nat) : Prop :=
  ∀ q : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
    (3 : ℤ)^(s+q) ∣ worldtraceWitness u s

/-- The corrected pure-integer Mahler input.  No admissible rational
candidate can receive arbitrary precision *above* the baseline `3^s`. -/
def MahlerSharp : Prop :=
  ¬ ∃ (a u : Nat), (a < 9 ∧ ¬ 3 ∣ a) ∧ (¬ 3 ∣ u) ∧
    ∀ q : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3 : ℤ)^(s+q) ∣
        (2 * (u : ℤ) * ((4 : ℤ)^(3^s) - 1)
          - (6 * (a : ℤ) - 27) * (3 : ℤ)^s)

/-- The corrected residual version of the old ghost compression:
the finite kernel has already paid every exponent through 500. -/
def ResidualGhostCompression : Prop :=
  ∀ (K sigma u : Nat), 500 < K → K = 3^sigma * u → ¬ 3 ∣ u →
    GSTClimbInfiniteFamily.CantorianPower K → GSTGhostRay.GhostRay u

/-- The exact Worldtrace-arithmetic compression consumed by Mahler.
It is weaker than demanding the entire ghost geometry. -/
def WorldtraceScaledCompression : Prop :=
  ∀ (K sigma u : Nat), 500 < K → K = 3^sigma * u → ¬ 3 ∣ u →
    GSTClimbInfiniteFamily.CantorianPower K → RelativeLock u

/-- One combined theory object: the external Mahler fracture and the
internal Worldtrace relative-precision compression. -/
structure WorldtraceMahlerTheory : Prop where
  mahler : MahlerSharp
  compression : WorldtraceScaledCompression

/-- The witness has an automatic factor `3^(s+1)`.  This identity is
why fixed-modulus convergence was the wrong terminal encoding. -/
theorem worldtraceWitness_factor (u s : Nat) :
    worldtraceWitness u s =
      (3 : ℤ)^(s+1) *
        (2 * (u : ℤ) * (GSTTowerFire.c s : ℤ)
          - 2 * (worldtraceHead u : ℤ) + 9) := by
  have h4 : (4 : ℤ)^(3^s)
      = 1 + (3 : ℤ)^(s+1) * (GSTTowerFire.c s : ℤ) := by
    exact_mod_cast GSTTowerFire.four_pow_three_pow_eq s
  unfold worldtraceWitness
  rw [h4, pow_succ]
  ring

/-- The baseline divisibility is automatic, for every core and every
depth; meaningful convergence must therefore ask for precision above it. -/
theorem worldtraceWitness_baseline (u s : Nat) :
    (3 : ℤ)^(s+1) ∣ worldtraceWitness u s := by
  rw [worldtraceWitness_factor]
  exact ⟨2 * (u : ℤ) * (GSTTowerFire.c s : ℤ)
    - 2 * (worldtraceHead u : ℤ) + 9, rfl⟩

/-- The existing ghost theorem is strictly stronger than the new
terminal interface: its quadratic-depth witness gives every requested
relative precision. -/
theorem ghost_implies_relative_lock (u : Nat)
    (hg : GSTGhostRay.GhostRay u) : RelativeLock u := by
  intro q
  refine ⟨max 2 q, ?_⟩
  intro s hs
  obtain ⟨m, hm⟩ := GSTGhostRay.ghost_witness u hg s (by omega)
  have hpow : (3 : ℤ)^(s+q) ∣ (3 : ℤ)^(2*s+2) :=
    pow_dvd_pow 3 (by omega)
  exact hpow.trans ⟨m, hm⟩

/-- Any correctly residualized version of the older ghost compression
immediately yields the weaker, arithmetic-only scaled compression. -/
theorem scaled_compression_of_residual_ghost
    (H : ResidualGhostCompression) : WorldtraceScaledCompression := by
  intro K sigma u hK hKu hu hCant
  exact ghost_implies_relative_lock u (H K sigma u hK hKu hu hCant)

/-- A three-free core's canonical head is an admissible Mahler head. -/
theorem worldtraceHead_admissible (u : Nat) (hu : ¬ 3 ∣ u) :
    worldtraceHead u < 9 ∧ ¬ 3 ∣ worldtraceHead u := by
  constructor
  · unfold worldtraceHead
    exact Nat.mod_lt _ (by decide)
  · simpa [worldtraceHead] using GSTGhostRay.ghost_head_unit u hu

/-- MahlerSharp excludes the relative lock of every three-free natural core. -/
theorem mahler_excludes_relative_lock
    (H : MahlerSharp) (u : Nat) (hu : ¬ 3 ∣ u) :
    ¬ RelativeLock u := by
  intro hlock
  apply H
  refine ⟨worldtraceHead u, u, worldtraceHead_admissible u hu, hu, ?_⟩
  simpa [RelativeLock, worldtraceWitness] using hlock

/-- The Mahler fracture in finite divisibility language: every three-free
core has one relative precision that fails arbitrarily far out. -/
theorem worldtrace_mahler_fracture
    (H : MahlerSharp) (u : Nat) (hu : ¬ 3 ∣ u) :
    ∃ q : Nat, ∀ S : Nat, ∃ s : Nat, S ≤ s ∧
      ¬ ((3 : ℤ)^(s+q) ∣ worldtraceWitness u s) := by
  have h := mahler_excludes_relative_lock H u hu
  unfold RelativeLock at h
  push_neg at h
  exact h

/-- The fracture cannot occur at relative precision zero or one because
the baseline factor is always present. -/
theorem worldtrace_mahler_fracture_ge_two
    (H : MahlerSharp) (u : Nat) (hu : ¬ 3 ∣ u) :
    ∃ q : Nat, 2 ≤ q ∧ ∀ S : Nat, ∃ s : Nat, S ≤ s ∧
      ¬ ((3 : ℤ)^(s+q) ∣ worldtraceWitness u s) := by
  obtain ⟨q, hq⟩ := worldtrace_mahler_fracture H u hu
  have hq2 : 2 ≤ q := by
    by_contra hnot
    have hqle : q ≤ 1 := by omega
    obtain ⟨s, _hs, hfail⟩ := hq 0
    apply hfail
    have hd : (3 : ℤ)^(s+q) ∣ (3 : ℤ)^(s+1) :=
      pow_dvd_pow 3 (by omega)
    exact hd.trans (worldtraceWitness_baseline u s)
  exact ⟨q, hq2, hq⟩

/-- **WORLDTRACE CORE-SPECTRUM DICHOTOMY.**
Every natural core is either visibly three-divisible, or else its Mahler
witness fractures at some genuinely super-baseline precision q ≥ 2
arbitrarily far out.  This removes the three-free premise from the outer
statement and makes the fracture a total classification of cores. -/
theorem worldtrace_mahler_core_spectrum
    (H : MahlerSharp) (u : Nat) :
    3 ∣ u ∨
      ∃ q : Nat, 2 ≤ q ∧
        ∀ S : Nat, ∃ s : Nat, S ≤ s ∧
          ¬ ((3 : ℤ)^(s+q) ∣ worldtraceWitness u s) := by
  by_cases hu : 3 ∣ u
  · exact Or.inl hu
  · exact Or.inr (worldtrace_mahler_fracture_ge_two H u hu)

/-- The intrinsic output of the Worldtrace/Mahler theory, before any external
Erdős boundary interface is attached. -/
structure WorldtraceMahlerSpectrum : Prop where
  coreSpectrum :
    ∀ u : Nat,
      3 ∣ u ∨
        ∃ q : Nat, 2 ≤ q ∧
          ∀ S : Nat, ∃ s : Nat, S ≤ s ∧
            ¬ ((3 : ℤ)^(s+q) ∣ worldtraceWitness u s)
  extinctionAboveKernel :
    ∀ K : Nat, 500 < K →
      ¬ GSTClimbInfiniteFamily.CantorianPower K

/-- THE EXTINCTION THEOREM ABOVE THE KERNEL BASE.  Scaled compression
forces a lock; Mahler forces a fracture of that same integer witness. -/
theorem worldtrace_mahler_extinction
    (H : MahlerSharp) (HC : WorldtraceScaledCompression) :
    ∀ K : Nat, 500 < K → ¬ GSTClimbInfiniteFamily.CantorianPower K := by
  intro K hK hCant
  obtain ⟨sigma, u, hKu, hu⟩ :=
    GSTGhostRay.exists_three_free_decomp K K (by omega) (by omega)
  have hlock : RelativeLock u := HC K sigma u hK hKu hu hCant
  exact (mahler_excludes_relative_lock H u hu) hlock

/-- Every Worldtrace/Mahler theory canonically determines its complete
internal spectrum: universal core fracture plus Cantorian extinction above
the finite kernel. -/
theorem WorldtraceMahlerTheory.toSpectrum
    (T : WorldtraceMahlerTheory) :
    WorldtraceMahlerSpectrum := by
  exact ⟨
    worldtrace_mahler_core_spectrum T.mahler,
    worldtrace_mahler_extinction T.mahler T.compression⟩

/-- The finite kernel plus extinction removes every Cantorian exponent
from the actual theorem range K >= 8. -/
theorem worldtrace_mahler_no_cantorian
    (H : MahlerSharp) (HC : WorldtraceScaledCompression) :
    ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K := by
  rintro ⟨K, hK8, hCant⟩
  by_cases h500 : K ≤ 500
  · have htwo : hasTernaryTwo (4^K) = true :=
      modular_check_base K (by omega) h500
    have hfalse : noTernaryTwo (4^K) = false :=
      has_two_imp_not_no_two (4^K) htwo
    have htrue : noTernaryTwo (4^K) = true :=
      GSTClimbInfiniteFamily.cantorian_no_two K hCant
    rw [htrue] at hfalse
    contradiction
  · exact worldtrace_mahler_extinction H HC K (by omega) hCant

/-- The exponent-axis witness form, exported through the monolith's
terminal observable. -/
theorem worldtrace_mahler_kill_all
    (H : MahlerSharp) (HC : WorldtraceScaledCompression) :
    ∀ K : Nat, 8 ≤ K → ∃ p : Nat,
      GSTCanonicalSevenAxisBridge.digit3 (4^K) p = 2 := by
  have hnc := worldtrace_mahler_no_cantorian H HC
  have hAct : GSTTheAct.the_act :=
    GSTClimbInfiniteFamily.the_act_iff_no_cantorian.mpr hnc
  intro K hK
  obtain ⟨p, hp⟩ := omega_shadow_kill_all_of_even_conjecture hAct K hK
  exact ⟨p, hp⟩

/-- The strengthened crown records all terminal faces at once. -/
structure WorldtraceMahlerCrown : Prop where
  noCantorian :
    ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K
  killAll :
    ∀ K : Nat, 8 ≤ K → ∃ p : Nat,
      GSTCanonicalSevenAxisBridge.digit3 (4^K) p = 2
  theAct : GSTTheAct.the_act
  tailF : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF
  fullErdos :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false
  controller :
    ∀ n : Nat, 9 ≤ n → ∃ p : Nat,
      (GSTGraphV2InfiniteControl.graph (1 + n % 2) (n / 2) p).seven.digit = 2

/-- THE NEW CROWN.  One theory object yields Cantorian extinction,
explicit digit witnesses, the act, tailF, the full theorem, and the
infinite-controller digit-two cell. -/
theorem worldtrace_mahler_relative_precision_crown
    (hB : infinite_controller_ternary_two_chokehold)
    (hBIff : erdos_even_conjecture_iff_tailF)
    (hOdd : erdos_ternary_2_conjecture_odd)
    (T : WorldtraceMahlerTheory) : WorldtraceMahlerCrown := by
  have hnc : ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K :=
    worldtrace_mahler_no_cantorian T.mahler T.compression
  have hAct : GSTTheAct.the_act :=
    GSTClimbInfiniteFamily.the_act_iff_no_cantorian.mpr hnc
  have hTail : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
    (GSTTheAct.the_act_iff_hTailF hBIff).mp hAct
  refine ⟨hnc, worldtrace_mahler_kill_all T.mahler T.compression,
    hAct, hTail, GSTTheAct.full_erdos_of_the_act hOdd hAct, ?_⟩
  intro n hn
  exact hB hTail n hn

/-- Direct crown from the corrected ghost-geometric interface:
residual ghost compression is converted internally to scaled arithmetic
compression before the Mahler collision. -/
theorem worldtrace_mahler_crown_of_residual_ghost
    (hB : infinite_controller_ternary_two_chokehold)
    (hBIff : erdos_even_conjecture_iff_tailF)
    (hOdd : erdos_ternary_2_conjecture_odd)
    (H : MahlerSharp) (HC : ResidualGhostCompression) :
    WorldtraceMahlerCrown :=
  worldtrace_mahler_relative_precision_crown hB hBIff hOdd
    ⟨H, scaled_compression_of_residual_ghost HC⟩

#print axioms worldtrace_mahler_crown_of_residual_ghost

#print axioms worldtraceWitness_factor
#print axioms ghost_implies_relative_lock
#print axioms mahler_excludes_relative_lock
#print axioms worldtrace_mahler_fracture_ge_two
#print axioms worldtrace_mahler_core_spectrum
#print axioms WorldtraceMahlerTheory.toSpectrum
#print axioms worldtrace_mahler_extinction
#print axioms worldtrace_mahler_relative_precision_crown

end GSTWorldtraceMahler
