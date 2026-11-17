import CardinalWorlds
import GSTGraphV2OmegaWaveLaw

/-!
# THE MONOLITH BOUNDARY — the terminal identity interface

The source monolith `kyo-oo/erdosternary2` (branch
`sol/kyo-gate-universe-wire`, head `cb29501`) closes its campaign through
the §7.15 TERMINAL IDENTITY: the second-observer input
`four_power_omega_shadow_wave_tailF` and the even-exponent Erdős ternary
statement are ONE object, machine-certified in BOTH directions
(`erdos_even_conjecture_iff_tailF`, zero axioms beyond
`[propext, choice, Quot.sound]`).

This universe deliberately does NOT re-carry the monolith's 18,500-line
campaign machinery.  Instead the terminal objects enter the universe the
same way the Cardinal Worlds postulates do: as NAMED PROPOSITIONS with
their proof status declared.  NO boundary object here is assumed
as an axiom.  Files downstream take them as EXPLICIT HYPOTHESES
(`(hB : erdos_even_conjecture_iff_tailF)`), so the universe stays
self-contained: 0 sorries, 0 custom axioms, with the monolith's results
as inputs, exactly like a proof imports a lemma from a library.

PROOF STATUS (all four, per the source monolith):
  PROVEN — in `kyo-oo/erdosternary2` at the cited sections, with axiom
  profile `[propext, choice, Quot.sound]` (see the monolith's own
  `#print axioms` receipts at its lines 18493–18528).

EXTRACTION NOTE: this file is authored in a sandbox with NO Lean toolchain
(boss override).  It is UNCOMPILED here; the repo's comparator CI is the
verifier of record.
-/

/-! ## §1 The terminal identity, both readings -/

/-- **THE TERMINAL IDENTITY** (boundary object).  The second-observer input
and the even-exponent Erdős ternary statement are one object.  PROVEN in
the source monolith §7.15 (`erdos_even_conjecture_iff_tailF`), both
directions, kernel-checked. -/
def erdos_even_conjecture_iff_tailF : Prop :=
  (∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)
    ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF

/-- **THE CROWN** (boundary object).  The universal theorem with the
terminal content as its single input: every `2^n` from nine onward owns
its ternary digit two.  PROVEN in the source monolith
(`erdos_ternary_2_universal_of_tailF`). -/
def erdos_ternary_2_universal_of_tailF : Prop :=
  ∀ (hTailF : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF)
    (n : Nat), 9 ≤ n → noTernaryTwo (2^n) = false

/-- **THE INFINITE-CONTROLLER CHOKEHOLD** (boundary object).  The main
theorem's verdict, read as a statement about the one infinite GST-V2
control graph: for every exponent from nine onward, the graph shows the
ternary two somewhere in its column.  PROVEN in the source monolith
(`infinite_controller_ternary_two_chokehold`). -/
def infinite_controller_ternary_two_chokehold : Prop :=
  ∀ (hTailF : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF)
    (n : Nat), 9 ≤ n →
    ∃ p : Nat,
      (GSTGraphV2InfiniteControl.graph (1 + n % 2) (n / 2) p).seven.digit
        = 2

/-- **THE ODD-EXPONENT HALF** (boundary object).  Every odd exponent from
nine onward owns its ternary digit two.  PROVEN in the source monolith
(`erdos_ternary_2_conjecture_odd`, delegating to the green odd-case
machinery `erdos_ternary_2_odd_universal`). -/
def erdos_ternary_2_conjecture_odd : Prop :=
  ∀ n : Nat, 9 ≤ n → n % 2 = 1 → noTernaryTwo (2^n) = false

/-! ## §2 Adapters — what the boundary hands the universe immediately -/

/-- The boundary identity is symmetric: the tail-input reading of the
terminal content, extracted directly from the identity. -/
theorem erdos_even_conjecture_of_tailF_boundary
    (hB : erdos_even_conjecture_iff_tailF)
    (hTailF : GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  hB.mpr hTailF

/-! ## §3 Receipts -/

#check erdos_even_conjecture_iff_tailF
#check erdos_ternary_2_universal_of_tailF
#check infinite_controller_ternary_two_chokehold
#check erdos_ternary_2_conjecture_odd
