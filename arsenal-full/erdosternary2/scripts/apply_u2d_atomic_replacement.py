#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

for stale in (
    'import GSTHandwrittenPhaseIncidence\n',
    'import GSTSpacetimeV2\n',
):
    s = s.replace(stale, '', 1)

imp = 'import GSTGraphV2InfiniteControl\n'
if imp not in s:
    anchor = 'import Mathlib.Tactic.Ring\n'
    if anchor not in s:
        raise SystemExit('import anchor not found')
    s = s.replace(anchor, anchor + imp, 1)

start_marker = '/-- Literal BIG-N finite-support horizon for the canonical child information. -/'
end_marker = '/-- The two consecutive power waves overlap at a Happy Gate.'
installed_marker = '-- SOL56 U2D ATOMIC PREFIX-ONE CLOSURE'
creation_marker = 'theorem gst_four_power_creation_certificate_inline'

if start_marker not in s:
    if installed_marker in s and 'theorem gst_prefix_one_u2d_atomic_collision_inline' in s:
        print('atomic U2D replacement already installed')
        p.write_text(s, encoding='utf-8')
        raise SystemExit(0)
    raise SystemExit('old prefix-one start marker not found')
if end_marker not in s:
    raise SystemExit('prefix-one end marker not found')
if creation_marker not in s:
    raise SystemExit('existing production gst_four_power_creation_certificate_inline declaration not found')

start = s.index(start_marker)
end = s.index(end_marker, start)
creation_start = s.index(creation_marker)
creation_decl = ''
creation_position = 'before'
if creation_start >= start:
    try:
        creation_end = s.index('\n/--', creation_start)
    except ValueError as exc:
        raise SystemExit('could not locate end of gst_four_power_creation_certificate_inline declaration') from exc
    creation_decl = s[creation_start:creation_end].rstrip() + '\n\n'
    if creation_decl.count(creation_marker) != 1:
        raise SystemExit('production gst_four_power_creation_certificate_inline extraction multiplicity changed')
    if creation_start < end:
        creation_position = 'inside'
        # The normal seam replacement removes the original copy.
    else:
        creation_position = 'after'
        # Move the existing declaration before the new helper so Lean sees it
        # first, and remove its later original to preserve exact multiplicity.
        s = s[:creation_start] + s[creation_end:]

replacement = creation_decl + r'''/-- Kernel adapter for the already-proved universal creation certificate.
The carry-one branch is advanced by one exact GST carry edge. -/
theorem gst_h_creation_full_power_navigation_atomic
    (k : Nat) (hk5 : 5 ≤ k) (hk7 : k ≠ 7) :
    GSTNavigationWitness (4^k) := by
  obtain ⟨p, hp1, hd, hcase⟩ := gst_four_power_creation_certificate_inline k hk5 hk7
  have hClt : gstCarry (4^k) p < 4 := gstCarry_lt_four _ _ hp1
  rcases hcase with hmod0 | hmod1
  · have hCmod : gstCarry (4^k) p % 3 = 0 := by
      simpa [gstCarry] using hmod0
    have hC : gstCarry (4^k) p = 0 ∨ gstCarry (4^k) p = 3 := by
      omega
    rcases hC with h0 | h3
    · exact gstNavigationWitness_of_digit_carry_zero (4^k) p hd h0
    · exact gstNavigationWitness_of_digit_carry_three (4^k) p hd h3
  · have hCmod : gstCarry (4^k) p % 3 = 1 := by
      simpa [gstCarry] using hmod1.1
    have hC : gstCarry (4^k) p = 1 := by omega
    have hnext := gstCarry_forward_exact (4^k) p hp1
    rw [hC, hd] at hnext
    norm_num [gstStepCarry] at hnext
    have hdnext : gstDigit (4^k) (p+1) = 2 := by
      simpa [gstDigit] using hmod1.2
    exact gstNavigationWitness_of_digit_carry_three (4^k) (p+1) hdnext hnext

/-- Inverse of the forced `s+1` prefix shift. -/
theorem gst_full_power_navigation_descends_atomic
    (s b : Nat) (hs : 1 ≤ s) (hb : 1 ≤ b) (hb3 : b % 3 ≠ 0)
    (hfull : GSTNavigationWitness (4^(3^s * b))) :
    GSTNavigationWitness (gstNavigationConstant s b) := by
  obtain ⟨p, hd, hspace⟩ := hfull
  have hpge : s + 1 ≤ p := by
    by_contra hnot
    have hplt : p < s + 1 := by omega
    have hdecomp := gst_navigation_decomposition s b hs
    have hbiggt : 1 < 3^(s+1) := by
      have h9 : 9 ≤ 3^(s+1) := by
        simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
          (show 2 ≤ s+1 by omega))
      omega
    have hRmodBig : 4^(3^s * b) % 3^(s+1) = 1 := by
      rw [hdecomp, Nat.add_mod]
      have hmul :
          (3^(s+1) * gstNavigationConstant s b) % 3^(s+1) = 0 :=
        Nat.mod_eq_zero_of_dvd ⟨gstNavigationConstant s b, rfl⟩
      rw [hmul, Nat.add_zero]
      simp [Nat.mod_eq_of_lt hbiggt]
    have hdvd : 3^(p+1) ∣ 3^(s+1) :=
      Nat.pow_dvd_pow 3 (by omega)
    have hsmallgt : 1 < 3^(p+1) := by
      have h3 : 3 ≤ 3^(p+1) := by
        simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
          (show 1 ≤ p+1 by omega))
      omega
    have hm := Nat.mod_mod_of_dvd (4^(3^s * b)) hdvd
    rw [hRmodBig, Nat.mod_eq_of_lt hsmallgt] at hm
    have hRmodSmall : 4^(3^s * b) % 3^(p+1) = 1 := hm.symm
    have hdi := digit_identity (4^(3^s * b)) p
    rw [hRmodSmall] at hdi
    change 4^(3^s * b) / 3^p % 3 = 2 at hd
    by_cases hp0 : p = 0
    · subst p
      norm_num at hdi hd
      omega
    · have hp1 : 1 ≤ p := by omega
      have h3p : 3 ≤ 3^p := by
        simpa using (Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) hp1)
      have hdiv0 : 1 / 3^p = 0 := Nat.div_eq_of_lt (by omega)
      rw [hdiv0] at hdi
      norm_num at hdi
      omega
  let j := p - (s+1)
  have hpEq : p = s + 1 + j := by
    dsimp [j]
    omega
  refine ⟨j, ?_⟩
  apply (gst_navigation_position_universal s b j hs hb hb3).1
  rw [← hpEq]
  exact ⟨hd, hspace⟩

-- SOL56 U2D ATOMIC PREFIX-ONE CLOSURE
/-- Atomic GST Graph V2 event collision. -/
theorem gst_prefix_one_u2d_atomic_collision_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (_hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  let E : Nat := 4^(3^(s+1) * n)
  let N : Nat := 3^s
  let B : Nat := 3^(s+2)
  let P1 : Nat := 1 + 3^(s+1)
  let H : Nat := gstPrefixOneUPotentialTailS s n
  have hc3 : c s % 3 = 1 := c_mod3 s hs
  have hcshape : c s = 1 + 3 * (c s / 3) := by
    have hcdiv := Nat.mod_add_div (c s) 3
    rw [hc3] at hcdiv
    omega
  have hA : 4^(3^s) = 1 + 3^(s+1) * c s := lte_identity s hs
  have hE1raw := gst_canonical_phase1_energy_shape_surgeryS
    gstNavigationConstant gst_navigation_constant_origin_energyS
    s n (c s) (c s / 3) hs hA hcshape
  have hE1 : 4^N * E = P1 + B*H := by
    dsimp [N, E, P1, B, H, gstPrefixOneUPotentialTailS]
    rw [show 3^(s+2) = 3 * 3^(s+1) by
      rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]; ac_rfl]
    simpa [Nat.mul_assoc] using hE1raw
  let X : Nat := 3^(s+1)
  have hX9 : 9 ≤ X := by
    dsimp [X]
    have hpow : 3^2 ≤ 3^(s+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at hpow ⊢
    exact hpow
  have hBshape : B = 3 * X := by
    dsimp [B, X]
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    ac_rfl
  have hP1shape : P1 = 1 + X := by rfl
  have hP1 : P1 < B := by rw [hBshape, hP1shape]; omega
  have hP1lo : B ≤ 4 * P1 := by rw [hBshape, hP1shape]; omega
  have hP1hi : 4 * P1 < 2 * B := by rw [hBshape, hP1shape]; omega
  have hBpos : 0 < B := by omega
  have hseed1lo : 1 ≤ (4 * P1) / B :=
    (Nat.le_div_iff_mul_le hBpos).2 (by simpa using hP1lo)
  have hseed1hi : (4 * P1) / B < 2 :=
    (Nat.div_lt_iff_lt_mul hBpos).2 (by simpa using hP1hi)
  have hseed1 : (4 * P1) / B = 1 := by omega
  have hseeded := gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad
  have hRightBad : ∀ j,
      ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph E N (s+2+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph E N (s+2+j)).seven.digit := by
    intro j hHappy
    have hTail :=
      (GSTGraphV2InfiniteControl.graph_prefix_slice_happy_iff
        E N (s+2) P1 H j hE1 hP1).1 hHappy
    rw [hseed1] at hTail
    have hbadj := hseeded j
    apply hbadj
    simpa [GSTBadPairS, GSTCanonicalSevenAxisBridge.digit3,
      GSTGraphV2InfiniteControl.seededCarry,
      gstAffineMulCarryS, gstDigitS] using hTail
  let K : Nat := 3^s * (1 + 3*n)
  have h3pow : 3 ≤ 3^s := by
    have h := Nat.pow_le_pow_of_le (by decide : 1 < 3) hs
    norm_num at h ⊢
    exact h
  have harg4 : 4 ≤ 1 + 3*n := by omega
  have hK12 : 12 ≤ K := by dsimp [K]; nlinarith
  have hfull : GSTNavigationWitness (4^K) :=
    gst_h_creation_full_power_navigation_atomic K (by omega) (by omega)
  have hb3 : (1 + 3*n) % 3 ≠ 0 := by simp [Nat.add_mod, Nat.mul_mod]
  have hParent :
      GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) :=
    gst_full_power_navigation_descends_atomic
      s (1 + 3*n) hs (by omega) hb3 (by simpa [K] using hfull)
  obtain ⟨r, hdr, hspaceR⟩ := hParent
  have hrpos : 1 ≤ r := by
    by_contra hnot
    have hr0 : r = 0 := by omega
    subst r
    have hmodParent : gstNavigationConstant s (1 + 3*n) % 3 = 1 := by
      have hm := gstNavigationConstant_mod3 s (1 + 3*n) hs (by omega) hb3
      simpa [Nat.add_mod, Nat.mul_mod] using hm
    simp [gstDigit, hmodParent] at hdr
  have hCmodR : gstCarry (gstNavigationConstant s (1 + 3*n)) r % 3 = 0 :=
    gstGoodSpace_carry_mod3_zero _ _ hspaceR
  have hCltR : gstCarry (gstNavigationConstant s (1 + 3*n)) r < 4 :=
    gstCarry_lt_four _ r hrpos
  have hCR :
      gstCarry (gstNavigationConstant s (1 + 3*n)) r = 0 ∨
      gstCarry (gstNavigationConstant s (1 + 3*n)) r = 3 := by
    omega
  let j : Nat := r - 1
  have hrEq : r = 1 + j := by dsimp [j]; omega
  rw [hrEq] at hdr hCR
  have hstate := gst_prefix_one_product_state s n j hs
  have hdH : gstDigit H j = 2 := by
    dsimp [H, gstPrefixOneUPotentialTailS]
    exact hstate.1.symm.trans hdr
  have hCH :
      gstAffineMulCarry 4 1 H j = 0 ∨
      gstAffineMulCarry 4 1 H j = 3 := by
    dsimp [H, gstPrefixOneUPotentialTailS]
    rcases hCR with h0 | h3
    · exact Or.inl (hstate.2.symm.trans h0)
    · exact Or.inr (hstate.2.symm.trans h3)
  have hRight :
      GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph E N (s+2+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph E N (s+2+j)).seven.digit := by
    apply (GSTGraphV2InfiniteControl.graph_prefix_slice_happy_iff
      E N (s+2) P1 H j hE1 hP1).2
    rw [hseed1]
    constructor
    · simpa [GSTCanonicalSevenAxisBridge.digit3, gstDigit] using hdH
    · simpa [GSTGraphV2InfiniteControl.seededCarry, gstAffineMulCarry] using hCH
  exact hRightBad j hRight

/-- Mechanical target splice. -/
theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild
  exact gst_prefix_one_u2d_atomic_collision_inline s n hs hn hchild hBad

/-- Public prefix-one lift consumes only the exact Graph-V2 event collision. -/
theorem gst_prefix_one_navigation_lift : GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  by_contra hnoParent
  have hBad : GSTOmegaInfiniteBadTrace s 1 n :=
    gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
  exact gst_prefix_one_u2d_atomic_collision_inline s n hs hn hchild hBad

#print axioms hCreationCheck_univ
#print axioms gst_four_power_creation_certificate_inline
#print axioms gst_h_creation_full_power_navigation_atomic
#print axioms gst_full_power_navigation_descends_atomic
#print axioms gst_prefix_one_u2d_atomic_collision_inline
#print axioms gst_prefix_one_information_bad_descends_inline
#print axioms gst_prefix_one_navigation_lift

'''

s = s[:start] + replacement + s[end:]
old_ring = 'convert hshared using 1 <;> ring'
ring_count = s.count(old_ring)
if ring_count != 1:
    raise SystemExit(f'expected exactly one localized ring scar, found {ring_count}')
s = s.replace(old_ring, 'convert hshared using 1 <;> ring_nf', 1)

for required in (
    'theorem gst_four_power_creation_certificate_inline',
    'theorem gst_h_creation_full_power_navigation_atomic',
    'theorem gst_full_power_navigation_descends_atomic',
    'theorem gst_prefix_one_u2d_atomic_collision_inline',
    'theorem gst_prefix_one_information_bad_descends_inline',
):
    if s.count(required) != 1:
        raise SystemExit(f'expected exactly one installed declaration: {required}')
helper_start = s.index('theorem gst_prefix_one_u2d_atomic_collision_inline')
helper_end = s.index('theorem gst_prefix_one_navigation_lift', helper_start)
if 'gst_residual_navigation_lift' in s[helper_start:helper_end]:
    raise SystemExit('quarantined residual navigation lift survived U2D replacement block')
if 'trace_state\n  contradiction' in s:
    raise SystemExit('old RED seam survived U2D replacement')

p.write_text(s, encoding='utf-8')
print(f'PRODUCTION_H_CREATION_POSITION={creation_position}')
print('PRODUCTION_H_CREATION_PRESERVED=1')
print('U2D_ATOMIC_COLLISION_RESTORED=1')
print('PREFIX_ONE_INFORMATION_WRAPPER_INSTALLED=1')
print('LIVE_RESIDUAL_NAVIGATION_LIFT_DEPENDENCY=0')
print('forward mechanical RC2 fixes installed')
