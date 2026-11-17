import Mathlib

/-!
# GST WEIL-FORCING FRAME CERTIFICATE (Cycle 2)

Lean shadow of the derivation
`research/derivations/GST_weil_forcing_frame_end_signature_and_input_stratification_2026_10_25.tex`
and the record
`research/records/2026-10-25-gst-weil-forcing-frame-end-signature-and-input-stratification.md`.

## What is certified here (all statements are exact finite algebra)

Part A — THE WEIL PROJECTOR CORRESPONDENCE ALGEBRA.
For the discriminating Weil fourfold A with the isogeny f = [2+i], the spectral projector onto the
rational Weil plane is P_W(t) = -((t-25)(39t-79)(t^2-30t+625))/44000000. We certify:

1. The expanded numerator pwN t = -39 t^4 + 2224 t^3 - 57970 t^2 + 718000 t - 1234375,
   hence the CORRESPONDENCE COEFFICIENTS a_j (the rational coefficients of the transpose-graph
   algebraic correspondence Pi_W^CH = sum_j a_j * Γ_{f^j}):
   a_0 = -79/2816, a_1 = 359/22000, a_2 = -527/400000, a_3 = 139/2750000, a_4 = -39/44000000.
2. The key identity  pwN t + (t^2+14t+625)(39t^2-2770t+72375) = 44000000.
3. The spectral evaluations: P_W = 1 on the Weil factor (t^2+14t+625 = 0),
   P_W = 0 on the mixed factor (t^2-30t+625 = 0), P_W(25) = 0 on the ambient factor.

Part B — THE EXTERIOR SIGN-COUNT CERTIFICATE FOR INT W_R^2 = 8.
W_R = Re(Omega), Omega = wedge_{j=1..4}(e_j + i f_j), has eight ±1 monomial components
(DATA from the exterior algebra; the expansion and the vanishing of the 56 non-complementary
ordered products are elementary and proved in the derivation .tex). Each surviving ordered
complementary pair contributes s_i * s_j * invsign(l_i ++ l_j), where invsign is the parity sign
of the concatenated index list. We certify, by full evaluation (`decide`), that the eight
contributions sum to exactly 8:  INT W_R^2 = 8  (equivalently W_R^2 = 8 vol as a class).

Part C — THE END-MASS ARITHMETIC (corrected sign; audit finding F2 of 2026-10-25).
The duality sign on Chern characters is PER GRADE: ch(E^vee) = r + (-1)^p m alpha, so at even p the dual
character coincides with the original; at p = 2, ch(End E) = r^2 + 2rm alpha + m^2 alpha^2 (three grades).
Given the declared geometric inputs as HYPOTHESES (Riemann--Roch on the abelian fourfold with td = 1 and the
certified pairing; Serre duality h3 = h1, h4 = h0), the Euler signature
chi(End F) = +(m^2) * 8 > 0 for every scale m ≠ 0, and the End-mass identity
h0 + h2/2 = h1 + 4 m^2 >= 4 m^2 holds. The End-mass no-go: h1 >= 0, m >= 1 force
h0 + h2/2 >= 4, and for simple realizations (h0 = 1) this forces h2 >= 8 m^2 - 2 (>= 6 at m = 1):
any birth law producing carriers with bounded even-End-cohomology mass cannot realize the forcing input
at all scales on the discriminator. No claim is made about rigidity (the corrected identity permits
h1 = 0 with the mass carried by h2).

## Context (commentary; NOT certified in this file)

Scheme-level statements live OUTSIDE this file's certified scope and are proved in the
derivation .tex with declared external leaves: the geometric identification of the Weil plane
with Q[t]/(t^2+14t+625) and of S with the projected Chow image; the correspondence-action
compatibility (external leaf E1); the reduction of the dichotomy S = 0 or S = W_Q to the
kernel-verified theorem cmWeilStableSourceDichotomy in GSTUniversalCMArithmeticObstruction.lean
(already kernel-verified green; not duplicated here); the one-source reconstruction of explicit
cycles; GAGA; the two-center descent law application; Hirzebruch--Riemann--Roch; Serre
duality; the Kunneth unimodularity of the torus K-lattice and the derived minimal scale m0 = 1.
The monomial sign table in Part B is DATA supplied by the exterior algebra (each entry is
independently checkable by hand; the file verifies the complete numerical content of the
period identity). No sorry, no custom axioms, no native_decide.
-/

set_option maxHeartbeats 400000

/-! ## Part A: the projector correspondence algebra -/

/-- Numerator of the Weil projector polynomial: pwN t = -((t-25)(39t-79)(t^2-30t+625)). -/
def pwN (t : ℚ) : ℚ := -(t-25)*(39*t-79)*(t^2-30*t+625)

/-- The denominator 44 000 000. -/
def cdenom : ℚ := 44000000

/-- The Weil projector P_W(t) = pwN t / 44000000. -/
def pw (t : ℚ) : ℚ := pwN t / cdenom

theorem cdenom_ne : cdenom ≠ 0 := by decide

/-- Expanded numerator: the correspondence coefficient table. -/
theorem pwN_expansion (t : ℚ) :
    pwN t = -39*t^4 + 2224*t^3 - 57970*t^2 + 718000*t - 1234375 := by
  unfold pwN; ring

/-- The correspondence coefficients a_j of Pi_W^CH = sum_j a_j Γ_{f^j}. -/
theorem pw_correspondence_coeffs (t : ℚ) :
    pw t = -(39:ℚ)/44000000 * t^4 + (139:ℚ)/2750000 * t^3 - (527:ℚ)/400000 * t^2
      + (359:ℚ)/22000 * t - (79:ℚ)/2816 := by
  have hD1 : (44000000:ℚ) ≠ 0 := by decide
  have hD2 : (2750000:ℚ) ≠ 0 := by decide
  have hD3 : (400000:ℚ) ≠ 0 := by decide
  have hD4 : (22000:ℚ) ≠ 0 := by decide
  have hD5 : (2816:ℚ) ≠ 0 := by decide
  unfold pw cdenom pwN
  field_simp
  ring

/-- Key identity: pwN t + G_W(t) * M(t) = 44000000. -/
theorem pwN_key_identity (t : ℚ) :
    pwN t + (t^2+14*t+625)*(39*t^2-2770*t+72375) = 44000000 := by
  unfold pwN; ring

/-- P_W restricts to the identity on the Weil primary factor. -/
theorem pw_fixes_weil {t : ℚ} (h : t^2+14*t+625 = 0) : pw t = 1 := by
  have hkey := pwN_key_identity t
  rw [h, zero_mul, add_zero] at hkey
  unfold pw cdenom
  rw [hkey]
  norm_num

/-- P_W kills the mixed primary factor. -/
theorem pw_kills_mixed {t : ℚ} (h : t^2-30*t+625 = 0) : pw t = 0 := by
  unfold pw cdenom pwN
  rw [h, mul_zero, zero_div]

/-- P_W kills the ambient (t-25) factor. -/
theorem pw_kills_ambient : pw 25 = 0 := by
  unfold pw cdenom pwN
  norm_num

/-! ## Part B: the exterior sign-count certificate INT W_R^2 = 8 -/

/-- Number of entries of `l` strictly smaller than `a`. -/
def countGreater (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: bs => (if a > b then 1 else 0) + countGreater a bs

/-- Number of inversions of a list (its parity gives the wedge reordering sign). -/
def inversions : List ℕ → ℕ
  | [] => 0
  | a :: as => countGreater a as + inversions as

/-- Sign of the reordering of a list to canonical order: +1 if even, -1 if odd. -/
def invsign (l : List ℕ) : ℤ := if inversions l % 2 = 0 then 1 else -1

/-! The eight monomial components of W_R (indices 0..7 encode e1..e4,f1..f4) with their
signs, and their eight surviving ordered complementary-pair products. Each product is
s_i * s_j * invsign (l_i ++ l_j); the 56 non-complementary ordered products vanish by
repeated generators (exterior algebra; see the derivation .tex). -/

theorem weil_WR_square_top_certificate :
    ( (1:ℤ) * 1 * invsign ([0,1,2,3] ++ [4,5,6,7]))
  + ((-1:ℤ) * (-1) * invsign ([0,1,6,7] ++ [2,3,4,5]))
  + ((1:ℤ) * 1 * invsign ([0,2,5,7] ++ [1,3,4,6]))
  + ((-1:ℤ) * (-1) * invsign ([0,3,5,6] ++ [1,2,4,7]))
  + ((-1:ℤ) * (-1) * invsign ([1,2,4,7] ++ [0,3,5,6]))
  + ((1:ℤ) * 1 * invsign ([1,3,4,6] ++ [0,2,5,7]))
  + ((-1:ℤ) * (-1) * invsign ([2,3,4,5] ++ [0,1,6,7]))
  + ((1:ℤ) * 1 * invsign ([4,5,6,7] ++ [0,1,2,3]))
  = 8 := by decide

/-! ## Part C: the End-signature arithmetic -/

/-- The Euler signature of End F on the discriminator: chi = +(m^2) * INT W_R^2 = +8 m^2
    is strictly positive at every nonzero scale (corrected sign; audit finding F2). -/
theorem end_mass_positive (m : ℚ) (hm : m ≠ 0) :
    (0:ℚ) < (m*m) * 8 := by
  have hpos : (0:ℚ) < m * m := by
    rcases lt_or_gt_of_ne hm with h | h
    · first
      | exact neg_mul_neg h h
      | have hm2 : (0:ℚ) < -m := by linarith
        nlinarith [hm2]
    · exact mul_pos h h
  nlinarith

/-- The End-mass identity: from the RR signature (corrected positive sign) and Serre duality (declared as
    hypotheses; external leaves E8, E9 of the derivation), every holomorphic realization of the exact Weil
    carrier satisfies h^0 + h^2/2 = h^1 + 4 m^2. -/
theorem end_mass_identity (m h0 h1 h2 h3 h4 chi : ℚ)
    (heuler : chi = h0 - h1 + h2 - h3 + h4)
    (hdual3 : h3 = h1)
    (hdual4 : h4 = h0)
    (hRR : chi = (m*m) * 8) :
    h0 + h2/2 = h1 + (m*m)*8/2 := by
  linarith [heuler, hdual3, hdual4, hRR]

/-- End-mass no-go at the minimal scale: h1 >= 0 and m >= 1  ⟹  h0 + h2/2 >= 4. -/
theorem end_mass_no_go_minimal (m h0 h1 h2 : ℚ)
    (hsig : h0 + h2/2 = h1 + (m*m)*8/2)
    (hm : (1:ℚ) ≤ m) (h1ge : (0:ℚ) ≤ h1) :
    (4:ℚ) ≤ h0 + h2/2 := by
  have hmm : (1:ℚ) ≤ m*m := by nlinarith
  have hdiv : (m*m)*8/2 = (m*m)*4 := by ring
  rw [hsig, hdiv]
  nlinarith

/-- Simple-realization refinement: h0 = 1 (simple carrier), h1 >= 0, m >= 1  ⟹  h2 >= 8 m^2 - 2
    (in particular h2 >= 6 at m = 1 on the discriminator). -/
theorem simple_end_mass_bound (m h0 h1 h2 : ℚ)
    (hsig : h0 + h2/2 = h1 + (m*m)*8/2)
    (h0eq : h0 = 1) (h1ge : (0:ℚ) ≤ h1) (hm : (1:ℚ) ≤ m) :
    (8:ℚ)*m*m - 2 ≤ h2 := by
  have hmm : (1:ℚ) ≤ m*m := by nlinarith
  have hdiv : (m*m)*8/2 = (m*m)*4 := by ring
  rw [h0eq] at hsig
  nlinarith

/-! ## Capstones -/

theorem weil_forcing_frame_capstone_A :
    (∀ t : ℚ, pwN t + (t^2+14*t+625)*(39*t^2-2770*t+72375) = 44000000) ∧
    (∀ t : ℚ, pw t = -(39:ℚ)/44000000 * t^4 + (139:ℚ)/2750000 * t^3 - (527:ℚ)/400000 * t^2
      + (359:ℚ)/22000 * t - (79:ℚ)/2816) ∧
    (∀ t : ℚ, t^2+14*t+625 = 0 → pw t = 1) ∧
    (∀ t : ℚ, t^2-30*t+625 = 0 → pw t = 0) ∧
    pw 25 = 0 := by
  exact ⟨pwN_key_identity, pw_correspondence_coeffs,
    fun t h => pw_fixes_weil h, fun t h => pw_kills_mixed h, pw_kills_ambient⟩

theorem weil_forcing_frame_capstone_B :
    (( (1:ℤ) * 1 * invsign ([0,1,2,3] ++ [4,5,6,7]))
  + ((-1:ℤ) * (-1) * invsign ([0,1,6,7] ++ [2,3,4,5]))
  + ((1:ℤ) * 1 * invsign ([0,2,5,7] ++ [1,3,4,6]))
  + ((-1:ℤ) * (-1) * invsign ([0,3,5,6] ++ [1,2,4,7]))
  + ((-1:ℤ) * (-1) * invsign ([1,2,4,7] ++ [0,3,5,6]))
  + ((1:ℤ) * 1 * invsign ([1,3,4,6] ++ [0,2,5,7]))
  + ((-1:ℤ) * (-1) * invsign ([2,3,4,5] ++ [0,1,6,7]))
  + ((1:ℤ) * 1 * invsign ([4,5,6,7] ++ [0,1,2,3]))) = 8 := by
  exact weil_WR_square_top_certificate

theorem weil_forcing_frame_capstone_C :
    (∀ m h0 h1 h2 h3 h4 chi : ℚ,
      chi = h0 - h1 + h2 - h3 + h4 → h3 = h1 → h4 = h0 → chi = (m*m)*8 →
        h0 + h2/2 = h1 + (m*m)*8/2) ∧
    (∀ m h0 h1 h2 : ℚ,
      h0 + h2/2 = h1 + (m*m)*8/2 → (1:ℚ) ≤ m → (0:ℚ) ≤ h1 → (4:ℚ) ≤ h0 + h2/2) ∧
    (∀ m h0 h1 h2 : ℚ,
      h0 + h2/2 = h1 + (m*m)*8/2 → h0 = 1 → (0:ℚ) ≤ h1 → (1:ℚ) ≤ m →
        (8:ℚ)*m*m - 2 ≤ h2) := by
  exact ⟨fun m h0 h1 h2 h3 h4 chi h1' h2' h3' h4' =>
      end_mass_identity m h0 h1 h2 h3 h4 chi h1' h2' h3' h4',
    fun m h0 h1 h2 hsig hm h1ge => end_mass_no_go_minimal m h0 h1 h2 hsig hm h1ge,
    fun m h0 h1 h2 hsig h0eq h1ge hm =>
      simple_end_mass_bound m h0 h1 h2 hsig h0eq h1ge hm⟩

#print axioms weil_forcing_frame_capstone_A
#print axioms weil_forcing_frame_capstone_B
#print axioms weil_forcing_frame_capstone_C
