import Mathlib

/-!
# GST CARRIER-MECHANISM VERDICT CERTIFICATE (Cycle 2, strike 2)

Lean shadow of the derivation
`research/derivations/GST_carrier_mechanism_verdict_spread_no_go_and_rr_invisibility_2026_10_25.tex`
and the record
`research/records/2026-10-25-gst-carrier-mechanism-verdict-spread-no-go-and-rr-invisibility.md`.

## What is certified here (all statements are exact finite algebra)

Part A — THE INDEX-COLLISION CERTIFICATE AND THE THETA^4 COUNT.
W_R = Re(Omega), Omega = wedge_{j=1..4}(e_j + i f_j), has eight +-1 monomial components, each carrying
exactly one of {e_j, f_j} for every complex index j (DATA from the exterior algebra; the expansion and
signs are proved in the derivation .tex; the signs are IRRELEVANT here because every pairing in sight
vanishes). theta^2 expands over the six pair-words e_a f_a e_b f_b (a < b), each carrying BOTH letters
of its two indices. We certify, by full evaluation (`decide`), that all 8 x 6 = 48 ordered pairings
have a repeated generator index, hence vanish in the exterior algebra:
INT W_R theta^2 = 0.
We further certify the surjection count for theta^4: among the 4^4 = 256 four-letter words in the
pair-block alphabet, exactly 24 have four distinct blocks (each contributing +1 by 2-form
commutativity) and 232 repeat a block (vanishing):  INT theta^4 = 24.
Together with the companion-certified period INT W_R^2 = 8
(GSTWeilForcingFrameCertificate.lean, Part B), these are the three period constants of the strike-2
package.

Part B — THE SINGLE-BAND KILL AND THE TWIST-CHI ARITHMETIC.
The cohomological-spread no-go (Theorem V2 of the derivation) has as its arithmetic core: a cohomology
concentrated in a single degree j with Euler characteristic 0 is ZERO (the band is empty). We certify
this exactly: given h : degrees -> Q with h0 - h1 + h2 - h3 + h4 = 0 and h i = 0 for all i != j
(j < 5), then h j = 0. (The Fourier-Mukai steps that turn "every twist acyclic" into "F = 0" are
external leaf E13 of the derivation and are NOT certified here.)
The RR-invisibility arithmetic (Theorem V1(ii)): with the certified constants INT theta^4 = 24 and
INT W_R theta^2 = 0 as hypotheses, the twist Euler characteristic
chi = r * (k^4 * 24 / 24) + m * (k^2 / 2) * INT_W_R_theta2 equals r * k^4 for all r, m, k
(INDEPENDENT OF m; k = 0 gives the Euler-zero law chi = 0). The End-twist table (Remark R1):
chi_k(End F) = (r*r) * (k^4 * 24 / 24) + (2*r*m) * (k^2 / 2) * INT_W_R_theta2 + (m*m) * INT_W_R^2
equals (r*r) * k^4 + (m*m) * 8: the Weil-End mass 8 m^2 is twist-constant (at k = 0 this reproduces
the strike-1 End-mass chi = +8 m^2).

## What is NOT certified here (scheme-level; proved in the .tex on declared leaves)

The Pic^0-class lemma (c_1(P) = 0; exponential sequence, leaf E12); Hirzebruch-Riemann-Roch with
td(T_A) = 1 on abelian A (leaf E8 of the strike-1 set); Chern-character multiplicativity (leaf E5);
the Fourier-Mukai toolkit: derived base change along the Poincare family, perfectness preservation,
and the equivalence (leaf E13); Mukai's semi-homogeneous band theorem (leaf E14; used only in the
conditional corollary that no semi-homogeneous bundle is an exact carrier). The scale-monoid
structure (Proposition V3) is set arithmetic in the .tex (no finite content). The monomial sign
table of W_R is DATA from the exterior algebra (each entry independently checkable by hand); the
collision certificate is sign-free by vanishing. No sorry, no custom axioms, no native_decide.
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 100000

/-! ## Part A: the index-collision certificate and the theta^4 surjection count -/

/-- Duplicate detection on an index list: the list has a repeated entry. -/
def hasDup (l : List ℕ) : Bool :=
  decide (l.eraseDups.length < l.length)

/-- The eight monomial components of W_R = Re(Omega) (indices 0..7 encode e1..e4, f1..f4;
each monomial carries exactly one of {e_j, f_j} per complex index j = 0..3). The signs (+1, -1 x6, +1)
are DATA from the exterior algebra and are irrelevant for the collision certificate (all pairings
vanish); see the derivation .tex. -/
def wrMonoLists : List (List ℕ) :=
  [[0,2,4,6], [1,3,4,6], [1,2,5,6], [1,2,4,7],
   [0,3,5,6], [0,3,4,7], [0,2,5,7], [1,3,5,7]]

/-- The six theta^2 pair-words e_a f_a e_b f_b for a < b (each carries BOTH letters of its
two indices). -/
def theta2Words : List (List ℕ) :=
  [[0,1,2,3], [0,1,4,5], [0,1,6,7], [2,3,4,5], [2,3,6,7], [4,5,6,7]]

/-- THE INDEX-COLLISION CERTIFICATE: all 48 ordered W_R-monomial--theta^2-word pairings have a
repeated generator index, hence the exterior product vanishes: INT W_R theta^2 = 0. -/
theorem weil_WR_theta2_collision :
    (wrMonoLists.all (fun m => theta2Words.all (fun w => hasDup (m ++ w))) = true) ∧
    (wrMonoLists.length = 8) ∧
    (theta2Words.length = 6) := by
  decide

/-- Base-4 digit word of length 4 encoding a theta^4 word (the pair-block choices). -/
def b4word (n : ℕ) : List ℕ := [n/64 % 4, n/16 % 4, n/4 % 4, n % 4]

/-- THE THETA^4 SURJECTION COUNT: among the 4^4 = 256 words, exactly 24 have four distinct
pair-blocks (each contributes +1 by 2-form commutativity) and 232 repeat a block (vanishing):
theta^4 = 24 vol, i.e. INT theta^4 = 24. -/
theorem theta4_surjection_count :
    ((List.range 256).countP (fun n => decide ((b4word n).eraseDups.length = 4)) = 24) ∧
    ((List.range 256).countP (fun n => decide ((b4word n).eraseDups.length < 4)) = 232) := by
  decide

/-! ## Part B: the single-band kill and the twist-chi arithmetic -/

/-- The single-band kill (arithmetic core of the spread no-go, Theorem V2(ii)): a cohomology
concentrated in one degree j with Euler characteristic 0 is zero. -/
theorem wit_kill (j : ℕ) (h : ℕ → ℚ)
    (hchi : h 0 - h 1 + h 2 - h 3 + h 4 = 0)
    (hband : ∀ i, i ≠ j → h i = 0)
    (hj : j < 5) :
    h j = 0 := by
  interval_cases j
  · have e1 : h 1 = 0 := hband 1 (by decide)
    have e2 : h 2 = 0 := hband 2 (by decide)
    have e3 : h 3 = 0 := hband 3 (by decide)
    have e4 : h 4 = 0 := hband 4 (by decide)
    linarith
  · have e0 : h 0 = 0 := hband 0 (by decide)
    have e2 : h 2 = 0 := hband 2 (by decide)
    have e3 : h 3 = 0 := hband 3 (by decide)
    have e4 : h 4 = 0 := hband 4 (by decide)
    linarith
  · have e0 : h 0 = 0 := hband 0 (by decide)
    have e1 : h 1 = 0 := hband 1 (by decide)
    have e3 : h 3 = 0 := hband 3 (by decide)
    have e4 : h 4 = 0 := hband 4 (by decide)
    linarith
  · have e0 : h 0 = 0 := hband 0 (by decide)
    have e1 : h 1 = 0 := hband 1 (by decide)
    have e2 : h 2 = 0 := hband 2 (by decide)
    have e4 : h 4 = 0 := hband 4 (by decide)
    linarith
  · have e0 : h 0 = 0 := hband 0 (by decide)
    have e1 : h 1 = 0 := hband 1 (by decide)
    have e2 : h 2 = 0 := hband 2 (by decide)
    have e3 : h 3 = 0 := hband 3 (by decide)
    linarith

/-- RR-invisibility arithmetic (Theorem V1(ii)): with the certified period constants, the twist
Euler characteristic of the exact carrier is r * k^4, independent of the scale m
(k = 0 is the Euler-zero law chi = 0). -/
theorem carrier_twist_chi (r m k iWRtheta2 chi : ℚ)
    (hcert : iWRtheta2 = 0)
    (hRR : chi = r * (k^4 * 24 / 24) + m * (k^2 / 2) * iWRtheta2) :
    chi = r * k^4 := by
  rw [hcert, mul_zero, add_zero] at hRR
  rw [hRR]
  have h24 : (24:ℚ) ≠ 0 := by decide
  field_simp

/-- Euler-zero law instance: at k = 0 the carrier twist-chi vanishes (Theorem V1(i) on the
discriminator). -/
theorem euler_zero_instance (r m k chi : ℚ)
    (hRR : chi = r * k^4)
    (hk : k = 0) :
    chi = 0 := by
  rw [hk] at hRR
  rw [hRR]
  norm_num

/-- End-twist table (Remark R1): chi_k(End F) = r^2 k^4 + 8 m^2; the Weil-End mass 8 m^2 is
twist-constant (at k = 0: the certified End-mass chi = +8 m^2 of strike 1; INT W_R^2 = 8 enters
as the companion-certified constant). -/
theorem end_twist_chi (r m k iWRtheta2 iWR2 chi : ℚ)
    (hcert : iWRtheta2 = 0)
    (hWR2 : iWR2 = 8)
    (hRR : chi = (r*r) * (k^4 * 24 / 24) + (2*r*m) * (k^2 / 2) * iWRtheta2 + (m*m) * iWR2) :
    chi = (r*r) * k^4 + (m*m) * 8 := by
  rw [hcert, hWR2, mul_zero, add_zero] at hRR
  rw [hRR]
  have h24 : (24:ℚ) ≠ 0 := by decide
  field_simp

/-! ## Capstones -/

theorem carrier_mechanism_verdict_capstone_A :
    (wrMonoLists.all (fun m => theta2Words.all (fun w => hasDup (m ++ w))) = true) ∧
    ((List.range 256).countP (fun n => decide ((b4word n).eraseDups.length = 4)) = 24) ∧
    ((List.range 256).countP (fun n => decide ((b4word n).eraseDups.length < 4)) = 232) := by
  exact ⟨weil_WR_theta2_collision.1, theta4_surjection_count.1, theta4_surjection_count.2⟩

theorem carrier_mechanism_verdict_capstone_B :
    ∀ (j : ℕ) (h : ℕ → ℚ),
      h 0 - h 1 + h 2 - h 3 + h 4 = 0 → (∀ i, i ≠ j → h i = 0) → j < 5 → h j = 0 :=
  fun j h hchi hband hj => wit_kill j h hchi hband hj

theorem carrier_mechanism_verdict_capstone_C :
    (∀ r m k i chi : ℚ, i = 0 →
      chi = r * (k^4 * 24 / 24) + m * (k^2 / 2) * i → chi = r * k^4) ∧
    (∀ r m k i chi : ℚ, i = 0 → chi = r * k^4 → k = 0 → chi = 0) ∧
    (∀ r m k i i8 chi : ℚ, i = 0 → i8 = 8 →
      chi = (r*r) * (k^4 * 24 / 24) + (2*r*m) * (k^2 / 2) * i + (m*m) * i8 →
      chi = (r*r) * k^4 + (m*m) * 8) :=
  ⟨fun r m k i chi hi hRR => carrier_twist_chi r m k i chi hi hRR,
   fun r m k i chi hi hRR hk => euler_zero_instance r m k chi hRR hk,
   fun r m k i i8 chi hi h8 hRR => end_twist_chi r m k i i8 chi hi h8 hRR⟩

#print axioms carrier_mechanism_verdict_capstone_A
#print axioms carrier_mechanism_verdict_capstone_B
#print axioms carrier_mechanism_verdict_capstone_C
