import Mathlib

/-!
# GST PAIR-CHANNEL WALLS CERTIFICATE (Cycle 4, strike 1: the Lean layer)

Lean shadow of the derivation
`research/derivations/GST_pair_channel_walls_fm_duality_and_weil_charge_2026_10_26.tex`
and the record
`research/records/2026-10-26-gst-pair-channel-walls-fm-duality-and-weil-charge.md`.

## What is certified here (all statements are exact finite algebra, INTEGER arithmetic)

The bitmask exterior model of the discriminator's rational cohomology ring: the eight letters
e1,f1,e2,f2,e3,f3,e4,f4 sit at positions 0..7 (block j = {2j, 2j+1}); a class is a normalized list of
(INTEGER coefficient, monomial-mask) pairs, sorted by ascending mask, coefficients merged, zeros
dropped. Every kernel-evaluated statement in this file is an equality of integer classes, integer
period values, or integer Chern-conductor numerators - the committed decide idiom (Nat/Int/List
arithmetic only; no Rat computation is kernel-evaluated anywhere). The Newton conductors are carried
in numerator form (ch_2-num = c_1^2 - 2 c_2; ch_3-num = c_1^3 - 3 c_1 c_2 + 3 c_3;
ch_4-num = c_1^4 - 4 c_1^2 c_2 + 2 c_2^2 + 4 c_1 c_3 - 4 c_4), and the Euler pairing is certified in
the 24-scaled integer form chi24 = 24 * chi (the conductor denominators cleared:
chi24(A,B) = INT [b_0 * g4A + a_0 * g4B + 4 * (g1A AND g3B) + 6 * (g2A AND g2B) + 4 * (g3A AND g1B)],
where g_k are the numerator grades).

Part A - LEMMA W0 (ring annihilation) AND THE PERIODS.
theta = sum of the four pair-words e_j f_j (masks 3,12,48,192). We certify theta^j AND W = the ZERO
CLASS for j = 1, 2, 3 and W in {W_R, W_I} (six class annihilations; every term dies by the
repeated-generator collision - each theta^j monomial fully occupies at least one block, and every
Weil monomial carries one letter of every block). j = 4 is vacuous by degree (2j + 4 > 8).
We re-confirm, in the bitmask model, every committed period constant: INT theta^4 = 24,
INT W_R^2 = 8, INT W_I^2 = 8, INT W_R W_I = 0, Omega OmegaBar = W_R^2 + W_I^2 = 16 vol,
and INT W_R theta^j = 0 for j = 1..4. These agree with the kernel-green certificates
GSTCarrierMechanismVerdictCertificate.lean (Part A) and GSTWeilForcingFrameCertificate.lean (Part B),
which use a different (index-list) encoding - the two encodings cross-check each other.

Part B - W4 ARITHMETIC (the pair invisibility corridor), universal laws in hypothesis form.
Given the W0-annihilated period constants as hypotheses, the twist difference-Euler of any pure pair
chi(E+ tensor L) - chi(E- tensor L) = m * (k * i1 + (k^2/2) * i2) with i1 = i2 = 0, hence = 0 for
EVERY line bundle level k (k = 0 is the Pic^0 case). The linear-detector arithmetic: the only
surviving term of chi(E+ tensor G) - chi(E- tensor G) is m * <W_R, ch_2(G)> (the degree-4 and
degree-6 cross-grades have no degree-8 component; the degree-10 cross-grade is zero in the model).

Part C - W5 FM NORMALIZATION (exact).
The cohomological Fourier-Mukai transform on degree-4 classes, in the dual-basis convention
c_1(P) = sum_p u_p (x) u_hat_p, sends a monomial u_S to wsign(l_S, l_{S^c}) * u_hat_{S^c}
(complement mask; the fourth wedge of c_1(P) divided by 4! contributes exactly this reorder sign).
We certify: fm(W_R) = W_R and fm(W_I) = W_I (the dual fourfold's Weil classes in the position-matched
dual basis have the SAME DATA tables, so these equalities ARE the exact-coefficient-1 normalization
Phi_hat(W_R) = W_R-dual, Phi_hat(W_I) = W_I-dual of the derivation's Lemma), and both round trips
are the identity: fm(fm(W_R)) = W_R, fm(fm(W_I)) = W_I.

Part D - W6 SYNTHETIC PAIR INSTANCES (the pair Chern table, integer form).
The Newton conductor numerators and the pair construction
c_2(E+) = c_2(E-) - m W_R, c_3(E+) = c_3(E-) + c_1 (-m W_R),
c_4(E+) = c_4(E-) - m * (c_2(E-) AND W_R) + m^2 * (W_R^2 / 2)     [the c_1-terms cancel; the
half-period class W_R^2/2 = 4 vol is the certified constant INT W_R^2 = 8 halved - an integral class]
are evaluated on four instances (r, m, c_1, gamma) = (3,1,0,0), (5,2,0,0), (4,1,theta,0),
(7,3,theta,5 vol) with c_2(E-) = W_R, plus the carrier instance (5,1,0,0) with c_2(E-) = 0 (the O^r
side), plus the linear-detector instance (6,2,0,0) with probe G = E-. We certify for each: grade
purity (the ch_2-numerator difference = 2m W_R; the ch_3- and ch_4-numerator differences zero), the
charge split q(E+) - q(E-) = -8 m with q(G) = INT (W_R AND c_2(G)), and the three mixed-End table
identities in the 24-scaled form:
24 * [chi(End E+) - chi(E+ x E-^vee)] = 24 * (8 m^2 - m q(E-)),
24 * [chi(E+ x E-^vee) - chi(End E-)] = 24 * (- m q(E-)),
24 * [chi(End E+) - chi(End E-)] = 24 * (8 m^2 - 2 m q(E-)),
and the carrier consistency: q = 0 recovers the committed End-mass law
24 * chi(End F) = 24 * 8 m^2 (at m = 1) together with chi24(End O^r) = 0 (Euler-zero).
The universal laws behind the table are certified in hypothesis form (over Q, tactic-proved): the
charge split follows from INT W_R^2 = 8; the mixed-End table follows from the charge split and the
W0-annihilated c_1^2-pairing; the third line is the telescoped SUM of the first two.

## What is NOT certified here (scheme-level; proved in the .tex on declared leaves)

Hirzebruch-Riemann-Roch with td = 1 on abelian A (leaf E8); Chern-character multiplicativity (E5);
GAGA (E3); Serre duality (E9); the derived Fourier-Mukai toolkit - perfectness preservation, the
equivalence, and the E13 identity Phi_hat_Phi ~ (-1)^* [-8] (the g = 4 evenness observation used
there is derivation-level); GRR for the cohomological-transform formula; the dual-world axioms
(the dual is again a nonsplit Q(i)-Weil fourfold with NS = Z theta-hat - standard polarized duality,
flagged in the derivation); the K^0 presentation (classes are differences of holomorphic bundles);
the pair-form equivalence content itself (committed W2, audit-closed cycle 2 - NOT re-proved here);
the integrality of Weil charges (standard integrality of W_R and c_2); the degree-bookkeeping leaf
(the degree-4/6/10 cross-grades contribute no degree-8 component; the synthetic instances compute
them exactly). The monomial DATA tables (W_R, W_I signs and masks) are DATA from the exterior
algebra, each entry independently checkable by hand; they were additionally cross-checked against
an independent reconstruction and against the committed index-list certificates, and the integer
restatement of every decided proposition was pre-verified by the mirror script
research/experiments/task14a_lean_data_mirror.py.

## Scope (the strike's scope box, restated at the Lean layer)

This certificate DETERMINES NO BIT: no decision of S = 0 versus S = W_Q, no monoid-bit claim, no
exhaustiveness claim, no resolution of the campaign target. The walls are necessary conditions and
transport structure on the pair channel; the dichotomy bit remains the campaign's forcing vertex.
No sorry, no custom axioms, no native_decide.
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 100000

/-! ## The bitmask exterior model (INTEGER coefficients) -/

/-- The letter positions of a monomial mask (positions 0..7; the committed div/mod idiom). -/
def bitList (m : ℕ) : List ℕ := (List.range 8).filter (fun i => ((m / 2 ^ i) % 2 = 1))

/-- Disjointness of two masks: no letter position set in both (the committed countP idiom). -/
def disjoint (m1 m2 : ℕ) : Bool :=
  decide ((bitList m1).countP (fun a => ((m2 / 2 ^ a) % 2 = 1)) = 0)

/-- Cross inversions between two ascending words: #(a in l1, b in l2) with a > b. -/
def invPairs : List ℕ → List ℕ → ℕ
  | [], _ => 0
  | a :: as, l2 => l2.countP (fun b => decide (a > b)) + invPairs as l2

/-- The wedge reorder sign u_{l1} AND u_{l2} = wsign * u_{sorted}: +1 if even, -1 if odd. -/
def wsign (l1 l2 : List ℕ) : ℤ := if invPairs l1 l2 % 2 = 0 then 1 else -1

/-- The coefficient of a mask in a raw class list. -/
def coeffOf (m : ℕ) : List (ℤ × ℕ) → ℤ
  | [] => 0
  | p :: ps => if p.2 = m then p.1 + coeffOf m ps else coeffOf m ps

/-- Insert a term into a sorted-by-mask accumulator, merging equal masks. -/
def insertTerm (p : ℤ × ℕ) : List (ℤ × ℕ) → List (ℤ × ℕ)
  | [] => [p]
  | q :: qs =>
    if p.2 < q.2 then p :: q :: qs
    else if p.2 = q.2 then (q.1 + p.1, q.2) :: qs
    else q :: insertTerm p qs

/-- Accumulate a raw class list into sorted merged form, dropping zero coefficients at the end. -/
def normAcc : List (ℤ × ℕ) → List (ℤ × ℕ) → List (ℤ × ℕ)
  | [], acc => acc.filter (fun p => p.1 ≠ 0)
  | p :: rest, acc => normAcc rest (insertTerm p acc)

/-- Normal form of a class: ascending distinct masks, merged coefficients, no zeros. -/
def normCl (c : List (ℤ × ℕ)) : List (ℤ × ℕ) := normAcc c []

/-- The surviving product terms of one left monomial against a right class. -/
def pairTerms (p : ℤ × ℕ) : List (ℤ × ℕ) → List (ℤ × ℕ)
  | [] => []
  | q :: rest =>
    if disjoint p.2 q.2 = true then
      (p.1 * q.1 * wsign (bitList p.2) (bitList q.2), p.2 + q.2) :: pairTerms p rest
    else pairTerms p rest

/-- All surviving product terms of two raw classes. -/
def wedgeTerms : List (ℤ × ℕ) → List (ℤ × ℕ) → List (ℤ × ℕ)
  | [], _ => []
  | p :: rest, c2 => pairTerms p c2 ++ wedgeTerms rest c2

/-- The wedge of two classes in the bitmask model (disjoint masks merge by SUM: union = sum). -/
def wedgeCl (c1 c2 : List (ℤ × ℕ)) : List (ℤ × ℕ) :=
  normCl (wedgeTerms c1 c2)

/-- Scalar multiple of a class (integer scalars). -/
def smulCl (q : ℤ) (c : List (ℤ × ℕ)) : List (ℤ × ℕ) := normCl (c.map (fun p => (q * p.1, p.2)))

/-- Sum of classes. -/
def addCl (c1 c2 : List (ℤ × ℕ)) : List (ℤ × ℕ) := normCl (c1 ++ c2)

/-- Exterior power of a class. -/
def powCl (c : List (ℤ × ℕ)) : ℕ → List (ℤ × ℕ)
  | 0 => [(1, 0)]
  | (k+1) => wedgeCl (powCl c k) c

/-- The integral: the coefficient of the volume monomial (mask 255 = all eight letters). -/
def intCl (c : List (ℤ × ℕ)) : ℤ := coeffOf 255 c

/-- The cohomological FM transform on degree-4 classes (dual-basis convention): a monomial goes to
    its wsign-weighted complement mask (the complement of m in the 8-letter volume is 255 - m). -/
def fmCl (x : List (ℤ × ℕ)) : List (ℤ × ℕ) :=
  normCl (x.map (fun p => (p.1 * wsign (bitList p.2) (bitList (255 - p.2)), 255 - p.2)))

/-! ## DATA: the Weil classes, theta, and the half-period class (exterior algebra; hand-checkable) -/

/-- W_R = Re(Omega), Omega = wedge_{j=0..3}(e_j + i f_j): eight monomials, one letter of every block;
sign +1 for an even number of f-letters with Re(i^2) = -1 at #f = 2, +1 at #f = 0, 4. Ascending masks. -/
def WRcl : List (ℤ × ℕ) :=
  [(1, 85), (-1, 90), (-1, 102), (-1, 105), (-1, 150), (-1, 153), (-1, 165), (1, 170)]

/-- W_I = Im(Omega): sign +1 at #f = 1, -1 at #f = 3. Ascending masks. -/
def WIcl : List (ℤ × ℕ) :=
  [(1, 86), (1, 89), (1, 101), (-1, 106), (1, 149), (-1, 154), (-1, 166), (-1, 169)]

/-- theta = c_1(O(Theta)) = the sum of the four pair-words e_j f_j. -/
def THETAd : List (ℤ × ℕ) := [(1, 3), (1, 12), (1, 48), (1, 192)]

/-- The half-period class W_R^2 / 2 = 4 vol (the certified INT W_R^2 = 8, halved; integral). -/
def HALFWR2cl : List (ℤ × ℕ) := [(4, 255)]

/-- The zero class. -/
def zeroCl : List (ℤ × ℕ) := []

/-! ## Part A: Lemma W0 (class annihilation) and the period constants -/

/-- LEMMA W0 for W_R: theta^j AND W_R is the ZERO CLASS for j = 1, 2, 3 (j = 4 vacuous by degree). -/
theorem w0_ring_annihilation_WR :
    (wedgeCl (powCl THETAd 1) WRcl = []) ∧
    (wedgeCl (powCl THETAd 2) WRcl = []) ∧
    (wedgeCl (powCl THETAd 3) WRcl = []) := by
  decide

/-- LEMMA W0 for W_I: theta^j AND W_I is the ZERO CLASS for j = 1, 2, 3. -/
theorem w0_ring_annihilation_WI :
    (wedgeCl (powCl THETAd 1) WIcl = []) ∧
    (wedgeCl (powCl THETAd 2) WIcl = []) ∧
    (wedgeCl (powCl THETAd 3) WIcl = []) := by
  decide

/-- Period constants re-confirmed in the bitmask model (cross-check of the committed greens):
    theta^4 = 24 vol; W_R^2 = 8 vol; W_I^2 = 8 vol; W_R W_I = 0; Omega OmegaBar = 16 vol;
    INT W_R theta^j = 0 for j = 1..4. -/
theorem periods_reconfirm :
    (intCl (powCl THETAd 4) = 24) ∧
    (intCl (wedgeCl WRcl WRcl) = 8) ∧
    (intCl (wedgeCl WIcl WIcl) = 8) ∧
    (intCl (wedgeCl WRcl WIcl) = 0) ∧
    (intCl (addCl (wedgeCl WRcl WRcl) (wedgeCl WIcl WIcl)) = 16) ∧
    (∀ j ∈ [1, 2, 3, 4], intCl (wedgeCl WRcl (powCl THETAd j)) = 0) := by
  decide

/-! ## Part B: the W4 corridor arithmetic (universal laws, hypothesis form; proved over Q) -/

/-- W4(i) arithmetic: with the W0-annihilated periods i1 = INT W_R theta = 0 and i2 = INT W_R theta^2
    = 0, the twist difference-Euler of a pure pair vanishes at EVERY polarization level k
    (k = 0 is the Pic^0 case). The degree bookkeeping (only the j = 2 term of e^{k theta} reaches
    degree 8; j >= 3 is zero in the model) is the declared leaf, backed by Part A. -/
theorem pair_twist_difference_zero (m k i1 i2 chi : ℚ)
    (h1 : i1 = 0) (h2 : i2 = 0)
    (hRR : chi = m * ((k * i1) + ((k^2 / 2) * i2))) :
    chi = 0 := by
  rw [h1, h2] at hRR
  rw [hRR]
  ring

/-- W4(iii) arithmetic: the only surviving term of the difference-Euler against a perfect G is
    m * <W_R, ch_2(G)>; the degree-4 and degree-6 cross-grades carry no degree-8 component and the
    degree-10 cross-grade is zero in the model (declared leaf; computed exactly in the synthetic
    instances below). -/
theorem pair_linear_detector_arithmetic (m a0 a1 a2 a3 chi : ℚ)
    (h0 : a0 = 0) (h1 : a1 = 0) (h3 : a3 = 0)
    (hRR : chi = m * (a0 + a1 + a2 + a3)) :
    chi = m * a2 := by
  rw [h0, h1, h3] at hRR
  rw [hRR]
  ring

/-! ## Part C: the W5 FM normalization (exact) -/

/-- LEMMA (normalization) + round trips: the cohomological FM transform carries W_R (resp. W_I)
    identically onto the dual Weil class (the dual DATA table is the same list: coefficient 1),
    and both round trips are the identity. -/
theorem fm_normalization_exact :
    (fmCl WRcl = WRcl) ∧
    (fmCl WIcl = WIcl) ∧
    (fmCl (fmCl WRcl) = WRcl) ∧
    (fmCl (fmCl WIcl) = WIcl) := by
  decide

/-! ## Part D: the W6 pair Chern table (integer conductor numerators) -/

/-- The grade-2 conductor numerator: ch_2-num = c_1^2 - 2 c_2. -/
def ch2n (c1 c2 : List (ℤ × ℕ)) : List (ℤ × ℕ) :=
  addCl (powCl c1 2) (smulCl (-2) c2)

/-- The grade-3 conductor numerator: ch_3-num = c_1^3 - 3 c_1 c_2 + 3 c_3. -/
def ch3n (c1 c2 c3 : List (ℤ × ℕ)) : List (ℤ × ℕ) :=
  addCl (addCl (powCl c1 3) (smulCl (-3) (wedgeCl c1 c2))) (smulCl 3 c3)

/-- The grade-4 conductor numerator:
    ch_4-num = c_1^4 - 4 c_1^2 c_2 + 2 c_2^2 + 4 c_1 c_3 - 4 c_4. -/
def ch4n (c1 c2 c3 c4 : List (ℤ × ℕ)) : List (ℤ × ℕ) :=
  addCl (addCl (addCl (addCl (powCl c1 4)
    (smulCl (-4) (wedgeCl (powCl c1 2) c2))) (smulCl 2 (powCl c2 2)))
    (smulCl 4 (wedgeCl c1 c3))) (smulCl (-4) c4)

/-- The pair construction: c_2(E+) = c_2(E-) - m W_R. -/
def pairC2P (m : ℤ) (c2M : List (ℤ × ℕ)) : List (ℤ × ℕ) := addCl c2M (smulCl (-m) WRcl)

/-- The pair construction: c_3(E+) - c_3(E-) = c_1 AND (-m W_R). -/
def pairC3Shift (c1 : List (ℤ × ℕ)) (m : ℤ) : List (ℤ × ℕ) := wedgeCl c1 (smulCl (-m) WRcl)

/-- The pair construction: the c_4 shift closing grade 4. The general form is
    Delta c_4 = -(c_1^2 AND (-m W_R)) + (c_2(E+)^2 - c_2(E-)^2)/2 + c_1 AND c_3shift, whose c_1-terms
    cancel, leaving Delta(c_2^2)/2 = -m * (c_2(E-) AND W_R) + m^2 * (W_R^2/2), integral by the
    certified INT W_R^2 = 8. -/
def pairC4Shift (c2M : List (ℤ × ℕ)) (m : ℤ) : List (ℤ × ℕ) :=
  addCl (smulCl (-m) (wedgeCl c2M WRcl)) (smulCl (m * m) HALFWR2cl)

/-- A Chern character with its five grades (grade 0 as a scalar; grades 1..4 as conductor
    numerators: g_k = 24-, 6-, 2-, 1-fold multiples of the character grades respectively). -/
structure ChPair where
  r : ℤ
  g1 : List (ℤ × ℕ)
  g2 : List (ℤ × ℕ)
  g3 : List (ℤ × ℕ)
  g4 : List (ℤ × ℕ)

/-- The per-grade dual character: grades 1 and 3 flip sign (ch(E^vee) = sum (-1)^j ch_j). -/
def chDualP (x : ChPair) : ChPair where
  r := x.r
  g1 := smulCl (-1) x.g1
  g2 := x.g2
  g3 := smulCl (-1) x.g3
  g4 := x.g4

/-- The 24-scaled Euler pairing of two characters: chi24(A,B) = 24 * chi(A,B), the conductor
    denominators cleared (all integer arithmetic). -/
def chiPP24 (x y : ChPair) : ℤ :=
  intCl (addCl (smulCl y.r x.g4) (addCl (smulCl x.r y.g4)
    (addCl (smulCl 4 (wedgeCl x.g1 y.g3))
      (addCl (smulCl 6 (wedgeCl x.g2 y.g2)) (smulCl 4 (wedgeCl x.g3 y.g1))))))

/-- The pure-pair character construction: E+ from (r, c_1, c_2(E-), gamma) at integer scale m. -/
def pairEplus (r : ℤ) (c1 c2M gamma : List (ℤ × ℕ)) (m : ℤ) : ChPair where
  r := r
  g1 := c1
  g2 := ch2n c1 (pairC2P m c2M)
  g3 := ch3n c1 (pairC2P m c2M) (pairC3Shift c1 m)
  g4 := ch4n c1 (pairC2P m c2M) (pairC3Shift c1 m) (addCl gamma (pairC4Shift c2M m))

/-- The baseline character: E- from (r, c_1, c_2(E-), gamma) with c_3 = 0. -/
def pairEminus (r : ℤ) (c1 c2M gamma : List (ℤ × ℕ)) : ChPair where
  r := r
  g1 := c1
  g2 := ch2n c1 c2M
  g3 := ch3n c1 c2M zeroCl
  g4 := ch4n c1 c2M zeroCl gamma

/-- The Weil charge q(G) = INT (W_R AND c_2(G)). -/
def weilCharge (c2 : List (ℤ × ℕ)) : ℤ := intCl (wedgeCl WRcl c2)

/-! ### The universal table laws (hypothesis form; proved over Q) -/

/-- W6(iv) universal: the charge split follows from the certified period INT W_R^2 = 8:
    q(E+) - q(E-) = -m * INT W_R^2 = -8 m. -/
theorem pair_charge_split_universal (m iWR2 qP qM : ℚ)
    (hi : iWR2 = 8)
    (hp : qP - qM = -m * iWR2) :
    qP - qM = -8 * m := by
  rw [hi] at hp
  linarith [hp]

/-- W6(v), first line, universal: chi(End E+) - chi(E+ x E-^vee) = -m q(E+) = 8 m^2 - m q(E-)
    (the c_1^2-pairing dies by W0; the anchor is the charge split). -/
theorem pair_end_table_t1 (m qP qM chi1 : ℚ)
    (hq : chi1 = -m * qP)
    (hs : qP - qM = -8 * m) :
    chi1 = 8 * m * m - m * qM := by
  have hqP : qP = qM - 8 * m := by linarith
  rw [hqP] at hq
  rw [hq]
  ring

/-- W6(v), second line, universal: chi(E+ x E-^vee) - chi(End E-) = m * (p1/2 - q(E-)) with the
    W0-annihilated c_1^2-pairing p1 = 0, hence = -m q(E-). -/
theorem pair_end_table_t2 (m qM p1 chi2 : ℚ)
    (hp1 : p1 = 0)
    (hRR : chi2 = m * ((p1 / 2) - qM)) :
    chi2 = -m * qM := by
  rw [hp1] at hRR
  rw [hRR]
  ring

/-- W6(v), third line, universal: the telescoped SUM of the first two lines
    (chi(End E+) - chi(End E-) = [chi(End E+) - chi(E+ x E-^vee)] + [chi(E+ x E-^vee) - chi(End E-)]). -/
theorem pair_end_table_t3 (m qM chi1 chi2 d : ℚ)
    (h1 : chi1 = 8 * m * m - m * qM)
    (h2 : chi2 = -m * qM)
    (hd : d = chi1 + chi2) :
    d = 8 * m * m - 2 * m * qM := by
  rw [hd, h1, h2]
  ring

/-- W6(vi), carrier consistency, universal: at q(E-) = 0 the third line reads
    chi(End F) - chi(End O^r) = 8 m^2, the committed End-mass law (W3 instance). -/
theorem carrier_end_mass (m d : ℚ)
    (h : d = 8 * m * m - 2 * m * ((0:ℚ))) :
    d = 8 * m * m := by
  rw [h]
  ring

/-! ### The synthetic instances (bounded exact integer evaluation) -/

/-- W6 synthetic instance 1 (r, m, c_1, gamma) = (3, 1, 0, 0), c_2(E-) = W_R:
    grade purity (numerator form), the charge split -8 m, and the three 24-scaled mixed-End
    table identities. -/
theorem w6_instance_1 :
    (addCl (pairEplus 3 zeroCl WRcl zeroCl 1).g2 (smulCl (-1) (pairEminus 3 zeroCl WRcl zeroCl).g2)
      = smulCl 2 WRcl) ∧
    (addCl (pairEplus 3 zeroCl WRcl zeroCl 1).g3 (smulCl (-1) (pairEminus 3 zeroCl WRcl zeroCl).g3)
      = zeroCl) ∧
    (addCl (pairEplus 3 zeroCl WRcl zeroCl 1).g4 (smulCl (-1) (pairEminus 3 zeroCl WRcl zeroCl).g4)
      = zeroCl) ∧
    (weilCharge (pairC2P 1 WRcl) - weilCharge WRcl = -8 * 1) ∧
    (chiPP24 (pairEplus 3 zeroCl WRcl zeroCl 1) (chDualP (pairEplus 3 zeroCl WRcl zeroCl 1))
      - chiPP24 (pairEplus 3 zeroCl WRcl zeroCl 1) (chDualP (pairEminus 3 zeroCl WRcl zeroCl))
      = 24 * (8 * 1 * 1 - 1 * (weilCharge WRcl))) ∧
    (chiPP24 (pairEplus 3 zeroCl WRcl zeroCl 1) (chDualP (pairEminus 3 zeroCl WRcl zeroCl))
      - chiPP24 (pairEminus 3 zeroCl WRcl zeroCl) (chDualP (pairEminus 3 zeroCl WRcl zeroCl))
      = 24 * (-1 * (weilCharge WRcl))) ∧
    (chiPP24 (pairEplus 3 zeroCl WRcl zeroCl 1) (chDualP (pairEplus 3 zeroCl WRcl zeroCl 1))
      - chiPP24 (pairEminus 3 zeroCl WRcl zeroCl) (chDualP (pairEminus 3 zeroCl WRcl zeroCl))
      = 24 * (8 * 1 * 1 - 2 * 1 * (weilCharge WRcl))) := by
  decide

/-- W6 synthetic instance 2 (r, m, c_1, gamma) = (5, 2, 0, 0), c_2(E-) = W_R. -/
theorem w6_instance_2 :
    (addCl (pairEplus 5 zeroCl WRcl zeroCl 2).g2 (smulCl (-1) (pairEminus 5 zeroCl WRcl zeroCl).g2)
      = smulCl 4 WRcl) ∧
    (addCl (pairEplus 5 zeroCl WRcl zeroCl 2).g3 (smulCl (-1) (pairEminus 5 zeroCl WRcl zeroCl).g3)
      = zeroCl) ∧
    (addCl (pairEplus 5 zeroCl WRcl zeroCl 2).g4 (smulCl (-1) (pairEminus 5 zeroCl WRcl zeroCl).g4)
      = zeroCl) ∧
    (weilCharge (pairC2P 2 WRcl) - weilCharge WRcl = -8 * 2) ∧
    (chiPP24 (pairEplus 5 zeroCl WRcl zeroCl 2) (chDualP (pairEplus 5 zeroCl WRcl zeroCl 2))
      - chiPP24 (pairEplus 5 zeroCl WRcl zeroCl 2) (chDualP (pairEminus 5 zeroCl WRcl zeroCl))
      = 24 * (8 * 2 * 2 - 2 * (weilCharge WRcl))) ∧
    (chiPP24 (pairEplus 5 zeroCl WRcl zeroCl 2) (chDualP (pairEminus 5 zeroCl WRcl zeroCl))
      - chiPP24 (pairEminus 5 zeroCl WRcl zeroCl) (chDualP (pairEminus 5 zeroCl WRcl zeroCl))
      = 24 * (-2 * (weilCharge WRcl))) ∧
    (chiPP24 (pairEplus 5 zeroCl WRcl zeroCl 2) (chDualP (pairEplus 5 zeroCl WRcl zeroCl 2))
      - chiPP24 (pairEminus 5 zeroCl WRcl zeroCl) (chDualP (pairEminus 5 zeroCl WRcl zeroCl))
      = 24 * (8 * 2 * 2 - 2 * 2 * (weilCharge WRcl))) := by
  decide

/-- W6 synthetic instance 3 (r, m, c_1, gamma) = (4, 1, theta, 0), c_2(E-) = W_R:
    the c_1 = k theta case (the c_3 shift dies by W0 exactly as in the derivation). -/
theorem w6_instance_3 :
    (addCl (pairEplus 4 THETAd WRcl zeroCl 1).g2 (smulCl (-1) (pairEminus 4 THETAd WRcl zeroCl).g2)
      = smulCl 2 WRcl) ∧
    (addCl (pairEplus 4 THETAd WRcl zeroCl 1).g3 (smulCl (-1) (pairEminus 4 THETAd WRcl zeroCl).g3)
      = zeroCl) ∧
    (addCl (pairEplus 4 THETAd WRcl zeroCl 1).g4 (smulCl (-1) (pairEminus 4 THETAd WRcl zeroCl).g4)
      = zeroCl) ∧
    (weilCharge (pairC2P 1 WRcl) - weilCharge WRcl = -8 * 1) ∧
    (chiPP24 (pairEplus 4 THETAd WRcl zeroCl 1) (chDualP (pairEplus 4 THETAd WRcl zeroCl 1))
      - chiPP24 (pairEplus 4 THETAd WRcl zeroCl 1) (chDualP (pairEminus 4 THETAd WRcl zeroCl))
      = 24 * (8 * 1 * 1 - 1 * (weilCharge WRcl))) ∧
    (chiPP24 (pairEplus 4 THETAd WRcl zeroCl 1) (chDualP (pairEminus 4 THETAd WRcl zeroCl))
      - chiPP24 (pairEminus 4 THETAd WRcl zeroCl) (chDualP (pairEminus 4 THETAd WRcl zeroCl))
      = 24 * (-1 * (weilCharge WRcl))) ∧
    (chiPP24 (pairEplus 4 THETAd WRcl zeroCl 1) (chDualP (pairEplus 4 THETAd WRcl zeroCl 1))
      - chiPP24 (pairEminus 4 THETAd WRcl zeroCl) (chDualP (pairEminus 4 THETAd WRcl zeroCl))
      = 24 * (8 * 1 * 1 - 2 * 1 * (weilCharge WRcl))) := by
  decide

/-- W6 synthetic instance 4 (r, m, c_1, gamma) = (7, 3, theta, 5 vol), c_2(E-) = W_R:
    the non-carrier charge with a nonzero c_4 baseline. -/
theorem w6_instance_4 :
    (addCl (pairEplus 7 THETAd WRcl [(5, 255)] 3).g2
      (smulCl (-1) (pairEminus 7 THETAd WRcl [(5, 255)]).g2) = smulCl 6 WRcl) ∧
    (addCl (pairEplus 7 THETAd WRcl [(5, 255)] 3).g3
      (smulCl (-1) (pairEminus 7 THETAd WRcl [(5, 255)]).g3) = zeroCl) ∧
    (addCl (pairEplus 7 THETAd WRcl [(5, 255)] 3).g4
      (smulCl (-1) (pairEminus 7 THETAd WRcl [(5, 255)]).g4) = zeroCl) ∧
    (weilCharge (pairC2P 3 WRcl) - weilCharge WRcl = -8 * 3) ∧
    (chiPP24 (pairEplus 7 THETAd WRcl [(5, 255)] 3) (chDualP (pairEplus 7 THETAd WRcl [(5, 255)] 3))
      - chiPP24 (pairEplus 7 THETAd WRcl [(5, 255)] 3) (chDualP (pairEminus 7 THETAd WRcl [(5, 255)]))
      = 24 * (8 * 3 * 3 - 3 * (weilCharge WRcl))) ∧
    (chiPP24 (pairEplus 7 THETAd WRcl [(5, 255)] 3) (chDualP (pairEminus 7 THETAd WRcl [(5, 255)]))
      - chiPP24 (pairEminus 7 THETAd WRcl [(5, 255)]) (chDualP (pairEminus 7 THETAd WRcl [(5, 255)]))
      = 24 * (-3 * (weilCharge WRcl))) ∧
    (chiPP24 (pairEplus 7 THETAd WRcl [(5, 255)] 3) (chDualP (pairEplus 7 THETAd WRcl [(5, 255)] 3))
      - chiPP24 (pairEminus 7 THETAd WRcl [(5, 255)]) (chDualP (pairEminus 7 THETAd WRcl [(5, 255)]))
      = 24 * (8 * 3 * 3 - 2 * 3 * (weilCharge WRcl))) := by
  decide

/-- W6(vi) carrier instance (F, O^r) at (r, m) = (5, 1), c_2(E-) = 0: q(E-) = 0,
    chi24(End O^r) = 0 (Euler-zero), q(F) = -8 m, and the committed End-mass law
    24 * chi(End F) = 24 * 8 m^2 recovered at the q = 0 slice. -/
theorem w6_carrier_instance :
    (weilCharge zeroCl = 0) ∧
    (chiPP24 (pairEminus 5 zeroCl zeroCl zeroCl) (chDualP (pairEminus 5 zeroCl zeroCl zeroCl)) = 0) ∧
    (weilCharge (pairC2P 1 zeroCl) - weilCharge zeroCl = -8 * 1) ∧
    (chiPP24 (pairEplus 5 zeroCl zeroCl zeroCl 1) (chDualP (pairEplus 5 zeroCl zeroCl zeroCl 1))
      - chiPP24 (pairEminus 5 zeroCl zeroCl zeroCl) (chDualP (pairEminus 5 zeroCl zeroCl zeroCl))
      = 24 * (8 * 1 * 1)) := by
  decide

/-- W4(iii) detector instance (r, m) = (6, 2), probe G = E-: the 24-scaled identity
    chi24(E+ x G) - chi24(E- x G) = 12 * m * INT (W_R AND ch_2-num(G))
    (the 12 = 24/2 clearing the ch_2 conductor denominator; the only surviving cross-grade). -/
theorem w4_detector_instance :
    chiPP24 (pairEplus 6 zeroCl WRcl zeroCl 2) (pairEminus 6 zeroCl WRcl zeroCl)
      - chiPP24 (pairEminus 6 zeroCl WRcl zeroCl) (pairEminus 6 zeroCl WRcl zeroCl)
      = 12 * 2 * (intCl (wedgeCl WRcl (pairEminus 6 zeroCl WRcl zeroCl).g2)) := by
  decide

/-! ## Capstones -/

theorem pair_channel_walls_capstone_A :
    (wedgeCl (powCl THETAd 1) WRcl = []) ∧ (wedgeCl (powCl THETAd 2) WRcl = []) ∧
    (wedgeCl (powCl THETAd 3) WRcl = []) ∧
    (wedgeCl (powCl THETAd 1) WIcl = []) ∧ (wedgeCl (powCl THETAd 2) WIcl = []) ∧
    (wedgeCl (powCl THETAd 3) WIcl = []) ∧
    (intCl (powCl THETAd 4) = 24) ∧ (intCl (wedgeCl WRcl WRcl) = 8) ∧
    (intCl (wedgeCl WIcl WIcl) = 8) ∧ (intCl (wedgeCl WRcl WIcl) = 0) ∧
    (fmCl WRcl = WRcl) ∧ (fmCl WIcl = WIcl) ∧
    (fmCl (fmCl WRcl) = WRcl) ∧ (fmCl (fmCl WIcl) = WIcl) :=
  ⟨w0_ring_annihilation_WR.1, w0_ring_annihilation_WR.2.1, w0_ring_annihilation_WR.2.2,
   w0_ring_annihilation_WI.1, w0_ring_annihilation_WI.2.1, w0_ring_annihilation_WI.2.2,
   periods_reconfirm.1, periods_reconfirm.2.1, periods_reconfirm.2.2.1, periods_reconfirm.2.2.2.1,
   fm_normalization_exact.1, fm_normalization_exact.2.1,
   fm_normalization_exact.2.2.1, fm_normalization_exact.2.2.2⟩

theorem pair_channel_walls_capstone_B :
    (∀ m k i1 i2 chi : ℚ, i1 = 0 → i2 = 0 →
      chi = m * ((k * i1) + ((k^2 / 2) * i2)) → chi = 0) ∧
    (∀ m a0 a1 a2 a3 chi : ℚ, a0 = 0 → a1 = 0 → a3 = 0 →
      chi = m * (a0 + a1 + a2 + a3) → chi = m * a2) ∧
    (∀ m iWR2 qP qM : ℚ, iWR2 = 8 → qP - qM = -m * iWR2 → qP - qM = -8 * m) ∧
    (∀ m qP qM chi1 : ℚ, chi1 = -m * qP → qP - qM = -8 * m →
      chi1 = 8 * m * m - m * qM) ∧
    (∀ m qM p1 chi2 : ℚ, p1 = 0 → chi2 = m * ((p1 / 2) - qM) → chi2 = -m * qM) ∧
    (∀ m qM chi1 chi2 d : ℚ, chi1 = 8 * m * m - m * qM → chi2 = -m * qM →
      d = chi1 + chi2 → d = 8 * m * m - 2 * m * qM) ∧
    (∀ m d : ℚ, d = 8 * m * m - 2 * m * ((0:ℚ)) → d = 8 * m * m) :=
  ⟨fun m k i1 i2 chi h1 h2 hRR => pair_twist_difference_zero m k i1 i2 chi h1 h2 hRR,
   fun m a0 a1 a2 a3 chi h0 h1 h3 hRR =>
     pair_linear_detector_arithmetic m a0 a1 a2 a3 chi h0 h1 h3 hRR,
   fun m iWR2 qP qM hi hp => pair_charge_split_universal m iWR2 qP qM hi hp,
   fun m qP qM chi1 hq hs => pair_end_table_t1 m qP qM chi1 hq hs,
   fun m qM p1 chi2 hp1 hRR => pair_end_table_t2 m qM p1 chi2 hp1 hRR,
   fun m qM chi1 chi2 d h1 h2 hd => pair_end_table_t3 m qM chi1 chi2 d h1 h2 hd,
   fun m d h => carrier_end_mass m d h⟩

theorem pair_channel_walls_capstone_C :
    (addCl (pairEplus 3 zeroCl WRcl zeroCl 1).g2 (smulCl (-1) (pairEminus 3 zeroCl WRcl zeroCl).g2)
      = smulCl 2 WRcl) ∧
    (weilCharge (pairC2P 2 WRcl) - weilCharge WRcl = -8 * 2) ∧
    (addCl (pairEplus 4 THETAd WRcl zeroCl 1).g3
      (smulCl (-1) (pairEminus 4 THETAd WRcl zeroCl).g3) = zeroCl) ∧
    (addCl (pairEplus 7 THETAd WRcl [(5, 255)] 3).g4
      (smulCl (-1) (pairEminus 7 THETAd WRcl [(5, 255)]).g4) = zeroCl) ∧
    (chiPP24 (pairEplus 5 zeroCl zeroCl zeroCl 1) (chDualP (pairEplus 5 zeroCl zeroCl zeroCl 1))
      - chiPP24 (pairEminus 5 zeroCl zeroCl zeroCl) (chDualP (pairEminus 5 zeroCl zeroCl zeroCl))
      = 24 * (8 * 1 * 1)) ∧
    (chiPP24 (pairEplus 6 zeroCl WRcl zeroCl 2) (pairEminus 6 zeroCl WRcl zeroCl)
      - chiPP24 (pairEminus 6 zeroCl WRcl zeroCl) (pairEminus 6 zeroCl WRcl zeroCl)
      = 12 * 2 * (intCl (wedgeCl WRcl (pairEminus 6 zeroCl WRcl zeroCl).g2))) :=
  ⟨w6_instance_1.1, w6_instance_2.2.2.2.1, w6_instance_3.2.1, w6_instance_4.2.2.1,
   w6_carrier_instance.2.2.2, w4_detector_instance⟩

#print axioms pair_channel_walls_capstone_A
#print axioms pair_channel_walls_capstone_B
#print axioms pair_channel_walls_capstone_C
