import Mathlib

/-!
# GST Gr(2,5) PURE PAIR LATTICE CERTIFICATE

Lean shadow of the derivation
`research/derivations/GST_gr25_pure_pair_lattice_completion_and_universal_two_center_descent_law_2026_10_24.tex`
(commit 3ca08e7) and the record
`research/records/2026-10-24-gst-gr25-lattice-completion-pure-pair-and-universal-two-center-descent-law.md`.

## What is certified here (all statements are exact finite algebra)

The cohomology ring of the calibration world X = Gr(2,5) is presented by

    Q[h, s2] / (h^4 - 3 h^2 s2 + s2^2,  h^3 s2 - 2 h s2^2),

with h the Pluecker hyperplane class and s2 = c2(S^vee).  We work in
`MvPolynomial (Fin 2) Q` with `hP = X 0`, `sP = X 1`, quotient by the ideal
spanned by the two relations (`r1`, `r2`), and certify, with INTEGER-cleared
polynomials (k! * ch_k, so all coefficients are integers and every proof is
`ring`):

1. RING LAWS / PERIODS: in the quotient, h^6 = 5 h^2 s2^2, h^4 s2 = 2 h^2 s2^2,
   s2^3 = h^2 s2^2, and for alphaZ = 2 h^2 - 5 s2  (= 5 * alpha,
   alpha = (2/5) h^2 - s2):  alphaZ * h^4 = 0 and
   alphaZ^2 * h^2 = 5 h^2 s2^2, i.e. the cleared period table
   INT h^6 = 5, INT s2 h^4 = 2, INT s2^2 h^2 = INT s2^3 = 1,
   INT alpha h^4 = 0, INT alpha^2 h^2 = 1/5.
2. NAIVE PLUECKER ASSEMBLY x = 5(S + S^vee) - (O(1) + O(-1)) - 8 O:
   2 ch2(x) = 4 * alphaZ (= 20 alpha) exactly; and the grade-4
   NON-purity: 24 ch4(x) = -16 h^2 s2 + 12 s2^2 in the quotient
   (its raw form differs by 8 r1), the obstruction the lattice
   correction removes.
3. THE COMPLETED PURE PAIR at minimal scale m0 = 360:
   E+  = 351 S^vee + 5 Sym^3 S^vee + 736 S^vee(1) + 36 O(2) + O(3)
   E-  = 17 O + 51 Sym^2 S^vee + 1620 O(1) + 141 Sym^2 S^vee(1) + 9 S^vee(2)
   with equal ranks 2231 = 2231, equal c1-grade (2664 h), and
   2(ch2(E+) - ch2(E-)) = 144 alphaZ = 720 alpha = 2*360 alpha EXACTLY,
   while every higher Chern-character grade AGREEs:
   6 ch3: raw-equal; 24 ch4: equal in the quotient (difference = -3168 r1);
   120 ch5: equal in the quotient (difference = -17280 h r1 + 8640 r2);
   720 ch6: equal in the quotient (difference = (15120 s2 - 68832 h^2) r1
   + 57024 h r2).  This is the completed pure pair demanded by the Law-4
   two-center protocol.

## Context (commentary; NOT certified in this file)

Every generator Chern-character grade below is the integer-cleared raw
power-sum closed form k! * ch_k(Sym^j S^vee (x) O(i)) of the Schur bundle,
supplied as DATA (its derivation is Chern-root calculus done in the
derivation .tex and cross-checked by exact rational scripts); the theorems
verify all multiplicity arithmetic and all quotient identities by `ring`.

The following statements live OUTSIDE this file's certified scope
(scheme-level mathematics, NOT formalized here): the minimality of the
scale m0 = 360 (a K-lattice Z-basis argument), the rank/ch_1 values as
statements about actual bundles, the two-center descent law output
[D+] - [D-] = -360 alpha with W = (-1/360)([D+] - [D-]) and cl(W) = alpha,
and the component-by-component match with the proven Rees witness
(W = (2/5) sigma_2 - (3/5) sigma_{1,1} = Z_alpha).  These are proved in
the derivation .tex (LaTeX, external leaves named there) and are NOT
Lean theorems of this file.
-/

set_option maxHeartbeats 20000000
set_option maxRecDepth 1000000

namespace GSTGr25PurePairLatticeCertificate

open MvPolynomial

/-! ## 1. The presentation ring -/

abbrev Gr25Poly : Type := MvPolynomial (Fin 2) ℚ

noncomputable def hP : Gr25Poly := X (0 : Fin 2)

noncomputable def sP : Gr25Poly := X (1 : Fin 2)

/-- First relation: h^4 = 3 h^2 s2 - s2^2 (from c(S) c(Q) = 1 on Gr(2,5)). -/
noncomputable def r1 : Gr25Poly := hP^4 - 3 * hP^2 * sP + sP^2

/-- Second relation: h^3 s2 = 2 h s2^2. -/
noncomputable def r2 : Gr25Poly := hP^3 * sP - 2 * hP * sP^2

/-- The presentation ideal of H*(Gr(2,5)). -/
noncomputable def gr25Ideal : Ideal Gr25Poly :=
  Ideal.span ({r1, r2} : Set Gr25Poly)

/-- The quotient ring H*(Gr(2,5)). -/
noncomputable def quo25 (p : Gr25Poly) : Gr25Poly ⧸ gr25Ideal :=
  Ideal.Quotient.mk gr25Ideal p

/-- alphaZ = 5 * alpha where alpha = (2/5) h^2 - s2 (cleared denominator). -/
noncomputable def alphaZ : Gr25Poly := 2 * hP^2 - 5 * sP

private theorem r1_mem : r1 ∈ gr25Ideal :=
  Ideal.subset_span (Set.mem_insert _ _)

private theorem r2_mem : r2 ∈ gr25Ideal :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Membership in the presentation ideal via an explicit two-generator combo. -/
theorem mem_of_combo {x a b : Gr25Poly} (h : x = a * r1 + b * r2) :
    x ∈ gr25Ideal := by
  rw [h]
  exact gr25Ideal.add_mem
    (gr25Ideal.mul_mem_left a r1_mem)
    (gr25Ideal.mul_mem_left b r2_mem)

/-- Vanishing in the quotient via an explicit two-generator combo. -/
theorem Q_zero_of_combo {d a b : Gr25Poly} (h : d = a * r1 + b * r2) :
    quo25 d = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (mem_of_combo h)

/-! ## 2. Ring laws and the cleared period table -/

theorem rel_h4 : quo25 r1 = 0 := Q_zero_of_combo (a := 1) (b := 0) (by ring)

theorem rel_h3s : quo25 r2 = 0 := Q_zero_of_combo (a := 0) (b := 1) (by ring)

/-- h^6 = 5 h^2 s2^2 in the quotient (so INT h^6 = 5 INT h^2 s2^2, degree 1). -/
theorem top_h6 : quo25 (hP^6 - 5 * hP^2 * sP^2) = 0 :=
  Q_zero_of_combo (a := hP^2) (b := 3 * hP) (by
    simp only [r1, r2, hP, sP]; ring)

/-- h^4 s2 = 2 h^2 s2^2 in the quotient (INT s2 h^4 = 2). -/
theorem top_h4s : quo25 (hP^4 * sP - 2 * hP^2 * sP^2) = 0 :=
  Q_zero_of_combo (a := 0) (b := hP) (by
    simp only [r1, r2, hP, sP]; ring)

/-- s2^3 = h^2 s2^2 in the quotient (INT s2^3 = INT s2^2 h^2 = 1). -/
theorem top_s3 : quo25 (sP^3 - hP^2 * sP^2) = 0 :=
  Q_zero_of_combo (a := sP) (b := -hP) (by
    simp only [r1, r2, hP, sP]; ring)

/-- Cleared period: 5 * alpha * h^4 = 0 in the quotient (INT alpha h^4 = 0). -/
theorem period_alpha_h4 : quo25 (alphaZ * hP^4) = 0 :=
  Q_zero_of_combo (a := 2 * hP^2) (b := hP) (by
    simp only [r1, r2, hP, sP, alphaZ]; ring)

/-- Cleared period: (5 alpha)^2 h^2 = 5 h^2 s2^2 in the quotient, i.e.
25 alpha^2 h^2 = 5 h^2 s2^2, i.e. INT alpha^2 h^2 = 1/5. -/
theorem period_alpha2_h2 : quo25 (alphaZ^2 * hP^2 - 5 * hP^2 * sP^2) = 0 :=
  Q_zero_of_combo (a := 4 * hP^2) (b := -8 * hP) (by
    simp only [r1, r2, hP, sP, alphaZ]; ring)

/-! ## 3. Generator table: k! * ch_k, integer-cleared raw closed forms

Each entry is the exact power-sum expansion of the Schur bundle
`Sym^j S^vee (x) O(i)` on Gr(2,5) (roots r1, r2 of S^vee: r1 + r2 = h,
r1 r2 = s2), cleared by k! so all coefficients are integers. -/

/-- ch1 (c1-grade) of the generators. -/
noncomputable def ch1Sv : Gr25Poly := hP
noncomputable def ch1Sym2Sv : Gr25Poly := 3 * hP
noncomputable def ch1Sym3Sv : Gr25Poly := 6 * hP
noncomputable def ch1O1 : Gr25Poly := hP
noncomputable def ch1Sv1 : Gr25Poly := 3 * hP
noncomputable def ch1Sym2Sv1 : Gr25Poly := 6 * hP
noncomputable def ch1O2 : Gr25Poly := 2 * hP
noncomputable def ch1Sv2 : Gr25Poly := 5 * hP
noncomputable def ch1O3 : Gr25Poly := 3 * hP

/-- 2 * ch2 of the generators. -/
noncomputable def ch2Sv : Gr25Poly := hP^2 - 2 * sP
noncomputable def ch2Sym2Sv : Gr25Poly := 5 * hP^2 - 8 * sP
noncomputable def ch2Sym3Sv : Gr25Poly := 14 * hP^2 - 20 * sP
noncomputable def ch2O1 : Gr25Poly := hP^2
noncomputable def ch2Sv1 : Gr25Poly := 5 * hP^2 - 2 * sP
noncomputable def ch2Sym2Sv1 : Gr25Poly := 14 * hP^2 - 8 * sP
noncomputable def ch2O2 : Gr25Poly := 4 * hP^2
noncomputable def ch2Sv2 : Gr25Poly := 13 * hP^2 - 2 * sP
noncomputable def ch2O3 : Gr25Poly := 9 * hP^2

/-- 6 * ch3 of the generators. -/
noncomputable def ch3Sv : Gr25Poly := hP^3 - 3 * hP * sP
noncomputable def ch3Sym2Sv : Gr25Poly := 9 * hP^3 - 24 * hP * sP
noncomputable def ch3Sym3Sv : Gr25Poly := 36 * hP^3 - 90 * hP * sP
noncomputable def ch3O1 : Gr25Poly := hP^3
noncomputable def ch3Sv1 : Gr25Poly := 9 * hP^3 - 9 * hP * sP
noncomputable def ch3Sym2Sv1 : Gr25Poly := 36 * hP^3 - 48 * hP * sP
noncomputable def ch3O2 : Gr25Poly := 8 * hP^3
noncomputable def ch3Sv2 : Gr25Poly := 35 * hP^3 - 15 * hP * sP
noncomputable def ch3O3 : Gr25Poly := 27 * hP^3

/-- 24 * ch4 of the generators. -/
noncomputable def ch4Sv : Gr25Poly := hP^4 - 4 * hP^2 * sP + 2 * sP^2
noncomputable def ch4Sym2Sv : Gr25Poly := 17 * hP^4 - 64 * hP^2 * sP + 32 * sP^2
noncomputable def ch4Sym3Sv : Gr25Poly := 98 * hP^4 - 352 * hP^2 * sP + 164 * sP^2
noncomputable def ch4O1 : Gr25Poly := hP^4
noncomputable def ch4Sv1 : Gr25Poly := 17 * hP^4 - 28 * hP^2 * sP + 2 * sP^2
noncomputable def ch4Sym2Sv1 : Gr25Poly := 98 * hP^4 - 208 * hP^2 * sP + 32 * sP^2
noncomputable def ch4O2 : Gr25Poly := 16 * hP^4
noncomputable def ch4Sv2 : Gr25Poly := 97 * hP^4 - 76 * hP^2 * sP + 2 * sP^2
noncomputable def ch4O3 : Gr25Poly := 81 * hP^4

/-- 120 * ch5 of the generators. -/
noncomputable def ch5Sv : Gr25Poly := hP^5 - 5 * hP^3 * sP + 5 * hP * sP^2
noncomputable def ch5Sym2Sv : Gr25Poly := 33 * hP^5 - 160 * hP^3 * sP + 160 * hP * sP^2
noncomputable def ch5Sym3Sv : Gr25Poly := 276 * hP^5 - 1290 * hP^3 * sP + 1230 * hP * sP^2
noncomputable def ch5O1 : Gr25Poly := hP^5
noncomputable def ch5Sv1 : Gr25Poly := 33 * hP^5 - 75 * hP^3 * sP + 15 * hP * sP^2
noncomputable def ch5Sym2Sv1 : Gr25Poly := 276 * hP^5 - 800 * hP^3 * sP + 320 * hP * sP^2
noncomputable def ch5O2 : Gr25Poly := 32 * hP^5
noncomputable def ch5Sv2 : Gr25Poly := 275 * hP^5 - 325 * hP^3 * sP + 25 * hP * sP^2
noncomputable def ch5O3 : Gr25Poly := 243 * hP^5

/-- 720 * ch6 of the generators. -/
noncomputable def ch6Sv : Gr25Poly :=
  hP^6 - 6 * hP^4 * sP + 9 * hP^2 * sP^2 - 2 * sP^3
noncomputable def ch6Sym2Sv : Gr25Poly :=
  65 * hP^6 - 384 * hP^4 * sP + 576 * hP^2 * sP^2 - 128 * sP^3
noncomputable def ch6Sym3Sv : Gr25Poly :=
  794 * hP^6 - 4560 * hP^4 * sP + 6630 * hP^2 * sP^2 - 1460 * sP^3
noncomputable def ch6O1 : Gr25Poly := hP^6
noncomputable def ch6Sv1 : Gr25Poly :=
  65 * hP^6 - 186 * hP^4 * sP + 69 * hP^2 * sP^2 - 2 * sP^3
noncomputable def ch6Sym2Sv1 : Gr25Poly :=
  794 * hP^6 - 2904 * hP^4 * sP + 2016 * hP^2 * sP^2 - 128 * sP^3
noncomputable def ch6O2 : Gr25Poly := 64 * hP^6
noncomputable def ch6Sv2 : Gr25Poly :=
  793 * hP^6 - 1266 * hP^4 * sP + 189 * hP^2 * sP^2 - 2 * sP^3
noncomputable def ch6O3 : Gr25Poly := 729 * hP^6

/-! ## 4. The naive Pluecker assembly (scale 10) -/

/-- 2 * ch2(x) for x = 5(S + S^vee) - (O(1) + O(-1)) - 8 O.
S and S^vee contribute equal even grades; O(-1) contributes h^2. -/
noncomputable def ch2X : Gr25Poly :=
  5 * (ch2Sv + ch2Sv) - (ch2O1 + hP^2)

/-- 2 ch2(x) = 20 alpha exactly: the naive assembly carries the class. -/
theorem naive_ch2 : ch2X = 4 * alphaZ := by
  simp only [ch2X, ch2Sv, ch2O1, hP, sP, alphaZ]
  ring

/-- 24 * ch4(x): raw. -/
noncomputable def ch4X : Gr25Poly :=
  5 * (ch4Sv + ch4Sv) - (ch4O1 + hP^4)

/-- The grade-4 obstruction: 24 ch4(x) = -16 h^2 s2 + 12 s2^2 in the
quotient (raw difference is exactly 8 r1), so x is NOT the pure carrier. -/
theorem naive_ch4_reduced :
    quo25 (ch4X - (-16 * hP^2 * sP + 12 * sP^2)) = 0 :=
  Q_zero_of_combo (a := 8) (b := 0) (by
    simp only [ch4X, ch4Sv, ch4O1, r1, r2, hP, sP]
    ring)

/-! ## 5. The completed pure pair at minimal scale m0 = 360 -/

/-- Rank of E+ = 351 S^vee + 5 Sym^3 S^vee + 736 S^vee(1) + 36 O(2) + O(3). -/
def rankEplus : ℤ := 351 * 2 + 5 * 4 + 736 * 2 + 36 * 1 + 1 * 1

/-- Rank of E- = 17 O + 51 Sym^2 S^vee + 1620 O(1) + 141 Sym^2 S^vee(1)
+ 9 S^vee(2). -/
def rankEminus : ℤ := 17 * 1 + 51 * 3 + 1620 * 1 + 141 * 3 + 9 * 2

theorem pair_rank : rankEplus = rankEminus := by
  unfold rankEplus rankEminus
  norm_num

/-- Equal ranks: 2231 = 2231. -/
theorem pair_rank_value : rankEplus = 2231 ∧ rankEminus = 2231 := by
  unfold rankEplus rankEminus
  norm_num

/-- c1-grades of E+ and E-. -/
noncomputable def ch1Eplus : Gr25Poly :=
  351 * ch1Sv + 5 * ch1Sym3Sv + 736 * ch1Sv1 + 36 * ch1O2 + 1 * ch1O3
noncomputable def ch1Eminus : Gr25Poly :=
  17 * 0 + 51 * ch1Sym2Sv + 1620 * ch1O1 + 141 * ch1Sym2Sv1 + 9 * ch1Sv2

theorem pair_ch1 : ch1Eplus = ch1Eminus := by
  simp only [ch1Eplus, ch1Eminus, ch1Sv, ch1Sym3Sv, ch1Sv1, ch1O2, ch1O3,
    ch1Sym2Sv, ch1O1, ch1Sym2Sv1, ch1Sv2, hP, sP]
  ring

/-- 2 * ch2 grades of E+ and E-. -/
noncomputable def ch2Eplus : Gr25Poly :=
  351 * ch2Sv + 5 * ch2Sym3Sv + 736 * ch2Sv1 + 36 * ch2O2 + 1 * ch2O3
noncomputable def ch2Eminus : Gr25Poly :=
  17 * 0 + 51 * ch2Sym2Sv + 1620 * ch2O1 + 141 * ch2Sym2Sv1 + 9 * ch2Sv2

/-- THE CARRIER GRADE: 2 (ch2(E+) - ch2(E-)) = 720 alpha = 2 * 360 * alpha
exactly (raw polynomial identity).  The two-center descent law then gives
[D+] - [D-] = -360 alpha and W = (-1/360) ([D+] - [D-]) with cl(W) = alpha,
matching the Rees witness Z_alpha = (2/5) sigma_2 - (3/5) sigma_{1,1}
component-by-component. -/
theorem pair_ch2 : ch2Eplus - ch2Eminus = 144 * alphaZ := by
  simp only [ch2Eplus, ch2Eminus, ch2Sv, ch2Sym3Sv, ch2Sv1, ch2O2, ch2O3,
    ch2Sym2Sv, ch2O1, ch2Sym2Sv1, ch2Sv2, hP, sP, alphaZ]
  ring

/-- 6 * ch3 grades of E+ and E-. -/
noncomputable def ch3Eplus : Gr25Poly :=
  351 * ch3Sv + 5 * ch3Sym3Sv + 736 * ch3Sv1 + 36 * ch3O2 + 1 * ch3O3
noncomputable def ch3Eminus : Gr25Poly :=
  17 * 0 + 51 * ch3Sym2Sv + 1620 * ch3O1 + 141 * ch3Sym2Sv1 + 9 * ch3Sv2

/-- Purity, grade 3: raw equality, no quotient needed. -/
theorem pair_ch3 : ch3Eplus = ch3Eminus := by
  simp only [ch3Eplus, ch3Eminus, ch3Sv, ch3Sym3Sv, ch3Sv1, ch3O2, ch3O3,
    ch3Sym2Sv, ch3O1, ch3Sym2Sv1, ch3Sv2, hP, sP]
  ring

/-- 24 * ch4 grades of E+ and E-. -/
noncomputable def ch4Eplus : Gr25Poly :=
  351 * ch4Sv + 5 * ch4Sym3Sv + 736 * ch4Sv1 + 36 * ch4O2 + 1 * ch4O3
noncomputable def ch4Eminus : Gr25Poly :=
  17 * 0 + 51 * ch4Sym2Sv + 1620 * ch4O1 + 141 * ch4Sym2Sv1 + 9 * ch4Sv2

/-- Purity, grade 4: the difference is exactly -3168 r1, so it vanishes in
the cohomology ring. -/
theorem pair_ch4 : quo25 (ch4Eplus - ch4Eminus) = 0 :=
  Q_zero_of_combo (a := -3168) (b := 0) (by
    simp only [ch4Eplus, ch4Eminus, ch4Sv, ch4Sym3Sv, ch4Sv1, ch4O2, ch4O3,
      ch4Sym2Sv, ch4O1, ch4Sym2Sv1, ch4Sv2, r1, r2, hP, sP]
    ring)

/-- 120 * ch5 grades of E+ and E-. -/
noncomputable def ch5Eplus : Gr25Poly :=
  351 * ch5Sv + 5 * ch5Sym3Sv + 736 * ch5Sv1 + 36 * ch5O2 + 1 * ch5O3
noncomputable def ch5Eminus : Gr25Poly :=
  17 * 0 + 51 * ch5Sym2Sv + 1620 * ch5O1 + 141 * ch5Sym2Sv1 + 9 * ch5Sv2

/-- Purity, grade 5: the difference is exactly -17280 h r1 + 8640 r2. -/
theorem pair_ch5 : quo25 (ch5Eplus - ch5Eminus) = 0 :=
  Q_zero_of_combo (a := -17280 * hP) (b := 8640) (by
    simp only [ch5Eplus, ch5Eminus, ch5Sv, ch5Sym3Sv, ch5Sv1, ch5O2, ch5O3,
      ch5Sym2Sv, ch5O1, ch5Sym2Sv1, ch5Sv2, r1, r2, hP, sP]
    ring)

/-- 720 * ch6 grades of E+ and E-. -/
noncomputable def ch6Eplus : Gr25Poly :=
  351 * ch6Sv + 5 * ch6Sym3Sv + 736 * ch6Sv1 + 36 * ch6O2 + 1 * ch6O3
noncomputable def ch6Eminus : Gr25Poly :=
  17 * 0 + 51 * ch6Sym2Sv + 1620 * ch6O1 + 141 * ch6Sym2Sv1 + 9 * ch6Sv2

/-- Purity, grade 6: the difference is exactly
(15120 s2 - 68832 h^2) r1 + 57024 h r2. -/
theorem pair_ch6 : quo25 (ch6Eplus - ch6Eminus) = 0 :=
  Q_zero_of_combo (a := 15120 * sP - 68832 * hP^2) (b := 57024 * hP) (by
    simp only [ch6Eplus, ch6Eminus, ch6Sv, ch6Sym3Sv, ch6Sv1, ch6O2, ch6O3,
      ch6Sym2Sv, ch6O1, ch6Sym2Sv1, ch6Sv2, r1, r2, hP, sP]
    ring)

/-! ## 6. Capstones -/

/-- The completed pure pair certificate: equal ranks, equal c1-grade,
carrier grade 720 alpha, and purity in every higher grade. -/
theorem gr25_pure_pair_certificate :
    rankEplus = rankEminus
    ∧ ch1Eplus = ch1Eminus
    ∧ ch2Eplus - ch2Eminus = 144 * alphaZ
    ∧ ch3Eplus = ch3Eminus
    ∧ quo25 (ch4Eplus - ch4Eminus) = 0
    ∧ quo25 (ch5Eplus - ch5Eminus) = 0
    ∧ quo25 (ch6Eplus - ch6Eminus) = 0 :=
  ⟨pair_rank, pair_ch1, pair_ch2, pair_ch3, pair_ch4, pair_ch5, pair_ch6⟩

/-- The cleared period-and-relation certificate of the calibration world. -/
theorem gr25_ring_period_certificate :
    quo25 r1 = 0
    ∧ quo25 r2 = 0
    ∧ quo25 (hP^6 - 5 * hP^2 * sP^2) = 0
    ∧ quo25 (hP^4 * sP - 2 * hP^2 * sP^2) = 0
    ∧ quo25 (sP^3 - hP^2 * sP^2) = 0
    ∧ quo25 (alphaZ * hP^4) = 0
    ∧ quo25 (alphaZ^2 * hP^2 - 5 * hP^2 * sP^2) = 0 :=
  ⟨rel_h4, rel_h3s, top_h6, top_h4s, top_s3, period_alpha_h4, period_alpha2_h2⟩

/-- The naive assembly and its grade-4 obstruction. -/
theorem gr25_naive_assembly_certificate :
    ch2X = 4 * alphaZ
    ∧ quo25 (ch4X - (-16 * hP^2 * sP + 12 * sP^2)) = 0 :=
  ⟨naive_ch2, naive_ch4_reduced⟩

#print axioms gr25_pure_pair_certificate
#print axioms gr25_ring_period_certificate
#print axioms gr25_naive_assembly_certificate

end GSTGr25PurePairLatticeCertificate
