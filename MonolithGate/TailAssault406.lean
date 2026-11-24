import MonolithGate.GSTFourPowerHappyProvider
import MonolithGate.GSTFourPowerNo22Magnitude
import MonolithGate.GSTFourPowerDirectNo22
import MonolithGate.GSTFourPowerDirectAdditionCarry
import MonolithGate.GSTInfiniteFourPowerNavigation
import MonolithGate.FinalVerdict406

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE TAIL ASSAULT — the climb's tail, cornered from three sides

THE composition BOSS ordered: multiple files' CI-green laws combined into
COMPLETE NEW THEOREMS that no single file contains.  The target is the
mission's last remaining hypothesis — the climb's tail, the statement that
every exponent above the base owns a physical Happy row — and this file
corners it from three independent sides:

* **§1 THE TRIT-TREE LAW** — the climb restated as the exponent-trit tree:
  through the chamber's exact prefix-killing-trit equivalence
  (`GSTFourPowerExponentTritObstruction.row_common_two_iff_prefix_killing_trit`)
  and the Happy provider (`GSTFourPowerHappyProvider`), the Happy rows of
  `4^K` are exactly the bad edges of `K`'s own ternary tree.
* **§2 THE BAND LATTICE** — four kernel-certified survivor tables
  (mod 27, 81, 243, 729): every residue class outside the level-six
  survivor table fires by row six.  Each table is one kernel decision
  over all classes; every fired class was two-method verified (exact
  big-int expansion and modular arithmetic) before generation.
* **§3 THE NO-22 FACE** — the counterexample's digit side: the chamber's
  No-22 isolation laws (`GSTFourPowerDirectNo22`) adapted to rows at
  least three force the ternary suffix `4^K / 27` to be No-22, and the
  magnitude law (`GSTFourPowerNo22Magnitude.no22_nine_power_bound`)
  caps it at the sharp 7/8 density constant.
* **§4 THE COLLISION** — the counterexample's COMPLETE forced structure
  in one theorem: Band-I tree-survivor class AND No-22 suffix AND the
  magnitude cap.  Five files' laws, one statement.
* **§5 THE EXTENDED BASE** — the kernel-certified climb base extended
  from five hundred to one thousand five hundred: 1000 explicit
  witnesses, exact kernel arithmetic on powers up to 3002 bits, each
  two-method verified before generation.
* **§6 THE SHARPENED VERDICT** — the universal Erdos #406 verdict from
  the tail above one thousand five hundred alone.

The engine never stops; it never lies.
-/

namespace GSTTailAssault406

open GSTFourPowerDirectResidue
open GSTFourPowerExponentTritObstruction

/-! ## §1 The trit-tree law — the climb as the exponent's own tree -/

/-- **THE BAD EDGE, COMPUTABLE.**  The level-`p` bad edge of the
exponent-trit tree: the prefix pair's power digits align at row `p+1`
and the `p`-th exponent trit is the unique killing trit. -/
def treeBad (K p : Nat) : Bool :=
    (digit3 (4^(K % 3^p)) (p+1) == digit3 (4^((K % 3^p)+1)) (p+1)) &&
    (K / 3^p % 3 == 2 - digit3 (4^(K % 3^p)) (p+1))

/-- **THE HAPPY FACE READ AS DIGITS.**  A physical Happy cell of `4^K`
at row `p` is exactly a shared ternary digit-two of the consecutive
powers `4^K` and `4^(K+1)` — the carry condition dissolves into the
x4 digit law.  Self-proved through the addition-carry engine. -/
theorem consecutive_digits_of_happy (K p : Nat)
    (h : GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)) :
    digit3 (4^K) p = 2 ∧ digit3 (4^(K+1)) p = 2 := by
  obtain ⟨hd, hc⟩ := h
  have hd' : digit3 (4^K) p = 2 := by
    simpa [GSTCanonicalTailStateIso.digit3, GSTFourPowerDirectResidue.digit3]
      using hd
  refine ⟨hd', ?_⟩
  have h4 : digit3 (4 * (4^K)) p = (digit3 (4^K) p + directCarry4 (4^K) p) % 3 :=
    digit3_four_mul (4^K) p
  have hc' : directCarry4 (4^K) p = 0 ∨ directCarry4 (4^K) p = 3 := by
    have hbr : (4 * ((4^K : Nat) % 3^p)) / 3^p = 0 ∨
        (4 * ((4^K : Nat) % 3^p)) / 3^p = 3 := by
      simpa [GSTCanonicalTailStateIso.carry4,
        GSTFourPowerDirectAdditionCarry.directCarry4] using hc
    exact hbr
  rcases hc' with h0 | h3
  · rw [h0, hd'] at h4
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h4
  · rw [h3, hd'] at h4
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h4

/-- The bad edge is exactly the prefix-killing-trit pair of the chamber's
equivalence. -/
theorem treeBad_iff_prefix_killing_trit (K p : Nat) :
    (treeBad K p = true) ↔
      (digit3 (4^(exponentPrefix K p)) (p+1) =
          digit3 (4^((exponentPrefix K p)+1)) (p+1) ∧
       exponentTrit K p =
          2 - digit3 (4^(exponentPrefix K p)) (p+1)) := by
  unfold treeBad exponentPrefix exponentTrit
  simp only [Bool.and_eq_true, beq_iff_eq]

/-- **THE TRIT CONGRUENCE.**  The `p`-th exponent trit sees only the
exponent modulo `3^(p+1)`. -/
theorem trit_congr (K r p : Nat) (h : K % 3^(p+1) = r % 3^(p+1)) :
    K / 3^p % 3 = r / 3^p % 3 := by
  have hpos : 0 < 3^p := Nat.pow_pos (by decide)
  obtain ⟨u, hu⟩ : ∃ u, K = 3^(p+1) * u + r % 3^(p+1) := by
    refine ⟨K / 3^(p+1), ?_⟩
    have hstd := Nat.div_add_mod K (3^(p+1))
    rw [h] at hstd
    rw [Nat.mul_comm] at hstd
    exact hstd.symm
  obtain ⟨w, hw⟩ : ∃ w, r = 3^(p+1) * w + r % 3^(p+1) := by
    refine ⟨r / 3^(p+1), ?_⟩
    have hstd := Nat.div_add_mod r (3^(p+1))
    rw [Nat.mul_comm] at hstd
    exact hstd.symm
  have hpp : ∀ x : Nat,
      (3^(p+1) * x + r % 3^(p+1)) / 3^p % 3
        = (r % 3^(p+1)) / 3^p % 3 := by
    intro x
    have hA : 3^(p+1) * x = (3 * x) * 3^p := by
      rw [Nat.pow_succ]
      ring
    rw [hA, Nat.add_mul_div_left _ _ hpos, Nat.mul_comm (3 * x),
      Nat.add_mul_mod_self_right]
  calc K / 3^p % 3
      = (3^(p+1) * u + r % 3^(p+1)) / 3^p % 3 := by rw [hu]
    _ = (3^(p+1) * w + r % 3^(p+1)) / 3^p % 3 := by rw [hpp u, hpp w]
    _ = r / 3^p % 3 := by rw [hw]

/-- **THE TREE'S CONGRUENCE LAW.**  The bad edge at level `p` sees only the
exponent modulo `3^(p+1)`: two exponents congruent there own the same edge. -/
theorem treeBad_congr (K r p : Nat)
    (h : K % 3^(p+1) = r % 3^(p+1)) :
    treeBad K p = treeBad r p := by
  have hp5 : 3^p ∣ 3^(p+1) := by
    rw [Nat.pow_succ]
    exact dvd_mul_right (3^p) 3
  have hKp : K % 3^p = (K % 3^(p+1)) % 3^p :=
    (Nat.mod_mod_of_dvd hp5 K).symm
  have hrp : r % 3^p = (r % 3^(p+1)) % 3^p :=
    (Nat.mod_mod_of_dvd hp5 r).symm
  unfold treeBad
  rw [hKp, hrp, h, trit_congr K r p h]

/-- **THE FIRE DELIVERY.**  A bad tree edge at level at least two delivers
the row-`p+1` common-two witness outright. -/
theorem commonTwoGeThree_of_treeBad (K p : Nat) (hp : 2 ≤ p)
    (h : treeBad K p = true) :
    GSTFourPowerHappyProvider.CommonTwoGeThree K :=
  GSTFourPowerHappyProvider.commonTwoGeThree_of_prefix_killing_trit K p hp
    ((treeBad_iff_prefix_killing_trit K p).1 h).1
    ((treeBad_iff_prefix_killing_trit K p).1 h).2

/-- **THE CLIMB AS THE TREE.**  `4^K` owns a physical Happy row at a
coordinate at least three exactly when `K`'s own ternary tree owns a bad
edge at some level at least two.  The chamber's provider, the obstruction
engine, and the addition-carry digit law, composed into one equivalence. -/
theorem happy_iff_treeBad (K : Nat) :
    (∃ p : Nat, 3 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)) ↔
    (∃ p : Nat, 2 ≤ p ∧ treeBad K p = true) := by
  constructor
  · rintro ⟨p, hp3, hHappy⟩
    have hp2 : 2 ≤ p := by omega
    refine ⟨p - 1, by omega, ?_⟩
    have hrow := consecutive_digits_of_happy K p hHappy
    have hstep : (p - 1) + 1 = p := by omega
    have heng := (row_common_two_iff_prefix_killing_trit K (p-1)).1
      (by rw [hstep]; exact hrow)
    exact (treeBad_iff_prefix_killing_trit K (p-1)).2 heng
  · intro ⟨p, hp, hbad⟩
    exact GSTFourPowerHappyProvider.commonTwoGeThree_to_physical_happy_ge_three K
      (commonTwoGeThree_of_treeBad K p hp hbad)

/-! ## §2 The band lattice — four kernel-certified survivor tables -/

/-- Level-three survivor classes (mod 27): the residues whose tree paths
dodge every bad edge through level two. -/
def tailS3 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 20, 21, 22, 23, 24, 26]

/-- Level-four survivor classes (mod 81). -/
def tailS4 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 43, 44, 47, 48, 49, 50, 59, 60, 61, 62, 63, 64, 65, 67, 69, 70, 71, 74, 75, 77, 78, 80]

/-- Level-five survivor classes (mod 243). -/
def tailS5 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 43, 44, 47, 49, 50, 59, 60, 62, 63, 64, 65, 67, 69, 74, 75, 80, 81, 82, 83, 84, 88, 92, 93, 94, 96, 97, 98, 102, 103, 104, 105, 107, 108, 109, 110, 111, 112, 113, 118, 119, 120, 121, 125, 128, 129, 130, 131, 140, 141, 142, 143, 144, 148, 150, 151, 152, 155, 156, 158, 159, 161, 165, 166, 167, 168, 169, 171, 172, 173, 177, 178, 183, 184, 186, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 206, 209, 210, 211, 212, 222, 223, 224, 225, 226, 227, 231, 232, 233, 236, 237, 239, 240, 242]

/-- Level-six survivor classes (mod 729): the Band-I entrants. -/
def tailS6 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 15, 16, 17, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 39, 40, 43, 44, 47, 49, 50, 59, 60, 62, 63, 64, 65, 67, 69, 75, 81, 82, 83, 84, 88, 92, 93, 94, 96, 97, 98, 102, 103, 104, 105, 107, 108, 109, 119, 120, 121, 125, 140, 141, 144, 148, 152, 155, 156, 158, 159, 161, 165, 166, 167, 168, 171, 177, 183, 184, 186, 188, 189, 190, 191, 192, 193, 194, 196, 197, 198, 199, 200, 201, 202, 205, 206, 209, 210, 211, 212, 223, 224, 225, 226, 232, 233, 236, 237, 239, 240, 242, 243, 244, 245, 246, 247, 248, 249, 250, 252, 253, 254, 259, 260, 265, 266, 267, 272, 273, 274, 275, 276, 277, 278, 279, 280, 282, 283, 286, 287, 290, 293, 302, 305, 306, 307, 308, 310, 312, 317, 318, 323, 324, 325, 326, 327, 335, 336, 337, 341, 345, 346, 347, 348, 350, 352, 353, 354, 355, 356, 361, 362, 363, 364, 371, 372, 373, 374, 383, 384, 385, 386, 387, 391, 393, 394, 395, 401, 402, 404, 411, 412, 414, 415, 416, 420, 421, 426, 427, 429, 431, 432, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 448, 449, 453, 454, 465, 466, 467, 469, 470, 474, 475, 476, 479, 482, 483, 490, 491, 492, 493, 495, 496, 497, 498, 499, 501, 502, 508, 509, 510, 512, 513, 514, 515, 516, 517, 519, 520, 521, 522, 523, 529, 530, 533, 535, 536, 545, 546, 550, 551, 553, 555, 560, 561, 566, 567, 568, 569, 570, 574, 579, 580, 582, 583, 584, 588, 590, 591, 593, 594, 595, 596, 597, 598, 599, 604, 605, 607, 611, 614, 615, 616, 617, 626, 627, 628, 629, 630, 634, 636, 637, 638, 641, 642, 644, 647, 651, 652, 653, 654, 655, 657, 658, 659, 663, 664, 669, 670, 675, 676, 677, 678, 680, 681, 682, 686, 687, 691, 695, 696, 697, 698, 708, 709, 710, 711, 712, 713, 717, 718, 719, 722, 723, 725, 726, 728]

/-- **BAND THREE.**  Every residue class mod 27 outside the survivor table
owns a level-two bad edge — the class fires at row three.  One kernel
decision over all 27 classes. -/
theorem band3_scan : ∀ r : Nat, r < 27 →
    (tailS3.contains r = true ∨ treeBad r 2 = true) := by
  intro r hr
  have hdec : (List.all (List.range 27) (fun r =>
      (tailS3.contains r) || treeBad r 2)) = true := by decide
  have h := (List.all_eq_true.mp hdec) r (List.mem_range.2 hr)
  simpa using h

/-- **BAND FOUR.**  Every residue class mod 81 outside the survivor table
owns a bad edge by level three. -/
theorem band4_scan : ∀ r : Nat, r < 81 →
    (tailS4.contains r = true ∨ treeBad r 2 = true ∨ treeBad r 3 = true) := by
  intro r hr
  have hdec : (List.all (List.range 81) (fun r =>
      (tailS4.contains r) || (treeBad r 2 || treeBad r 3))) = true := by
    decide
  have h := (List.all_eq_true.mp hdec) r (List.mem_range.2 hr)
  simpa using h

/-- **BAND FIVE.**  Every residue class mod 243 outside the survivor table
owns a bad edge by level four. -/
theorem band5_scan : ∀ r : Nat, r < 243 →
    (tailS5.contains r = true ∨ treeBad r 2 = true ∨ treeBad r 3 = true ∨
      treeBad r 4 = true) := by
  intro r hr
  have hdec : (List.all (List.range 243) (fun r =>
      (tailS5.contains r) ||
      (treeBad r 2 || (treeBad r 3 || treeBad r 4)))) = true := by
    decide
  have h := (List.all_eq_true.mp hdec) r (List.mem_range.2 hr)
  simpa using h

/-- **BAND SIX.**  Every residue class mod 729 outside the survivor table
owns a bad edge by level five — 377 fired classes, each two-method
verified (exact big-int ternary expansion and modular arithmetic) before
this file was generated.  The kernel itself re-verifies every one. -/
theorem band6_scan : ∀ r : Nat, r < 729 →
    (tailS6.contains r = true ∨ treeBad r 2 = true ∨ treeBad r 3 = true ∨
      treeBad r 4 = true ∨ treeBad r 5 = true) := by
  intro r hr
  have hdec : (List.all (List.range 729) (fun r =>
      (tailS6.contains r) ||
      (treeBad r 2 || (treeBad r 3 || (treeBad r 4 || treeBad r 5))))) = true
    := by decide
  have h := (List.all_eq_true.mp hdec) r (List.mem_range.2 hr)
  simpa using h

/-- **THE BAND-SIX FIRE LAW.**  Every exponent whose class mod 729 lies
outside the level-six survivor table owns its common-two row by row six:
the band scan, the congruence law, and the provider, composed. -/
theorem commonTwoGeThree_of_band6 (K : Nat)
    (hout : tailS6.contains (K % 729) = false) :
    GSTFourPowerHappyProvider.CommonTwoGeThree K := by
  have hr729 : K % 729 < 729 := Nat.mod_lt _ (by norm_num)
  rcases band6_scan (K % 729) hr729 with hS | hT
  · exact absurd hS hout
  · have hfire : ∃ p : Nat, 2 ≤ p ∧ p ≤ 5 ∧ treeBad (K % 729) p = true := by
      rcases hT with h2 | h3
      · exact ⟨2, by norm_num, by norm_num, h2⟩
      · rcases h3 with h3 | h4
        · exact ⟨3, by norm_num, by norm_num, h3⟩
        · rcases h4 with h4 | h5
          · exact ⟨4, by norm_num, by norm_num, h4⟩
          · exact ⟨5, by norm_num, by norm_num, h5⟩
    obtain ⟨p, hp2, hp5, hbad⟩ := hfire
    have hdvd : 3^(p+1) ∣ 729 := by
      have h6 : (3:Nat)^6 = 729 := by norm_num
      have hsplit : (3:Nat)^6 = 3^(p+1) * 3^(5-p) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [h6, hsplit]
      exact dvd_mul_right _ _
    have hcon : treeBad K p = treeBad (K % 729) p :=
      treeBad_congr K (K % 729) p (Nat.mod_mod_of_dvd hdvd K).symm
    rw [hcon] at hbad
    exact commonTwoGeThree_of_treeBad K p hp2 hbad

/-- **THE ROW-SIX HAPPY LAW.**  The band-six fire law delivered as the
climb's own physical statement. -/
open GSTU2DEventTransport in
open GSTCanonicalSevenAxisBridge in
theorem happy_ge_three_of_band6 (K : Nat)
    (hout : tailS6.contains (K % 729) = false) :
    ∃ p : Nat, 3 ≤ p ∧
      HappyCell (carry4 (4^K) p) (digit3 (4^K) p) :=
  GSTFourPowerHappyProvider.commonTwoGeThree_to_physical_happy_ge_three K
    (commonTwoGeThree_of_band6 K hout)

/-! ## §3 The No-22 face — the counterexample's digit side, rows ≥ 3 -/

open GSTFourPowerDirectAdditionCarry

/-- **THE ISOLATED TWO, ROWS AT LEAST THREE.**  Under a counterexample to
the row-three-or-higher common-two statement, every source digit two at a
row at least three forces the next binary carry bit to one.  The chamber's
isolation law, adapted from rows at least one to rows at least three. -/
theorem source_two_forces_next_binary_one_of_no_common_ge_three
    (K p : Nat) (hp : 3 ≤ p)
    (hNo : ¬ GSTFourPowerHappyProvider.CommonTwoGeThree K)
    (h2 : digit3 (4^K) p = 2) :
    binaryCarry (4^K) (p+1) = 1 := by
  have hp1 : 1 ≤ p := by omega
  have hbnext : binaryCarry (4^K) (p+1) < 2 :=
    binaryCarry_lt_two (4^K) (p+1) (by omega)
  have hrec := binaryCarry_forward_exact (4^K) p hp1
  rw [h2] at hrec
  have hprev := digit3_lt_three (4^K) (p-1)
  have hbit := binaryCarry_lt_two (4^K) p hp1
  have hnz : binaryCarry (4^K) (p+1) ≠ 0 := by
    intro hz
    have hq : (2 + digit3 (4^K) (p-1) + binaryCarry (4^K) p) / 3 = 0 := by
      rw [← hrec, hz]
    have hzero :=
      (GSTFourPowerDirectNo22.next_binary_zero_after_two_iff
        (digit3 (4^K) (p-1)) (binaryCarry (4^K) p) hprev hbit).1 hq
    have hcommon :=
      (common_two_row_iff_forbidden_edges (4^K) p hp1).2
        ⟨h2, Or.inl hzero⟩
    apply hNo
    refine ⟨p, hp, hcommon.1, ?_⟩
    simpa [pow_succ, Nat.mul_comm] using hcommon.2
  omega

/-- **THE ADAPTED NO-22 LAW.**  A counterexample to the row-three-or-higher
common-two statement has no adjacent ternary `22` pair at any row at least
three. -/
theorem no_common_ge_three_forbids_source_22
    (K p : Nat) (hp : 3 ≤ p)
    (hNo : ¬ GSTFourPowerHappyProvider.CommonTwoGeThree K)
    (h2 : digit3 (4^K) p = 2) :
    digit3 (4^K) (p+1) ≠ 2 := by
  intro hnext
  have hb1 :=
    source_two_forces_next_binary_one_of_no_common_ge_three K p hp hNo h2
  have hprev2 : digit3 (4^K) ((p+1)-1) = 2 := by simpa using h2
  have hcommon :=
    (common_two_row_iff_forbidden_edges (4^K) (p+1) (by omega)).2
      ⟨hnext, Or.inr ⟨hprev2, hb1⟩⟩
  apply hNo
  refine ⟨p+1, by omega, hcommon.1, ?_⟩
  simpa [pow_succ, Nat.mul_comm] using hcommon.2

/-- **THE NO-22 SUFFIX.**  A counterexample's whole ternary suffix beyond
row three is No-22: the chamber's suffix-stable ternary language, entered
through the adapted isolation law. -/
theorem no22_suffix_of_no_common_ge_three (K : Nat)
    (hNo : ¬ GSTFourPowerHappyProvider.CommonTwoGeThree K) :
    GSTFourPowerNo22Magnitude.No22Ternary (4^K / 27) := by
  intro j h22
  have h0 : digit3 (4^K / 27) j = digit3 (4^K) (3+j) :=
    GSTFourPowerNo22Magnitude.digit3_div_three_pow_shift (4^K) 3 j
  have h1 : digit3 (4^K / 27) (j+1) = digit3 (4^K) (3+(j+1)) :=
    GSTFourPowerNo22Magnitude.digit3_div_three_pow_shift (4^K) 3 (j+1)
  rw [h0, h1] at h22
  have hp3 : 3 ≤ j+3 := by omega
  have hfirst : digit3 (4^K) (j+3) = 2 := by
    simpa [Nat.add_comm, Nat.add_left_comm] using h22.1
  have hsecond : digit3 (4^K) (j+3+1) = 2 := by
    simpa [Nat.add_comm, Nat.add_left_comm] using h22.2
  exact no_common_ge_three_forbids_source_22 K (j+3) hp3 hNo hfirst hsecond

/-- **THE MAGNITUDE FACE.**  The counterexample's suffix obeys the chamber's
sharp finite magnitude law: the 7/8 density constant, extremal at the
alternating word 2121...21. -/
theorem magnitude_face_of_no_common (K m : Nat)
    (hNo : ¬ GSTFourPowerHappyProvider.CommonTwoGeThree K)
    (hX : 4^K / 27 < 9^m) :
    8 * (4^K / 27) ≤ 7 * (9^m - 1) :=
  GSTFourPowerNo22Magnitude.no22_nine_power_bound (4^K / 27) m hX
    (no22_suffix_of_no_common_ge_three K hNo)

/-! ## §4 The collision — the counterexample's complete forced structure -/

/-- **THE COLLISION THEOREM.**  Five files' laws in one statement: any
counterexample to the climb's content above the extended base is
simultaneously (1) a Band-I tree-survivor — its class mod 729 lies in the
level-six survivor table, the exact complement of the 377 kernel-fired
classes; (2) the owner of a No-22 ternary suffix beyond row three; and
(3) bounded by the sharp 7/8 magnitude law on every nine-power window.
The remaining content of Erdos #406 is the impossibility of this triple
collision. -/
theorem tail_counterexample_collision (K : Nat) (hK : 501 ≤ K)
    (hNo : ¬ GSTFourPowerHappyProvider.CommonTwoGeThree K) :
    (tailS6.contains (K % 729) = true) ∧
    GSTFourPowerNo22Magnitude.No22Ternary (4^K / 27) ∧
    (∀ m : Nat, 4^K / 27 < 9^m → 8 * (4^K / 27) ≤ 7 * (9^m - 1)) := by
  refine ⟨?_, no22_suffix_of_no_common_ge_three K hNo,
    fun m hX => magnitude_face_of_no_common K m hNo hX⟩
  by_contra hout
  have hout' : tailS6.contains (K % 729) = false := by
    simpa using hout
  exact hNo (commonTwoGeThree_of_band6 K hout')

/-- **THE COLLISION'S SHARPENED FACE.**  A counterexample above the
extended base sits in a level-six survivor class AND its suffix magnitude
is capped in the window of its own trit length: the two sides of the
collision, stated on the same window. -/
theorem tail_collision_magnitude_window (K : Nat) (hK : 501 ≤ K)
    (hNo : ¬ GSTFourPowerHappyProvider.CommonTwoGeThree K)
    (m : Nat) (hX : 4^K / 27 < 9^m) :
    tailS6.contains (K % 729) = true ∧
      8 * (4^K / 27) ≤ 7 * (9^m - 1) :=
  ⟨(tail_counterexample_collision K hK hNo).1,
    (tail_counterexample_collision K hK hNo).2.2 m hX]

/-! ## §5 The extended base — the climb kernel-certified to 1500 -/

open GSTU2DEventTransport in
open GSTCanonicalSevenAxisBridge in
/-- **THE CLIMB'S EXTENDED BASE.**  Every exponent from 501 through 1500
owns its physical Happy row at a ternary coordinate at least three — 1000
explicit witnesses, each verified by exact kernel arithmetic on powers up
to 3002 bits, each two-method verified (exact big-int expansion and
modular arithmetic) before generation. -/
theorem erdos406_climb_base_ext :
    ∀ K : Nat, 501 ≤ K → K ≤ 1500 →
      ∃ p : Nat, 3 ≤ p ∧
        HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  intro K hK1 hK2
  interval_cases K
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨26, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨21, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨24, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨23, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨35, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨22, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨27, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨21, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨21, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨26, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨32, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨30, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨23, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨21, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨21, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨25, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨21, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨27, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨25, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨30, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨25, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨25, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨22, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨35, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨23, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨22, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨31, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨38, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨28, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨20, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨28, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨27, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨23, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨19, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨16, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨14, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨13, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨10, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨11, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨17, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨7, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨18, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨31, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨15, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨6, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨12, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨27, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨32, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨9, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨5, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨8, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨3, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩
  exact ⟨4, by decide, by simp only [HappyCell, carry4, digit3]; decide⟩

/-- **THE FULL BASE TO 1500** — the original 493-witness base composed
with the 1000-witness extension. -/
open GSTU2DEventTransport in
open GSTCanonicalSevenAxisBridge in
theorem erdos406_climb_base_1500 :
    ∀ K : Nat, 8 ≤ K → K ≤ 1500 →
      ∃ p : Nat, 3 ≤ p ∧
        HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  intro K hK8 hK1500
  rcases Nat.lt_or_ge K 501 with h | h
  · exact erdos406_climb_base K hK8 (by omega)
  · exact erdos406_climb_base_ext K (by omega) (by omega)

/-! ## §6 The sharpened verdict — the whole problem above 1500 -/

/-- **THE MISSION'S SHARPEST STATEMENT, SHARPENED.**  Erdos #406's
universal verdict follows from the climb's tail above one thousand five
hundred alone: the base band is kernel-certified to 1500, the composition
is machine-proven, and the entire remaining mathematical content of the
problem is the single named hypothesis — now with its forced structure
exposed by the collision theorem. -/
theorem erdos406_universal_verdict_of_tail_1500
    (htail : ∀ K : Nat, 1500 < K →
      ∃ p : Nat, 3 ≤ p ∧
        HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false :=
  erdos406_universal_verdict_of_climb
    (fun K hK8 => by
      rcases Nat.lt_or_ge K 1501 with h | h
      · exact erdos406_climb_base_1500 K hK8 (by omega)
      · exact htail K (by omega))

/-- **THE TAIL HYPOTHESIS'S OWN FACE.**  The sharpened tail hypothesis is
exactly the statement that no exponent above 1500 realizes the collision
structure: the trit-tree law, the band lattice, the No-22 face, and the
extended base, assembled as one implication. -/
theorem tail_1500_of_no_collision
    (h : ∀ K : Nat, 1500 < K →
      ¬ (tailS6.contains (K % 729) = true ∧
        GSTFourPowerNo22Magnitude.No22Ternary (4^K / 27))) :
    ∀ K : Nat, 1500 < K →
      GSTFourPowerHappyProvider.CommonTwoGeThree K := by
  intro K hK hnc
  by_contra hNo
  have hcol := tail_counterexample_collision K (by omega) hNo
  exact hnc K hK ⟨hcol.1, hcol.2.1⟩

/-! ## §7 Receipts -/

#print axioms consecutive_digits_of_happy
#print axioms treeBad_iff_prefix_killing_trit
#print axioms trit_congr
#print axioms treeBad_congr
#print axioms commonTwoGeThree_of_treeBad
#print axioms happy_iff_treeBad
#print axioms band3_scan
#print axioms band4_scan
#print axioms band5_scan
#print axioms band6_scan
#print axioms commonTwoGeThree_of_band6
#print axioms happy_ge_three_of_band6
#print axioms source_two_forces_next_binary_one_of_no_common_ge_three
#print axioms no_common_ge_three_forbids_source_22
#print axioms no22_suffix_of_no_common_ge_three
#print axioms magnitude_face_of_no_common
#print axioms tail_counterexample_collision
#print axioms tail_collision_magnitude_window
#print axioms erdos406_climb_base_ext
#print axioms erdos406_climb_base_1500
#print axioms erdos406_universal_verdict_of_tail_1500
#print axioms tail_1500_of_no_collision

#eval "TAIL_ASSAULT_GREEN"

end GSTTailAssault406
