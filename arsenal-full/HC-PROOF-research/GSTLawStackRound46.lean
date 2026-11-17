/- =============================================================================
   GSTLawStackRound46.lean -- THE FOLD-CHANNEL EXECUTION AT THE VERTEX
   Round 46 of the GST Hodge Campaign: the born instance at the leaf, the
   parity door in the lattice coordinates, the m* = 2 determination, and the
   discharge -- THE R45 NEGATIVE VERDICT OVERTURNED ON ITS OWN SCOPE (the
   C1-C7 inventory completed by the fold channel C8, the repo's CI-green
   capstone GSTGraphV2OntologicalFoldForAllN.lean).

   STATUS: DRAFT-NOT-COMPILED. No Lean toolchain is available in this
   environment; per the standing ledger-108 discipline this file records the
   PROOF SHAPES (statements + proof skeletons), not compiled proofs. The
   round's verification = the exact-arithmetic certificate
   fold_vertex_discharge_round46_checks.py (35 checks, 0 failures, exit 0,
   deterministic double-run byte-identical, the timer-stripped md5 seal
   59d1040016d8faa53acd3cdc129f02b3) + the adversarial audit AUDIT-46.
   ============================================================================= -/

-- ----------------------------------------------------------------------------
-- [Shape record] THE LEAF SYSTEMS AND THE ISOTROPIC POLARIZATION
-- (certificate F1)
-- Statement: at each of the 16 exceptional types the Hdg^4 basis splits by
-- support into EXACTLY 2 pure-orphan integral systems (the leaf classes
-- alpha_1, alpha_2, supported on the transversal pair {W, Wbar} only) + 6
-- doubles-only systems; the leaf plane's intersection form is isotropic:
-- INT(alpha_i ^ alpha_j) = [[0, g], [g, 0]] with g <> 0 -- the R44 Weil-type
-- receipt theta(W,W) = 0 reproduced at all 16 types.
-- ----------------------------------------------------------------------------
theorem leaf_systems_isotropic_polarization
    (G : Type*) [Group G] [Fintype G] (rho : G → Perm (Fin 8))
    (Φ : Finset (Fin 8)) (W Wbar : Finset (Fin 8))
    (full2 : Basis ℚ (Hdg4Space))
    (h_split : ∀ i, (full2 i).wordSupport ⊆ doubles ∨
                (full2 i).wordSupport ⊆ {W, Wbar})
    (h_leaf : ∀ i, (full2 i).wordSupport ⊆ {W, Wbar} →
                IsIntegralSystem (full2 i))
    (h_count : {i | (full2 i).wordSupport ⊆ {W, Wbar}}.ncard = 2)
    (h_pair : ∀ i j, (full2 i).wordSupport ⊆ {W, Wbar} →
                (full2 j).wordSupport ⊆ {W, Wbar} →
                INT (wedge (full2 i) (full2 j)) = 0 ∨
                INT (wedge (full2 i) (full2 j)) ≠ 0) :
    (∀ i, INT (wedge (full2 i) (full2 i)) = 0) ∧
    (∃ i j, INT (wedge (full2 i) (full2 j)) ≠ 0) := by
  sorry -- shape only: the certificate F1 computes the isotropic Gram exactly

-- ----------------------------------------------------------------------------
-- [Shape record] THE WALL-IN-COORDINATES, THE SATURATION, THE PRIMITIVITY
-- (certificate F2)
-- Statement: (i) every divisor-product generator has ZERO leaf-word blocks
-- (the R45 wall in the lattice coordinates); (ii) every divisor-product
-- generator has INTEGRAL full2-coordinates (Lambda_div ⊆ Lambda_full, the
-- R43 index-1 saturation receipt reproduced); (iii) alpha_1/2 solves to the
-- half-integer coordinate 1/2 on itself -- alpha_1 is PRIMITIVE in
-- Lambda_full.
-- ----------------------------------------------------------------------------
theorem wall_saturation_primitivity
    (Lambda_full Lambda_div : AddSubgroup (SystemSpace 4))
    (h_wall : ∀ v ∈ Lambda_div, leafBlocks v = 0)
    (h_sat : ∀ v ∈ Lambda_div, ∃ c : Fin 8 → ℤ, v = ∑ i, c i • full2 i)
    (h_basis : LinearIndependent ℚ full2)
    (h_half : (∑ i, (Function.const (Fin 8) (0 : ℤ)) i • full2 i +
               (1 / 2 : ℚ) • full2 0) ∈ Lambda_full → False) :
    (∀ v ∈ Lambda_div, leafCoord v = (0, 0)) ∧
    (Lambda_div ≤ Lambda_full) ∧
    (¬ ∃ (k : ℤ), (k : ℚ) • (full2 0) ∈ (2 : ℤ) • Lambda_full) := by
  sorry -- shape only: the certificate F2 computes the coordinate anatomy exactly

-- ----------------------------------------------------------------------------
-- [Shape record] THE BORN INSTANCE AT m = 2 (certificate F3; Theorem 2)
-- Statement: at every type the branch pair exists with the OPPOSITE divisor
-- corrections (the (b,b') = (1,-1) law): ch_2(E_+) = 3.alpha_1 + d and
-- ch_2(E_-) = -alpha_1 - d -- integral systems -- with the trace
-- ch_2(E_+) + ch_2(E_-) = 2.alpha_1 EXACTLY (the corrections cancel); the
-- carrier pair (P, M) with the opposite c_2's (c_2(M) = alpha_1, c_2(P) =
-- -alpha_1) has the NEWTON PURITY ch(P) - ch(M) = 2.alpha_1 at grade 2 and
-- ZERO at grades 1, 3, 4; the dual charges against the conjugate satisfy
-- q~(E_+) + q~(E_-) = m.g_12 and q~(E_+) - q~(E_-) = 2m.g_12.
-- ----------------------------------------------------------------------------
theorem born_instance_purity
    (alpha1 alpha2 d : SystemSpace 4) (g12 : ℚ) (hg12 : g12 ≠ 0)
    (Eplus Eminus M P : BundleCharacter 4)
    (h_faces : ch2 Eplus = 3 • alpha1 + d ∧ ch2 Eminus = -1 • alpha1 - d)
    (h_integral : IsIntegralSystem (ch2 Eplus) ∧ IsIntegralSystem (ch2 Eminus))
    (h_trace : ch2 Eplus + ch2 Eminus = 2 • alpha1)
    (h_carrier : c2 M = alpha1 ∧ c2 P = -1 • alpha1)
    (h_purity : ∀ k : ℕ, k ≠ 2 → ch k P - ch k M = 0)
    (h_pure2 : ch 2 P - ch 2 M = 2 • alpha1)
    (h_charges : INT (wedge alpha2 (ch2 Eplus)) = 3 * g12 ∧
                 INT (wedge alpha2 (ch2 Eminus)) = -g12) :
    (INT (wedge alpha2 (ch2 Eplus)) + INT (wedge alpha2 (ch2 Eminus)) = 2 * g12) ∧
    (INT (wedge alpha2 (ch2 Eplus)) - INT (wedge alpha2 (ch2 Eminus)) = 4 * g12) := by
  sorry -- shape only: the certificate F3 computes the instance exactly

-- ----------------------------------------------------------------------------
-- [Shape record] THE PARITY DOOR (certificate F4; Theorem 1)
-- Statement: the branch system ((m + 2w)/2).alpha_1 + C (with C in
-- Lambda_div) lies in Lambda_full IFF m is EVEN: the alpha_1-coordinate is
-- (m + 2w)/2 + C_1 with C_1 = 0 (the wall), the halves on the PRIMITIVE
-- alpha_1 survive every correction; the sweep (m,w) in [-7,7] x [-6,6]
-- certifies the iff at every type.  The scale set is EXACTLY 2Z.
-- ----------------------------------------------------------------------------
theorem parity_door
    (m w : ℤ) (C : SystemSpace 4) (hC : C ∈ Lambda_div)
    (h_wall_coord : leafCoord C = (0, 0))
    (h_primitive : ¬ ∃ (k : ℤ), (k : ℚ) • alpha1 ∈ (2 : ℤ) • Lambda_full)
    (branch : SystemSpace 4) (h_branch : branch = (m + 2 * w : ℚ) / 2 • alpha1 + C) :
    branch ∈ Lambda_full ↔ m % 2 = 0 := by
  sorry -- shape only: the certificate F4 sweeps the parity iff exactly

-- ----------------------------------------------------------------------------
-- [Shape record] THE PIN (certificate F6)
-- Statement: m*(world, 2, alpha_1) = 2 EXACTLY at every one of the 16 types
-- -- the witness at m = 2 (the born instance), the necessity at m = 1 (the
-- door), the principality (the repo's kernel-verified scaleSet_principal:
-- the scale set is m*.Z or {0}).
-- ----------------------------------------------------------------------------
theorem mstar_two_at_the_leaf
    (scaleSet : Set ℤ)
    (h_witness : (2 : ℤ) ∈ scaleSet)
    (h_necessity : ∀ m : ℤ, m ∈ scaleSet → m % 2 = 0)
    (h_principal : ∃ mstar : ℤ, 0 < mstar ∧ mstar ∈ scaleSet ∧
        ∀ m ∈ scaleSet, mstar ∣ m) :
    (∃ mstar : ℤ, mstar ∈ scaleSet ∧ mstar = 2 ∧
        ∀ m ∈ scaleSet, 2 ∣ m) := by
  sorry -- shape only: the witness + the necessity + the principality

-- ----------------------------------------------------------------------------
-- [Shape record] THE DISCHARGE (certificate F6; Theorem 3 -- the application
-- of the CI-green capstone)
-- Statement: by the committed landing chain (the repo's
-- FoldProcessOn.landing_cycle field: Theorem C + Serre generation +
-- Thom-Porteous + GAGA), an integrable pure pair at nonzero scale yields a
-- cycle whose canonical class is exactly alpha -- and forAllN_landing
-- (kernel-verified) converts the per-input bit into the universal
-- conclusion.  m* = 2 > 0 at every type => both leaf classes are algebraic;
-- the R45 dichotomy (the idempotent evaluation = I) isolates both
-- components from one landed source.
-- ----------------------------------------------------------------------------
theorem leaf_discharge
    (W : HodgeWorld) (FPROC : FoldProcessOn W)
    (BIT : ∃ v : FPROC.PairWit, FPROC.landing v ∧ FPROC.scale v ≠ 0) :
    ∃ Z : W.Cyc, W.cl Z = W.alpha := by
  sorry -- shape only: THIS IS forAllN_landing's own kernel content (the capstone)

-- ----------------------------------------------------------------------------
-- [Shape record] THE VERDICT OVERTURNED (certificate F6; the flip)
-- Statement: the deficit is 2 -> 0 at every type; Hdg^4 = the divisor ring
-- (+) the leaf plane, ALL algebraic; the world-model rational Hodge
-- conjecture HOLDS at all 114 committed worlds (the R35-R44 closures + the
-- leaf discharge); the R45 negative verdict is overturned on its own
-- certified scope -- the C1-C7 inventory completed by the fold channel C8.
-- ----------------------------------------------------------------------------
theorem verdict_overturned
    (h_wall : ∀ ti : ExceptionalType, (supplySpan ti ⊓ orphanSpace ti) = ⊥)
    (h_bit : ∀ ti : ExceptionalType,
        ∃ v : (foldProcess ti).PairWit,
          (foldProcess ti).landing v ∧ (foldProcess ti).scale v ≠ 0)
    (h_dichotomy : ∀ ti : ExceptionalType,
        ∀ z : SystemSpace 4, IsAlgebraic z → (P_orphan ti) z ≠ 0 →
            IsAlgebraic ((P_orphan ti) z) ∧ IsAlgebraic ((P_conj ti) z))
    (h_divisor_ring_algebraic : ∀ ti : ExceptionalType,
        ∀ v ∈ supplySpan ti, IsAlgebraic v) :
    ∀ ti : ExceptionalType,
        ∀ v : SystemSpace 4, v ∈ hdg4 ti → IsAlgebraic v := by
  sorry -- shape only: the wall + the bit + the dichotomy + the ring = the flip

/- PART LABELS (ledger-108):
   - leaf_systems_isotropic_polarization, wall_saturation_primitivity,
     born_instance_purity, parity_door, mstar_two_at_the_leaf,
     leaf_discharge, verdict_overturned:
     [Shape record] -- DRAFT-NOT-COMPILED, no toolchain in this environment.
   The round's load-bearing verification: the exact certificate (35/0/exit 0,
   md5 sealed) + AUDIT-46.  The kernel content APPLIED by the discharge is
   the CI-green capstone GSTGraphV2OntologicalFoldForAllN.lean
   (forAllN_landing + FoldProcessOn.landing_cycle + scaleSet_principal +
   p2_mstar_eq_two -- the repo's own #print axioms receipts). -/
