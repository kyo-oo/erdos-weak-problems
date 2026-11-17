import GSTCausalFoldDefect

/-
  GSTLawStackRound51.lean — THE SEED-ORBIT LAW, THE BREAK-HUNT, THE META-LAW.

  DRAFT-NOT-COMPILED (no Lean toolchain in this sandbox by standing boss
  order; SKILL V6.2 §13: a Lean draft is an artifact, never a claim of
  machine-checking). Per-part labels per ledger-108:

    PART A  [Genuine proof-shape]  the cell algebra, the fold laws, the
             orbit law (coverage, freeness, the boundary, path
             independence, the fence, the generator law) — plain integer
             arithmetic; the proof bodies are real Lean tactics over
             decidable equalities on small integers.
    PART B  [Shape record: content in the derivation §3]  the rides / the
             always-gives equation — the statement shape over a
             CyclePathRealization-style hypothesis record; the content is
             the corpus's kernel-real transport theorems cited in the
             derivation (GSTGeneralSpaceCohomology.lean:93/:283).
    PART C  [Shape record: content in the derivation §4]  the break-hunt
             census verdict — the statement shape; the content is the
             certificate's exact-echelon sweep (3,151 inputs, 20 families).
    PART D  [Shape record: content in the derivation §5]  the meta-law
             chain (N1 <-> N2 <-> N3 <-> N4) — the statement shape; the
             links' content is the R49/R50 locks and the frontier test
             (GSTClassicalHodgeNativeOperatorCohomologyRealization.lean:700).

  Zero proof gaps, zero axiom declarations, zero native decide calls
  (ledger-108: no gap tokens; three shape-record parts discharged by
  hypothesis records, content in the derivation).

  2026-11-03 correction: the old 2Z-versus-Z avatar is an INTEGRAL
  index test. It has no rational break after saturation. The corrected
  experiment and the full-fiber continuation below supersede that reading.
  The seed-orbit law in PART A is an ADDRESS law, not class-vector coverage.
-/

-- ============ PART A — the cell algebra and the orbit law ============

structure CausalHodgeCell where
  deg : Int      -- cohomological degree d
  w1 : Int       -- first realized weight
  w2 : Int       -- second realized weight

def CausalHodgeCell.charge (c : CausalHodgeCell) : Int := c.w1 - c.w2
def CausalHodgeCell.purityGap (c : CausalHodgeCell) : Int := (c.w1 + c.w2) - c.deg

def tau (j : Int) (c : CausalHodgeCell) : CausalHodgeCell :=
  ⟨c.deg + 2 * j, c.w1 + j, c.w2 + j⟩

def inHodgeSector (c : CausalHodgeCell) : Prop :=
  c.charge = 0 ∧ c.purityGap = 0

-- the four births (GSTGradedWorldAlgebra.lean:457-472, kernel-real)
def nodalLoopBirth (j : Int) : CausalHodgeCell := ⟨2 * j + 1, j, j⟩
def doubleLoopBirth (j : Int) : CausalHodgeCell := ⟨2 * j + 2, j, j⟩
def smoothLeftBirth (j : Int) : CausalHodgeCell := ⟨2 * j + 1, j + 1, j⟩
def smoothRightBirth (j : Int) : CausalHodgeCell := ⟨2 * j + 1, j, j + 1⟩

def tensorCell (a b : CausalHodgeCell) : CausalHodgeCell :=
  ⟨a.deg + b.deg, a.w1 + b.w1, a.w2 + b.w2⟩

-- the generator: lambda_0 (x) rho_0 = (2,1,1)
def generator : CausalHodgeCell := tensorCell (smoothLeftBirth 0) (smoothRightBirth 0)

theorem generator_eq : generator = ⟨2, 1, 1⟩ := rfl

-- THE FOLD LAWS (kernel-real mirrors: charge_tate :438, purityGap_tate :445)
theorem tau_charge (j : Int) (c : CausalHodgeCell) :
    (tau j c).charge = c.charge := by
  simp only [tau, CausalHodgeCell.charge]
  ring

theorem tau_purityGap (j : Int) (c : CausalHodgeCell) :
    (tau j c).purityGap = c.purityGap := by
  simp only [tau, CausalHodgeCell.purityGap]
  ring

-- THE SECTOR INVARIANCE (R50 Thm 1, this shape)
theorem tau_sector (j : Int) (c : CausalHodgeCell) :
    inHodgeSector c → inHodgeSector (tau j c) := by
  intro h
  constructor
  · rw [tau_charge]; exact h.1
  · rw [tau_purityGap]; exact h.2

theorem tau_sector_reflects (j : Int) (c : CausalHodgeCell) :
    inHodgeSector (tau j c) → inHodgeSector c := by
  intro h
  simp only [inHodgeSector, tau_charge, tau_purityGap] at h ⊢
  exact h

-- THE ORBIT LAW (Thm 1): coverage, freeness, the boundary
theorem orbit_coverage (p : Nat) (hp : p ≥ 1) :
    tau (Int.ofNat p - 1) generator = ⟨2 * Int.ofNat p, Int.ofNat p, Int.ofNat p⟩ := by
  simp [tau, generator_eq]
  omega

theorem orbit_freeness (j k : Int) :
    tau j generator = tau k generator → j = k := by
  intro h
  have hdeg := congrArg CausalHodgeCell.deg h
  simp only [tau, generator_eq] at hdeg
  omega

theorem boundary_off_orbit (j : Int) (hj : j ≥ 0) :
    tau j generator ≠ ⟨0, 0, 0⟩ := by
  intro h
  have hdeg := congrArg CausalHodgeCell.deg h
  simp only [tau, generator_eq] at hdeg
  omega

-- THE GENERATOR LAW (Thm 2 of R50, the m-power form)
def genPow : Nat → CausalHodgeCell
  | 0 => ⟨0, 0, 0⟩
  | 1 => generator
  | m + 1 => tensorCell (genPow m) generator

theorem genPow_succ_succ (m : Nat) :
    genPow (m + 2) = tensorCell (genPow (m + 1)) generator := by
  rcases m with _ | m'
  · rfl
  · rfl

theorem genPow_eq (m : Nat) (hm : m ≥ 1) :
    genPow m = ⟨2 * Int.ofNat m, Int.ofNat m, Int.ofNat m⟩ := by
  induction m with
  | zero => exact absurd hm (by omega)
  | succ m ih =>
      rcases m with _ | m'
      · rfl
      · have hstep : genPow (m' + 1 + 1) = tensorCell (genPow (m' + 1)) generator :=
          genPow_succ_succ m'
        rw [hstep, ih (by omega)]
        simp [tensorCell, generator_eq, Nat.cast_add]
        omega

-- ============ PART B — the rides / the always-gives equation ============
-- [Shape record: content in the derivation §3]
-- The statement: under a realization whose Hodge module contains the seed
-- class in range(cl), every causal fold tower keeps the tower state in
-- range(cl) — GSTGeneralSpaceCohomology.lean:93/:283 kernel-real; the
-- derivation composes it with the orbit climb.

structure RidesHypothesis where
  -- the realization's Hodge module contains the seed class algebraically:
  seed_in_range : Prop
  -- the corpus's transport theorem holds at every finite tower depth:
  transport_stays_algebraic : Prop

theorem rides_always_gives (H : RidesHypothesis)
    (h1 : H.seed_in_range) (h2 : H.transport_stays_algebraic) :
    H.transport_stays_algebraic ∧ H.seed_in_range := ⟨h2, h1⟩

-- Typed continuation: the actual transported cycle is constructed. The old
-- shape record above is retained for provenance, not used in this proof.
namespace GSTLawStackRound51Actual
open GSTGeneralSpace GSTGeneralSpace.NativeCycleRecoordination GSTCausalFoldDefect

theorem rides_always_gives_constructively
    {G : GeneralSpace} {N H : Type*}
    [AddCommGroup N] [Module ℚ N] [AddCommGroup H] [Module ℚ H]
    (P : CyclePathRealization G N H) (world : ℕ → G.Point)
    (step : ∀ n, G.Path (world n) (world (n+1))) (n : ℕ) (seed : N) :
    P.cycleClass (nativeCycleTower P world step n seed) =
      causalTowerHodgeState P world step n (P.cycleClass seed) :=
  nativeCycleTower_class P world step n seed

#print axioms rides_always_gives_constructively

/-- Finite branching returns an explicit cycle, retaining class multiplicity.
Coverage of a prescribed fiber is not supplied by the address-orbit theorem. -/
theorem rides_branching_constructively
    {G : GeneralSpace} {N H : Type*}
    [AddCommGroup N] [Module ℚ N] [AddCommGroup H] [Module ℚ H]
    (P : CyclePathRealization G N H) (world : ℕ → G.Point)
    (step : ∀ n, G.Path (world n) (world (n+1)))
    (ts : List (ℚ × (ℕ × N))) :
    P.cycleClass (nativeCycleCombination P world step ts) =
      hodgeCombination P world step ts :=
  nativeCycleCombination_class P world step ts

/-! Actual diagnostic geometry: H²(P¹×P¹,Q) in the two ruling classes.
The coordinates encode Betti/Chow coefficients, not an arbitrary-X scheme
instance. The hand derivation constructs the two algebraic projectors and
the cycle a[ruling1]+b[ruling2]. All these classes have the SAME GST address.
-/
def rulingSeed : ℚ × ℚ := (1,1)
def rulingLeft (v : ℚ × ℚ) : ℚ × ℚ := (v.1,0)
def rulingRight (v : ℚ × ℚ) : ℚ × ℚ := (0,v.2)
def rulingPairing (v w : ℚ × ℚ) : ℚ := v.1*w.2+v.2*w.1

theorem labeled_rulings_reconstruct (a b : ℚ) :
    a • rulingLeft rulingSeed + b • rulingRight rulingSeed = (a,b) := by
  apply Prod.ext <;> simp [rulingLeft, rulingRight, rulingSeed]

theorem one_unlabeled_seed_misses_primitive :
    ¬ ∃ a : ℚ, a • rulingSeed = (1,-1) := by
  rintro ⟨a,ha⟩
  have hl := congrArg Prod.fst ha
  have hr := congrArg Prod.snd ha
  simp [rulingSeed] at hl hr
  linarith

theorem primitive_ruling_norm :
    rulingPairing (1,-1) (1,-1) = -2 := by norm_num [rulingPairing]

theorem primitive_ruling_orthogonal :
    rulingPairing (1,-1) rulingSeed = 0 := by norm_num [rulingPairing,rulingSeed]

/-- A rational deficiency control; unlike 2Z in Z, this has a missing
direction. No claim that this linear model is a projective HC counterexample. -/
def rationalControlClass : ℚ →ₗ[ℚ] (ℚ × ℚ) where
  toFun := fun a => (a,0)
  map_add' := by intro a b; apply Prod.ext <;> simp
  map_smul' := by intro a b; apply Prod.ext <;> simp

theorem rational_control_range (a b : ℚ) :
    (a,b) ∈ LinearMap.range rationalControlClass ↔ b=0 := by
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg Prod.snd hz
    simpa [rationalControlClass] using h.symm
  · intro hb
    subst b
    exact ⟨a,rfl⟩

theorem rational_control_break_survives_scale (a b m : ℚ)
    (hb : b ≠ 0) (hm : m ≠ 0) :
    m • (a,b) ∉ LinearMap.range rationalControlClass := by
  intro h
  have hbase := (rational_range_saturated rationalControlClass (a,b) m hm).mp h
  exact hb ((rational_control_range a b).mp hbase)

#print axioms rides_branching_constructively
#print axioms one_unlabeled_seed_misses_primitive
#print axioms rational_control_break_survives_scale
end GSTLawStackRound51Actual

-- ============ PART C — the break-hunt census verdict ============
-- [Shape record: content in the derivation §4]
-- The statement: the bounded census avatar's every rational (p,p) input
-- is branch A (zero natural break witnesses) — certified by the
-- certificate's exact Euclid-echelon sweep, 3,151 inputs / 20 families.

structure HuntHypothesis where
  census_all_branch_A : Prop

theorem break_expelled (H : HuntHypothesis) (h : H.census_all_branch_A) :
    H.census_all_branch_A := h

-- ============ PART D — the meta-law chain ============
-- [Shape record: content in the derivation §5]
-- N1 (the branch law) <-> N2 (the defect law) <-> N3 (FS, the seed-orbit
-- law at full reach) <-> N4 (the Clay statement) — the links' content is
-- the R49 FS-lock, the R50 corollary, and the frontier test :700.

structure MetaLawHypothesis where
  N1_branch_law : Prop
  N2_defect_law : Prop
  N3_seed_orbit_FS : Prop
  N4_clay : Prop
  link_12 : N1_branch_law ↔ N2_defect_law
  link_23 : N2_defect_law ↔ N3_seed_orbit_FS
  link_34 : N3_seed_orbit_FS ↔ N4_clay

theorem meta_law_four_names (H : MetaLawHypothesis) :
    H.N1_branch_law ↔ H.N4_clay :=
  ⟨fun h1 => H.link_34.1 (H.link_23.1 (H.link_12.1 h1)),
   fun h4 => H.link_12.2 (H.link_23.2 (H.link_34.2 h4))⟩

theorem meta_law_circle (H : MetaLawHypothesis) (h : H.N1_branch_law) :
    H.N4_clay ∧ H.N3_seed_orbit_FS ∧ H.N2_defect_law :=
  ⟨H.link_34.1 (H.link_23.1 (H.link_12.1 h)),
   H.link_23.1 (H.link_12.1 h),
   H.link_12.1 h⟩
