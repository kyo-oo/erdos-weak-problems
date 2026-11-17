from pathlib import Path


def replace(path: str, old: str, new: str) -> None:
    p = Path(path)
    s = p.read_text()
    if new in s:
        return
    if old not in s:
        raise SystemExit(f"target block not found: {path}")
    p.write_text(s.replace(old, new, 1))


replace(
    "GSTUniversalLefschetzCosmology.lean",
    '''theorem compactEvolution_completed (n : ℕ) (f : CompactCosmos) :
    (fun c => compactEvolution n f c) = (cosmicLefschetz^n) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (fun c => compactLefschetz (compactEvolution n f) c) = _
    rw [compactLefschetz_completed, ih, pow_succ', Module.End.mul_apply]
''',
    '''theorem compactEvolution_completed (n : ℕ) (f : CompactCosmos) :
    (fun c => compactEvolution n f c) = (cosmicLefschetz^n) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (fun c => compactLefschetz (compactEvolution n f) c) = _
    rw [compactLefschetz_completed]
    change cosmicLefschetz (fun c => compactEvolution n f c) = _
    rw [ih, pow_succ', Module.End.mul_apply]
''',
)

replace(
    "GSTUniversalLefschetzCosmology.lean",
    '''theorem observe_compactEvolution (A B n : ℕ) (f : CompactCosmos) :
    observe A B (compactEvolution n f) =
      (lefschetzEndo A B ^ n) (observe A B f) := by
  rw [compactEvolution_completed, observe_cosmicLefschetz_pow]
''',
    '''theorem observe_compactEvolution (A B n : ℕ) (f : CompactCosmos) :
    observe A B (compactEvolution n f) =
      (lefschetzEndo A B ^ n) (observe A B f) := by
  change observe A B (fun c => compactEvolution n f c) = _
  rw [compactEvolution_completed, observe_cosmicLefschetz_pow]
''',
)

replace(
    "GSTGlobalPureHodgeCosmology.lean",
    '''def CosmicPureHodge : Submodule ℤ CompletedCosmos where
  carrier := {f | ∀ c, c.1 ≠ c.2 → f c=0}
  zero_mem' := by intros; rfl
  add_mem' := by intro f g hf hg c hc; simp [hf c hc, hg c hc]
  smul_mem' := by intro z f hf c hc; simp [hf c hc]
''',
    '''def CosmicPureHodge : Submodule ℤ CompletedCosmos where
  carrier := {f | ∀ c, c.1 ≠ c.2 → f c=0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg c hc; simp [hf c hc, hg c hc]
  smul_mem' := by intro z f hf c hc; simp [hf c hc]
''',
)

replace(
    "GSTGlobalPureHodgeCosmology.lean",
    '''  left_inv := by
    intro f
    apply Subtype.ext
    funext c
    by_cases h : c.1=c.2
    · simp [cosmicPureReassemble, h]
    · simp [cosmicPureReassemble, h, f.property c h]
''',
    '''  left_inv := by
    intro f
    apply Subtype.ext
    funext c
    rcases c with ⟨i, j⟩
    by_cases h : i = j
    · subst j
      simp [cosmicPureReassemble]
    · simp [cosmicPureReassemble, h, f.property (i, j) h]
''',
)

replace(
    "GSTInfiniteWorldClassification.lean",
    '''  · intro h
    apply continuous_pi
    intro c
    exact (continuous_apply (⟨c.1, by omega⟩, ⟨c.2, by omega⟩) :
      Continuous (fun g : WorldCoef (c.1+1) (c.2+1) =>
        g (⟨c.1, by omega⟩, ⟨c.2, by omega⟩))).comp (h (c.1+1) (c.2+1))
''',
    '''  · intro h
    apply continuous_pi
    intro c
    let c' : WorldCell (c.1+1) (c.2+1) :=
      (⟨c.1, by omega⟩, ⟨c.2, by omega⟩)
    have heval : Continuous
        (fun g : WorldCoef (c.1+1) (c.2+1) => g c') :=
      continuous_apply c'
    simpa [c', observe] using heval.comp (h (c.1+1) (c.2+1))
''',
)

replace(
    "GSTInfiniteWorldClassification.lean",
    '''  continuous_invFun := by
    apply continuous_induced_rng.mpr
    have h : innovationStream ∘ streamTower = id := by
      funext a
      exact innovationStream_streamTower a
    rw [h]
    exact continuous_id
''',
    '''  continuous_invFun := by
    apply continuous_induced_rng.mpr
    change Continuous (innovationStream ∘ streamTower)
    have h : innovationStream ∘ streamTower = id := by
      funext a
      exact innovationStream_streamTower a
    rw [h]
    exact continuous_id
''',
)

replace(
    "GSTTransferBridgeV2.lean",
    '''def compactClMono (p : Nat) : CompactClRing :=
  Finsupp.single (compactClCode p) 1
''',
    '''noncomputable def compactClMono (p : Nat) : CompactClRing :=
  Finsupp.single (compactClCode p) 1
''',
)
