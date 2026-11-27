# General Space Omniversal Control Upgrade

Date: 2026-10-03
Branch: `sol/hodge-strict-betti-correspondence-fusion-20261003`
Parent design: `docs/superpowers/specs/2026-10-03-general-space-hodge-cosmology-design.md`

## Locked objective

Continue the already-approved carrier-independent General Space architecture. The upgrade must increase actual formal control, not decorative complexity. The exact Hodge target remains unchanged:

```lean
GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsFiniteRationalCombination H
```

No new structure may contain this conclusion, basis algebraicity, universal sheet reachability, cycle-class surjectivity, or defect extinction as data.

## Burst A — maps between whole General Spaces

Add a first-class `GeneralSpace.Hom` preserving points, paths, identities and composition. Add identity/composition, products, projections and product maps. This promotes GST from a collection of isolated path universes to an actual calculus of spaces and structure-preserving maps.

## Burst B — topology and all smooth manifolds as realizations

Add `GSTGeneralSpaceTopology.lean` using Mathlib continuous paths only through the proposition that a path exists. This quotient-by-existence is deliberate: raw topological path concatenation is associative and unital only up to reparametrization, whereas propositional reachability gives strict General Space laws by proof irrelevance.

Every topological space therefore induces a General Space. Every continuous map induces a General Space homomorphism. Homeomorphisms induce reversible General Space maps.

Add `GSTGeneralSpaceManifold.lean`: every Mathlib charted `C^n` manifold is admitted through its underlying topological General Space while retaining `ModelWithCorners`, `ChartedSpace`, and `IsManifold` as an optional capability. GST does not assert that every General Space is a manifold.

## Burst C — realization pullback and recoordination across space maps

A realization on a target General Space can be pulled back along a General Space homomorphism. Intrinsic observables and transported state systems must compose through these maps. This is the formal mechanism by which manifold, graph, scheme, Hodge, Betti and native-cycle sectors can be observed from one higher ontology without identifying them.

## Burst D — geometric/Hodge semantic firewall

Keep the exact Hodge target wired. Strengthen the distinction between:

1. arbitrary Stage-2G semantic data;
2. genuinely geometrically constructed Hodge/cycle-class realizations;
3. GST internal dyadic/triadic Hodge dictionaries.

No internal GST finite analogy may be used as the geometric Hodge decomposition of an arbitrary smooth projective complex variety without an explicit realization theorem.

## Burst E — source and operator construction

Continue the actual proof frontier:

- prove ambient exact codimension for principal-cut successors from scheme geometry;
- construct nonzero native sources in every live weight;
- construct source-specific genuine correspondence/native operators realizing the GST code/Lefschetz word;
- feed them into `GSTClassicalHodgeGeneralSpaceOperatorCosmos`;
- terminate through `GSTClassicalHodgeGeneralSpaceExactOperatorFinale` at the literal finite rational combination target.

## Verification discipline

New files are not called green until Lean compilation or GitHub CI reports success. GLM may repair syntax/API mismatches, but repairs must preserve theorem statements and the architecture above.
