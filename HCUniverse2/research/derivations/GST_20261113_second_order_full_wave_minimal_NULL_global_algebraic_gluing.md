# GST single-hypothesis attack: physical second-order wave, optimal NULL compensation, and genuine global algebraic gluing

**Research date:** 2026-11-13
**Base:** original research branch at \`eb4613544d2018f09a0809cc902d9009461320be\`
**Exact target:** \`GSTHodgeSingleHypothesisConditional.NativeGSTSingleFoldOrbitLaw\`, NOT a collection of restricted Hodge examples. For every original smooth projective complex X, Hodge weight p, construct ONE actual realized source-bearing correspondence and ONE true native seed whose cohomological orbit spans the entire prescribed rational Hodge fiber. The already-verified Lean implication from this GST law is not re-proved or mistaken for a proof of its antecedent.
**Status:** The full universal GST law remains unproved. The present execution gives a new all-rank GST minimal-NULL algebraic theorem and an explicit genuinely glued non-split algebraic bundle from the FULL owner's physical 12-cell, second-order \(N+N^2\) wave, without supplying any initial algebraic cycle.

## Owner-native inputs and three-world interpretation

Use the repository's exact definitions in \`GSTGraphV2CMWaveFusion.lean\` and \`GSTImageThreeCurvatureResonance.lean\` on the 12 actual carry/trit cells: shuffle U, signed rational complex mirror J with J^2=-I, SURVIVE diagonal M, and actual CM commutator C=[J,M]. The physically allowed Navigation charge is b=0 or b=1 from the existing navigation predicate (not an arbitrary half-curvature parameter).

Take the **owner's actual second-order** proposal, not a replacement isolated two-cell matrix:

    T_b = U + J + M + b [J,M],
    F_b = T_b + T_b^2.

Using exactly the repo's 12-cell ordering (carry i=0..3, trit k=0..2), the shuffle (i,k)->(floor((i+4k)/3),(i+4k) mod 3), signed mirror (i,k)->(3-i,2-k), sign chart {0,1,3,4,5,9}, and source multiplicity surviveI, independent exact computations give:

    rank([J,M]) = 6,
    rank([F_0,M]) = 6,
    rank([F_1,M]) = 6,
    rank(F_0) = 12,
    rank(F_1) = 11.

The initial wave signal has its prior independently verified full Krylov orbit in both physical modes, but the present rank statement concerns the *remaining curvature* between the owner's second-order fold and original SURVIVE.

Denote the two universe operations B1=F_b and B2=M, and C_b=[B1,B2]. We interpret the GST+ and ALT- branches as the two ordered terms B1 B2 and -B2 B1, and NULL as a finite source/return channel W capable of absorbing their obstruction.

## Theorem 1 (exact general minimal-NULL world law; ANY n)

Let V be n-dimensional over a characteristic-zero field, let B1,B2 endomorphisms, and let C=[B1,B2] have rank r. Seek a NULL world W and maps

    I:W->V (surjective),  R:V->W (injective),

satisfying the **actual curvature cancellation equation**

    [B1,B2] + I R = 0.

Then the minimum possible dimension of W is **2n-r**, and it is attained constructively for every pair B1,B2.

Proof of lower bound: the Sylvester rank inequality gives

    r=rank(IR)>=rank(I)+rank(R)-dim W = 2n-dim W.

Construction: choose a direct-sum splitting V=ker C ⊕ V', let pi:V->ker C be the corresponding projection, and define

    W = V ⊕ ker C,  I(v,k)=v,  R(v)=(-C v, pi(v)).

The map I is surjective. If R(v)=0, then Cv=0, hence v∈ker C and pi(v)=v=0; therefore R is injective. Finally IR=-C. Dimension is n+(n-r)=2n-r. QED.

This is a real **source-sensitive cardinality law**: the number of new NULL compensation channels is forced by exact curvature rank. It does not assume an unknown Hodge basis.

For the owner's full original second-order 12-wave and either genuine Navigation state, n=12,r=6, hence

    MINIMAL NULL DIMENSION = 2*12-6 = 18.

For r independent N-hole waves, the direct-sum rank is 6r and the minimum compensator dimension is 18r. Arbitrarily indexed finite-support collections are treated componentwise; an arbitrary infinite direct sum is NOT claimed to be a finite-type algebraic vector bundle.

## Theorem 2 (nontrivial GLOBAL algebraic gluing from full GST second-order F)

Fix one physical Navigation state b∈{0,1}; let n=12, V=Q^12, and use the maps I:Q^18->V and R:V->Q^18 supplied by Theorem 1 for C_b=[F_b,M].

Over projective plane P² with homogeneous coordinates [x:y:z], define actual morphisms of algebraic vector bundles:

    sigma: V⊗O(-1) -> (V⊕V⊕W)⊗O,
      sigma(v)=((z F_b-x)v, (z M-y)v, z R v),

    tau: (V⊕V⊕W)⊗O -> V⊗O(1),
      tau(u,v,w)=-(z M-y)u+(z F_b-x)v+z I w.

They satisfy the exact identity

    tau sigma = z²( [F_b,M] + I R ) = 0.

Fiberwise injectivity of sigma: when z≠0, its third block zR is injective; when z=0, at least one of x,y is nonzero so its first/second scalar blocks imply v=0.

Fiberwise surjectivity of tau: when z≠0, its last block zI is surjective; when z=0, at least one of x,y is nonzero so its first/second scalar blocks are surjective.

Therefore sigma and tau are globally constant-rank injective/surjective bundle maps, and their middle cohomology

    E_b = ker(tau)/im(sigma)

is a GENUINE locally free **algebraic vector bundle** of rank

    (2n+dim W) - n - n = dim W =18.

No algebraic-cycle seed representing a prescribed Hodge target was used; the input is the author's exact U,J,M physical wave plus the standard projective homogeneous coordinates. The resulting maps glue globally, not just as an abstract 48x48 finite wave.

Exact K-class and Chern character on P²:

    [E_b] = 42[O] - 12[O(-1)] - 12[O(1)],
    ch(E_b) = 18 - 12 h²; c1(E_b)=0; c2(E_b)=12 h².

The characteristic class is NONZERO, and E_b is **not** a sum of algebraic line bundles: any such splitting with c1=0 would give c2= -(1/2) sum_i a_i² ≤0, contradicting c2=12>0. The construction is a precise owner-GST realization of the established algebraic monad/ADHM compensation mechanism; no literature novelty is claimed for the general monad.

This genuinely solves the local-to-global *algebraic-gluing existence* subproblem FOR THIS CONSTRUCTED GST GEOMETRY, not the all-X GST orbit law.

## Critical distinction: what this has and has not forced

A new algebraic vector bundle exists, but its rational Chern character depends only on (n,dim W), NOT on the operator entries of F_b or M. Hence the present uniform monad gives an actual class on P² but by itself cannot force any arbitrary primitive Hodge direction on an arbitrary original X. This is an exact algebraic-charge blindness theorem for this specific constant-matrix monad, not a universal barrier to GST source-birth.

Any claim that the exact GST hypothesis is now proved would be false: it requires source-birth ON THE ORIGINAL arbitrary X with nonzero prescribed Hodge-fiber coupling, then a single realized correspondence with a full Krylov orbit. Existing graph birth rules and the new rank-minimal gluing theorem do not provide that original-X coupling automatically. The next research attack must develop *geometry-sensitive* GST matrix/cohomology coefficients, not another constant wave matrix or an unproved alpha-to-algebraic projectors assumption.

The core numerical improvement is not an isolated special-family rank certificate: the **minimal NULL theorem is exact for every n and every original operator pair**, while the GLOBAL genuine bundle is the demanding geometric test using the complete 12-state physical wave.

## Proof provenance

Independent SymPy reconstruction of original 12-cell U/J/M definitions, of C_0,C_1 and rank, explicit constructive I,R via a rational nullspace splitting, and projective monad rank checks at [1:0:0],[0:1:0],[0:0:1],[2:3:1] all passed. The all-projective-point injectivity/surjectivity follows from the symbolic proof above, not from sampling. Wolfram independently confirmed rank([F_b,M])=6 and null-minimum 18 for both physical b. The K-class/Chern calculation was independently checked exactly.

This mathematical derivation does NOT change any Lean theorem, assume \`NativeGSTSingleFoldOrbitLaw\`, assert algebraic surjectivity, or claim new Lean CI.
