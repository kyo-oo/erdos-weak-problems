# GST universal source-existence attempt: diagonal contraction test

Date: 2026-10-21
Source revision: ae27ee80ae6c3448bd856a6b75bafd5f73543192
Original owner goal: genuine canonical rational Hodge cycles on every original X.

## Verdict

The requested universal-existence theorem has **not** been proved. This is a new executed attempt at its decisive implication, not another conditional compiler presented as completion.

Tested implication: native diagonal + duality + positive residual doubled Euler index + stable world closure + native lift + formal degree/trace identities => a native one-sided source with nonzero residual period.

The listed abstract properties do not imply that conclusion. The attached derivation proves an invariant tensor contraction theorem and gives a nonzero unital polarized seven-dimensional graded algebra satisfying these properties while every admissible one-sided residual period vanishes.

**Scope:** This is an abstract algebraic test of that inference. It is not a variety, not a canonical Chow comparison, not a Hodge counterexample, and not a claim that every geometric hypothesis of the entire GST repository is modeled. Geometry-specific source birth may use additional facts.

## Mathematical result

For a B-isometric involution g, put N_n=(H^{tensor n})^g. Tensor products, permutations, contractions and all equivariant birth maps preserve N_n. Thus any admissible one-leg output z is g-fixed; if gr=-r, then B(r,z)=0.

Uniform model for all positive rational a,b:

H = Q[h,s,r]/(h^5,hs,hr,sr,s^2-a h^4,r^2-b h^4),
deg(h)=1, deg(s)=deg(r)=2, integral(h^4)=1.

It has a unit, formal Tate grading, Frobenius pairing determinant ab, Hard Lefschetz, and positive primitive middle Gram diag(a,b). Set gh=h, gs=s, gr=-r. Its *full* admissible one-leg sector has dimension six, including unit, ample, top and a nonzero primitive s.

The admissible tensor K=(r tensor r)/b is an idempotent kernel with T_K(r)=r, T_K(A)=0, trace one and positive doubled contraction b. In the established p=2,M=5 Euler convention, the signed kernel is -K and the negative doubled Euler index is b>0. Every one-leg admissible residual period is zero.

The full two-leg admissible sector has dimension 37; one-leg external products span dimension 36. The extra residual tensor is precisely the missing direction. This is a full admissible-sector test, not merely an incomplete chosen-frame test.

For every integer e>0 the diagonal pullback H->H^{directsum e} and summation trace satisfy f_*f^*=e id and energy scaling by e. They preserve the same obstruction. These model the linear trace equations only, not an actual complete alteration.

## Actual GST geometric discriminator

Using the existing all-genus curve intersection formulas on C x C, D=Delta-[point x C]-[C x point] satisfies D.A=D.B=0 and D^2=D.Delta=-2g.

Hence for g>=1, [O_Delta] is not a finite rational sum of external K0(C)-products: their ch_1 is in span(A,B), whereas ch_1(O_Delta)=Delta.

This excludes whole-diagonal separated K factorization. It does not exclude the weaker middle-Hodge-testing-block factorization of the preceding derivation. D itself is a genuine algebraic divisor.

## Durable artifacts and reproduction

- [Full mathematical derivation](../derivations/GST_universal_source_existence_attempt.tex)
- [Exact Python computation](../computations/gst_tensor_source_forcing_audit.py)
- [Python output](../computations/gst_tensor_source_forcing_audit.output.json)
- [v2 manifest](../computations/gst_tensor_source_forcing_audit.manifest.json)
- [Wolfram symbolic input](../computations/gst_tensor_source_forcing_audit.wl)
- [Observed Wolfram output](../computations/gst_tensor_source_forcing_audit.wolfram.txt)

From repository root: python3 research/computations/gst_tensor_source_forcing_audit.py

At a=3,b=5, exact rational checks passed for all 343 associativity basis triples and all 49 automorphism basis pairs, determinant 15, Lefschetz ranks (1,1,3), primitive Gram diag(3,5), tensor dimensions, projector and Euler signs. A separate stateless Wolfram evaluation checks the parameterized primitive formulas and symbolic genus calculation. Its first draft had a vector shape error; after explicit flattening the recorded run returned the expected exact results without messages.

The v2 manifest passed the Mathbox manifest validator with input/output hashes checked against these files. The source was compiled with pdflatex to a five-page document. This checks LaTeX compilation, not mathematical truth. Proof review is self-review; no independent review, new Lean theorem, or Lean compilation is claimed.

## Exact outstanding operation

Produce an actual algebraic perfect-complex source on the real middle blowup world with a nonzero linear residual Euler period, without assuming the target's algebraicity or one-sided factorization. Existing native return then gives the original-X detector. Neither the invariant model nor its formal degree equations settles whether real geometry always supplies that source.

No change to the canonical all-X proof contract and no completed-universal-existence status.

