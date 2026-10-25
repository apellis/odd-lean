# Lowest and highest weight versions of the action

Status: **proposed conditional construction**. Its input is a genuine
multicolour action, including the presentation comparison identified in
ActionReview.md. The construction supplies the other weight orientation;
it does not supply the fusion of two copies of the root datum.

## Which orientation is already proposed?

MulticolourActionTheorem uses `E=induction`, `F=restriction` and weight
`−Λ+β`. This is already the **lowest-weight** version: its generating
category has weight −Λ and restriction kills its vacuum at β=0. KKO's
letters E,F and weight Λ−β are reversed relative to this convention.
Consequently one must not obtain a purported lowest-weight action by
negating this weight a second time without also exchanging the functors.

Write this input action as `L_Λ`. At β=0 the algebra is its parameter
superalgebra A, and the vacuum is its free rank-one projective module. It
is nonzero when A is nonzero. The exterior parameters remain independent
at the vacuum; this observation alone does not identify the images of
normalized bubbles or prove their independence.

Odd cutoffs in L_Λ are handled by OddCutoffAction.md, with the qualifications
there. The weight reversal below works for either cutoff parity.

## Signed Chevalley transport

BE2, arXiv:1701.04133v2, Proposition 3.5 constructs

`ω: U → U^sop`, `λ↦−λ`, `E_i↦F_i`, `F_i↦E_i`.

Here sop reverses **2-morphisms**, not 1-morphisms. If f,g are homogeneous,
its vertical composition is

`f^sop ∘ g^sop = (−1)^(|f||g|)(g∘f)^sop`.

The image of an upward crossing has factor `−(−1)^(p(i)p(j))` times the
downward crossing in the super-opposite. The proposition also specifies
cups, caps and the weight-dependent factors on their derived versions.
These factors cannot be replaced by unsigned reflection. In particular,
an n-fold odd dot composite in sop acquires the usual pairwise reversal
sign; one should apply the functor to the composite rather than redraw
n dots without its composition convention.

For `L_Λ:U→B`, form

`H_Λ = L_Λ^sop ∘ ω : U → B^sop`.

This is the highest-weight version. Its category at λ is the super-opposite
of the old one at −λ, so its support has weights `Λ−β`. Its raising functor
is the old restriction and kills the vacuum; lowering is the old induction.
Its adjunction and inversion maps are the transported ones. All defining
relations follow from functoriality and the source isomorphism; no new trace
or nondegeneracy theorem is an input.

If B is a supercategory-valued target, the target can be realized using
super-opposite categories and functors. Finite projective duality provides
a subsequent description using opposite-side modules when desired. That
extra identification must be written with its superlinear signs; it is not
necessary merely to obtain a representation in the opposite target.

The source symmetry is already represented by
`OddMath.SKM.chevalleyTwo` in `SKM/ChevalleyTwo.lean`; graded/enveloped
versions include `chevalleyQTwo` and `chevalleyQReverseTwo`. The missing
formal work here is the concrete module action and its target-side
super-opposite transport, not a new proof of BE2's source symmetry.

### Ordinary opposite versus super-opposite coefficients

The ordinary reversal used in the projectivity proof sends the even-cutoff
parameter d to −d. This is not the whole rule for the present transport.
For an odd generator x in the super-opposite algebra,

`(x^sop)²=−(x²)^sop`.

For example, setting `X=x^sop`, `D=d^sop`, the image of an even-cutoff
polynomial is

`C(−X²)−XD q(−X²)`.

After monic normalization its even coefficients are
`χ_j'=(-1)^j χ_j^sop` and its odd parameter is `d'=−D`.
For an odd cutoff the image of `(x−d)C(x²)` is
`(X−D)C(−X²)`; after monic normalization the same even coefficient change
applies but `d'=D`. These are presentation comparisons for the
super-opposite algebra, not a license to omit the signs on crossings or
adjunction maps. The abstract transport above avoids any ambiguity by
retaining the opposite target throughout.

## The Hom family: two orientations without a new highest-weight algebra

The even declarations `Categorification.TwoRep.RouqFamily.homProduct`
and `Categorification.KLR.Unfurling.coverProduct` have been compared.
Their actual object is

`X(x₁,x₂)=Hom_B(T(−x₂),W(x₁))`.

Both input families may be lowest weight. Postcomposition with W gives
the first collection of colours. Precomposition with T, through a
horizontal-opposite/reverse construction, gives the other orientation.
Thus using H_Λ as a separately constructed highest-weight tower is not
required by this particular Hom construction. It remains useful as a
signed comparison and for alternate targets.

This horizontal opposite is different from BE2's sop above. In a super
Hom construction, odd natural transformations from opposite sides exchange
with the Koszul sign. Simply invoking the ordinary associator calculation
from the even implementation only checks the even skeleton. One needs
super Yoneda, the reversed adjunction and inversion maps, and the mixed
crossing maps with super-interchange. Those are new formal obligations.

For lowest-weight cutoffs Λ_W,Λ_T the two vacuum components are
`x₁=−Λ_W`, `x₂=Λ_T`. Their projected total weight is `Λ_T−Λ_W`.
Every integral weight is such a difference provided the chosen weight
lattice contains a sufficiently dominant integral weight (in particular,
for a usual realization with fundamental weights and finitely many
colours). More concretely choose a dominant δ with all coroot coordinates
positive; then λ+nδ and nδ are dominant for large n, and their difference
is λ. If the datum's lattice does not supply such a δ, this is an additional
coverage hypothesis, not a consequence of symmetrizability alone.
Odd coroot coordinates may have either parity, which is why both cutoff
parities must be available.

Nonvanishing of the Hom vacuum is also a condition on the chosen ambient
bicategory, not a formal consequence of having two nonzero categories.
A concrete candidate is the bicategory of coefficient superalgebras and
bimodules, with the free tensor bimodule between the two vacuum algebras.
One must check its permitted finiteness/projectivity class and the
super-interchange conventions before using it as the detection object.

## What the weight calculation does not prove

`homProduct` acts for the **product root datum** with separate colours on
the two sides. The linear map `(x₁,x₂)↦x₁+x₂` does not on its own make it
an action for the original datum. In the even comparison, `coverProduct`
uses disconnected spectral sectors and the subsequent furling construction.
Webster, arXiv:1603.06311v3, proof of the theorem labelled `nondegenerate`,
separates the signed collections of components before reversing one of them.

Thus the lowest/highest constructions do not solve the remaining
original-datum fusion problem. A super fusion theorem must construct the
cross-sector crossings and the inversion matrix with the original
parameters, and then show that the chosen vacuum detects upward diagrams
and normalized bubble products. GeneralRoute.md records that separate
obligation. Neither Chevalley transport nor a difference-of-dominants
argument proves it. No Clifford cover or multicolour confluence assertion
is used in the construction here.
