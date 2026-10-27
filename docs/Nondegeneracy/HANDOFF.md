# Odd nondegeneracy: restart state

## All-prefix cyclotomic relation killing

`IntertwinerRelation.lean` proves `allPrefix_relation_tmul_zero`: for every
finite prefix `ν`, moving colour `i`, and ambient left multiplier,
`f_i(x₁) T_|ν| V_(|ν|+1)` on `(i,ν,i)` vanishes in the prescribed prepend
balanced tensor with coefficient `qCoefficient`. The bare prefix is the
recursive morphism `lastToFirstHom`; the theorem includes the empty prefix,
repeated colours and arbitrary spectator parities. Polynomial parity is
unchanged, so odd cutoffs and cubic odd-colour polynomials are allowed.

`append_move_factor` reuses established moving-strand naturality and retains
the parity involution on the entire old expression. The stronger
`append_relation_move_tmul_zero` permits arbitrary inhomogeneous old factors
on both sides of the relation. `prepend_kernel_tmul_zero` kills the resulting
old quotient-kernel element by balancing, rather than assuming relation
vanishing or using flatness. `prefix_relation_move_tmul_zero` supplies the
typed word representative in the target of `parityCyclotomicContentQ`.

This closes the relation-killing step for the existing ordinary-polynomial
coefficient implementation only. Signed polynomial transport and the
inductive QP calculation remain; no global QP, full coefficient-superalgebra
extension, ideal-sum equality or projective resolution is asserted.


## Signed linear dot cancellation

`LinearDotCancellation.lean` proves injectivity of `targetRightDot -
targetRightCoefficient z`, where `z` is the cyclotomic image of the old
`affineLastDot`. The odd dot anticommutes with this coefficient, so the
square is `targetRightDot² + targetRightCoefficient (z²)`. At even colour
the complementary product instead gives the difference of squares.
`contentTargetRightDot_sub_lastDot_injective` transfers cancellation through
`contentTargetEquiv` into its fixed-projector submodule, not an equivalence
onto the full target. No domain, flatness, monicity or nonzero-quotient
hypothesis is added. Height zero and odd cubic shifts remain included.

This is cancellation only. The all-prefix relation-killing step is now
proved above for ordinary polynomial coefficients; signed polynomial
transport and induction needed for global QP remain. No global QP,
projective resolution or full nondegeneracy conclusion follows here.

## Supernatural postcomposition augmented inverses

`RouquierHomPostNaturalInverse.lean` proves signed naturality against arbitrary
homogeneous probe morphisms, including odd ones, for the prescribed dot
powers, mate, cups, caps and both families of inverse entries. The even
source and target coordinate comparisons are natural isomorphisms; the
inverse entries are transported from the specified factor maps, with the
original right adjoint `N S`. Every raw natural-number inverse entry is
retained, while product identities use the finite height window.

`RouquierHomPostSuperInverse.lean` constructs `homContentPostSuperInvPos`
and `homContentPostSuperInvNeg` in the existing SCat Hom category. All five
identities are lifted by homogeneous component extensionality, and the two
zero-height principal inverses agree as supernatural transformations. The
principal map equals the actual ordered cup–crossing–cap mate. The even
natural lifts use literal `homParityShiftDatum` comparisons, including the
identity summands, not unsigned shift identifications. No object-category
biproduct hypothesis is needed.

This closes the natural-transformation packaging of the same-colour local
augmented inverse. It does not supply the remaining fields of a full Hom
Rouquier family, mixed-sector braid relations, fusion, negative dot powers,
or a nonzero factor model in Lean.

## Pointwise content-shifted postcomposition inverse

`RouquierHomPostInverse.lean` constructs `homContentPostInvPos` and
`homContentPostInvNeg` from the specified factor inverse and the checked
principal and dotted-entry comparisons. All five finite-window products
and homogeneous parities hold over a commutative ring, at every content
and height. The forward maps remain the prescribed mate and dotted unit
or counit, rather than maps defined by conjugation.

The even-component theorems retain the literal parity-shifted identity
summands, including their diagonal and off-diagonal products. The principal
inverse, inverse rows and columns have explicit factor-coordinate formulas;
the zero-height presentations agree. These pointwise data are lifted to
supernatural transformations by the modules above. Fusion and construction
of a nonzero factor model in Lean remain separate.


## Input-side prepend decomposition

[PrependCoordinates.md](PrependCoordinates.md) records the construction for
the whole affine prepend corner at all heights, including height zero.
`PrependEquivalence.lean` now checks this affine coordinate equivalence.
Inverting `parabolicEquiv` yields the unique factorization
`w = d_j * blockPerm 1 v`; the input dot list splits uniquely into zeroes
and shifted old dots. Unitriangularity then gives spanning and independence,
and associativity proves right-old-algebra compatibility. Explicit balanced
forward and backward maps are supplied in the written argument; no flatness,
projectivity, diagram reflection or coefficient centrality is assumed.

`InputParabolic.lean` checks `prependPermutationEquiv`,
`length_prependPermutation` and `prependCrossingWord_spec`.
`CyclotomicAction/PrependCoordinates.lean` constructs the finite crossing
sums `prependShuffleElement` and the prescribed terms `c_j x^m φ(b)`.
`prependPBWTerm_corner` and `prependPBWCorner_right` check these terms in
the existing corner and right action. The consumer also exercises the
existing `qCoefficient` right action at the corresponding tensor terms.
The whole corner has free old-algebra coefficients in the written proof;
a fixed target word instead has idempotent-summand coefficients.

`PrependBasis.lean` now checks the input leading-index equivalence
`PrependIdx.leadEquiv`, the concrete chronological diagram comparison
`prependElt_eq_comp`, and `prependElt_approx`. Applying `basisOfTriangular`
gives `prependBasis`, a scalar basis of each `Hom(i :: s,t)`, including
height zero and repeated colours. Its old coefficient is the existing
normal form `PrependIdx.old.nf`.

`CyclotomicAction/PrependMatrix.lean` identifies the scalar prepend diagrams
with matrix terms: `prependPBWTerm_old_nf` sends the single old normal form
to the single `prependElt`. The intermediate formula `prependPBWTerm_single`
is valid for every old morphism and new exponent, including zero.
`prepend_single_expansion` gives the resulting finite expansion of every
allowed matrix entry, with scalar coefficients from `prependBasis.repr`
and single old normal forms as the old-algebra coefficients.

`CyclotomicAction/PrependEquivalence.lean` regroups finite scalar entry
expansions into old-algebra coefficients. `prependExpansion_projection`
identifies reassembly with multiplication by the actual prepend idempotent,
and `prependExpansion_injective` recovers coefficients using `prependBasis`
and `basisNF`. Thus `prependCoordinateEquiv` is the literal finite sum of
`prependPBWCorner`, with both round trips and forward/inverse right-action
laws. Its consumer includes repeated colours, old dots and a nonidentity
permutation, height zero, and exponent zero.

`PrependTensorCoordinates.lean` now checks the balanced extension (9):
`prependTensorEquiv` is an explicit additive equivalence for every unital
left old-algebra module, including height zero. The maps are the finite
sum of elementary prepend tensors and the balanced affine-coordinate
extraction, with both round trips proved without flatness.
`PrependCoefficientCoordinates.lean` specializes to the prescribed shifted
`qCoefficient` at affine height r+1. `qPrependTensorEquiv_symm_insert`
retains its parity involution; `qPrependTensorEquiv_symm_right` identifies
the prescribed right cyclotomic action coordinatewise. These are additive
and right-coefficient comparisons, not assertions of a new ambient action,
k-linear tensor structure, or tensor grading. Content comparisons remain
projectors on the uncut tensors. The degree-two raising formula and
coefficient-difference cancellation are checked below.

## Prepend square-dot operator and coefficient cancellation

`IntertwinerSquareDot.lean` checks the square operator needed for KKO I,
arXiv:1206.5933v2, Lemma 8.1 and Theorem 8.5. `affineFirstDot_sq_comm`
commutes the first-dot square with every old affine element, including at
height zero. `targetRightDot_sq_tmul` identifies the square of the existing
shifted right dot on `InductionAlong.Ind` with two first-dot corner actions
and the unchanged `qCoefficient`. `targetDotCorner_twice_val` identifies
that corner value with right multiplication by the first-dot square.
`contentTargetRightDot_sq_tmul` proves the same cancellation of the
coefficient involution on the unital content tensor. These require only
the existing finite colours, scalar datum, commutative ground ring and
polynomial homogeneity; no monicity or projectivity assumption is added.
The tensor statements retain positive coefficient height. The consumer
uses an odd-degree cyclotomic polynomial and arbitrary height and content.

`PrependDotCancellation.lean` checks `prependPBWTerm_mul_sq` using the
prescribed order `c_j x^m φ(b)` and whole-old-algebra square commutation.
`targetRightDot_sq_prepend` and `qPrependTensorEquiv_symm_sq` identify the
existing shifted right-dot square with raising m by two in the additive
balanced coordinates. `targetRightDot_sq_sub_coefficient_injective` then
proves injectivity of the square minus the existing right coefficient
operator for arbitrary cyclotomic c; `targetRightDot_sq_sub_lastDot_sq_injective`
specializes to the prescribed last-dot square. The proof uses a maximal
occupied exponent in finite support, not tensoring scalar independence.
It keeps all shuffle indices, repeated colours, polynomial parity and the
shifted coefficient at affine height r+1. The consumer includes odd cubic
polynomials, an odd coefficient shift, odd dot anticommutation, multiterm
families, last-dot-square and nonhomogeneous coefficients, and zero boundaries.

The next step is to identify the odd linear difference and its square
(the sum of the prescribed dot squares), then use this cancellation in
the global QP argument. The coefficient-difference theorem permits negative
coefficients as well; it does not itself identify that square or supply
the QP map identity. Reversing the difference changes its leading sign
but not injectivity. The old-dot contribution is the coefficient right
action, not a right-linear endomorphism of the noncommutative old algebra.
The empty old word
has no old last dot and is the separate base case of the QP induction,
not a case of cancelling a difference of a dot with itself. The proposed
arguments in `DeformedGlobalQP.md` and `DeformedProjectiveResolution.md`
still require their remaining operator identifications and QP induction. No all-height QP,
projectivity, literal P, or full coefficient-extension theorem follows.

## Repeated-odd two-strand cyclotomic error

`IntertwinerError.lean` proves the local quotient reduction needed in KKO I,
arXiv:1206.5933v2, Theorem 8.5 for the word `[i,i]`, with `p(i)=1`.
For `D=v²-u²`, `S=u²+v²`, the existing odd intertwiner `g` gives
`K=Tg-S=S-D(v-u)T` and `H=v²+2uv-u²-(v+u)DT`.
`error_pow` proves `u^m K = (if Even m then K else H) v^m` for every natural
exponent. `error_polynomial` yields the corresponding right factorization
for a central-coefficient polynomial supported in one parity.

`repeatedOddError_factor` instantiates the presented quiver Hecke dots and
crossing, using `oddTwo_block`; endomorphism products reverse composition.
The existing `CyclotomicPolynomialParity` condition is **homogeneity**, not
necessarily even support: odd degree uses H, even degree uses K. No extra
even-degree, monicity, nontriviality or domain hypothesis is imposed.
Constants and the zero polynomial are included.
`prepend_generator_single` identifies the right factor with the shifted old
cyclotomic generator, including its constant term. Balancing in the existing
`InductionAlong.Ind` over `prependAlgebra`, with the existing `qCoefficient`,
gives `repeatedOddError_tmul_zero` for arbitrary left multipliers and shifted
coefficients. Thus the local reduction requires neither inversion nor
cancellation of a dot difference.

This is not a literal Q∘P theorem: P and its `T_i^{Λ_i}` source have not been
constructed. The source's projectivity argument, full multicolour prefix
induction, and super coefficient polynomials remain separate obligations.
The consumer checks arbitrary monomial exponents, zero, and a polynomial
with several even terms and a nonzero constant, in the prescribed tensor.

## Content-tensor right dots

`IntertwinerContentDot.lean` constructs the source last-dot and shifted target
first-dot maps directly with `InductionAlong.Ind.lift` over `ContentAlgebra`.
The even central content identity is fixed by the parity involution; its
restriction pairs the corner dot with the coefficient involution in the
balance proof. No tensor action is defined by equivalence conjugation.
`contentTargetRightDot_insert` retains `(-1)^(p(i)p(β))`, the first dot and
`φ_i` on the coefficient. The forward comparisons commute with the existing
content-dot maps, and `contentTensorShiftedQ_rightDot` closes the dot generator
of KKO I, arXiv:1206.5933v2, Proposition 8.4 alongside the coefficient theorem.
The scope remains finite colours, positive coefficient height, polynomial
parity and an arbitrary commutative ground ring, without nontriviality or
signed-left premises. No graded comparison, zero-height extension, full ELV
coefficients or QP conclusion is asserted.

## Independent right coefficient descent

`IntertwinerContentCoefficient.lean` defines the right operators directly by
`InductionAlong.Ind.map`: source coefficients are multiplied in the unital
cyclotomic content corner, and the target restricts the existing shifted
right action to `qContentCoefficient`. Centrality gives source closure;
commutation with the existing affine left action gives target closure and
well-defined balancing. Neither operator is defined by equivalence conjugation.
The pure-tensor formulas, compatibility with `sourceContentRightCoefficient`
and `targetContentRightCoefficient`, and reverse composition law are proved.
`contentTensorShiftedQ_rightCoefficient` intertwines these operators for the
existing prescribed moving-strand Q. Finite colours, positive coefficient
height, arbitrary commutative ground ring and polynomial parity are unchanged.

This supplies the coefficient generator of KKO I Proposition 8.4; the dot
generator and its first-dot/involution sign are supplied above.
No signed-left-linearity premise is needed.
The consumer checks all-odd and mixed data and audits every owned declaration.

## Shifted target tensor over the content algebra

For KKO I, arXiv:1206.5933v2, Proposition 8.4,
`IntertwinerTargetTensor.lean` defines `contentTargetTensor` independently of
`qTargetContent`: the first factor is the prepend left ideal over the unital
`ContentAlgebra`, and the second is the content submodule of the existing
`qCoefficient`. Its action is restricted from `qCoefficientModule`, retaining
the parity-shift twist; no ring structure on the shifted coefficient is used.

`contentTargetForward` includes both factors; `contentTargetBackward` cuts
both by the content identity. `contentTargetBackward_forward` is identity,
and `contentTargetForward_backward` is the existing target content projector,
not identity on the entire height tensor. `contentTargetEquiv` gives the
explicit two-sided comparison. `qContentCoefficientCut_insert` and
`contentTargetEquiv_cut_tmul` identify the cuts with the prescribed shifted
representatives. `contentTensorShiftedQ_representative` proves the literal
moving-strand formula between the separately defined source and target tensors.

Hypotheses remain finite colours, positive coefficient height and polynomial
parity over the existing commutative ground ring and scalar datum. These are
underlying left-module statements, not a graded identification. The direct
right coefficient and dot actions and their Q compatibilities are supplied
above, retaining the first dot, involution and `(-1)^(p(i)p(β))`. Enlarged target-block
support, graded comparison, zero height, full ELV coefficients and QP are
separate obligations.

## Source tensor over the content algebra

`contentSourceEquiv` in `IntertwinerContentTensor.lean` identifies the KKO I §8 source
`R(β+αᵢ)e(β,i) ⊗[R(β)] RΛ(β)` with `qSourceContent`. Both coefficient
algebras use Mathlib's unital idempotent corners; the coefficient action is
the existing quotient map restricted to those corners. The append left ideal
is supported on content `β+αᵢ` (`contentSourceCorner_support`).
The forward map includes both factors. The inverse cuts both factors by their
content identities, is balanced over the unital corner, and has two checked
composites: identity on the source tensor, the content projection on the
height tensor. No arbitrary choice of equivalence or new action axiom is used.
`contentTensorQ_representative` gives the existing moving-strand formula on
this source carrier. Finite colours and positive coefficient height remain;
polynomial parity is needed only for Q.

The shifted target comparison and right coefficient/dot compatibility on
both tensor carriers are supplied above. The
zero-height case, QP and full nondegeneracy are not consequences of this step.

## Bounded cyclic recovery

`upwardCoefficientMap_injective_of_bounded_cyclic_recovery` consumes, for each
fixed pair `t,t′` and degree `d`, one `BoundedCyclicRecovery` at a colourwise
cutoff bounded below by `N > d + 2 * choose(length t, 2)`. It derives the pure
coefficient observation from source precomposition and the normalized
elementary/exterior bubble formulas, extends over `extensionBasis`, and applies
C0 with the unchanged word indices. The theorem works over a commutative ring.
No windows at other pairs or inadmissibly small cutoffs are required; degree
zero still requires recovery, including identities and crossing-only vectors.
The concrete two-colour importing consumer is conditional: construction of
the cyclic action, normalized bubbles and bounded affine recovery remains open.
No nonzero model or nondegeneracy theorem is asserted.

## Content-shifted postcomposition coordinates

`RouquierHomPostCoordinates.lean` bundles the specified
`homContentPostAdjunction` in `SCat`, with right adjoint `N S`, not its
output-shifted replacement. `homContentPostWordIso` is the prescribed
`S(beta_M⁻¹);xi` comparison followed by the even postcomposition associator.
`homContentPostCrossing` transports `W.cross i i h h₂ h h₂` with no scalar gauge.
Its component and parity are proved.

`homShiftConjugationIso_supernatural` proves cancellation of both comparison
signs, for arbitrary shift and homogeneous transformation parity.
`homContentPostFactorCrossing_shift` specializes this to the prescribed factor
crossing. The specified unit and counit have coordinates `u;b⁻¹` and `a;v`,
proved by `homContentPostAdjunction_unit_coordinates` and
`homContentPostAdjunction_counit_coordinates`. The source coordinate has the
signed two-removal formula `homShiftConjugationIso_hom_signed`; its factorization
is `homShiftConjugationIso_comp`. `homShiftConjugationIso_unit_cancel` cancels
the inner shift-square against the shifted word comparison.

`RouquierHomPostPrincipal.lean` now proves equation (B) as
`homContentPostCrossing_principal`: the source-coordinate inverse, specified
`rouquierMate`, and target coordinate compose to
`associator.hom; Z ◁ (W.loc i h h₂).sig; associator.inv`.
The proof cancels the shift comparisons inside the literal mate, then uses
even prefix/suffix coherence and crossing naturality. It covers arbitrary
content, every weight and both parities over a commutative ring; no comparison
premise is added. Odd-colour consumers apply this equality at odd and zero
content shift, jointly importing the normalized precomposition principal
theorem. The Rouquier family remains an input.
`RouquierHomPostPowers.lean` proves the natural-power part of §3 (9):
`homContentPostCup_coordinates` and `homContentPostCap_coordinates` identify
all dotted entries with the literal factor unit/counit words, including their
whiskering and associators. `homContentPostDot_power` identifies powers of the
prescribed shifted dot with shifted raw powers. Both comparison signs cancel;
no transpose sign or invertibility assumption is introduced. These theorems
apply to every finite window, both colour parities, all content and weights.
The importing consumer checks both parities, zero and odd content, and powers
zero and three, and audits every declaration owned by the module.
The pointwise whole augmented inverse and literal parity-shifted summands
are now checked as described above. Negative powers, natural inverse
packaging, swapping mates, fusion and a nonzero model remain separate.


## Raw normalized Hom mate coordinates

`homContentCrossing_coordinates_raw` proves cancellation of both comparisons
in the **defined** mate, with no additional premise. Its source is
`E_h ≫ F_h ≫ Z` and target is `F_h₂ ≫ E_h₂ ≫ Z`. It retains the raw cup,
the inherited crossing evaluated at `F_h ≫ Z`, and the normalized cap
with coefficient `leftAdjScalar i (-nuP)` inverse, not the lower-edge scalar.
The odd rank-one consumers specialize to arbitrary weights and height zero;
they take a Rouquier family as input, not a constructed nonzero model.

The proof first moves the input inverse through the even normalized unit
by ordinary naturality. Crossing supernaturality and the signed counit
give `koszulSign p sigma * koszulSign sigma sigma`. The remaining
unshifted map has parity `p + sigma`; output removal contributes
`koszulSign sigma (p + sigma)`. Their product is one, using edge parity
agreement. Thus no parity comparison or shift functor remains.

## Normalized principal Hom comparison

`homContentCrossing_coordinates` proves (10) of `HomPrincipalMate.md`:
the defined normalized mate in raw coordinates is the insertion of
`(T.loc i h₂ h).leftCrossingWord`, scaled by `-koszulSign p p` and
`leftAdjScalar i (-nuP)` inverse. Its even reassociation uses naturality
and structural coherence without swapping the cup, crossing or cap.

`homContentCrossing_principal` combines this equality with
`RouquierFamily.leftCrossingWord_eq` and `principalWord_scalar` to give
`D_H = gamma(k) P_(-sigL)`, with gamma(k)=(-1)^(p*k) for nonzero k and
gamma(0)=(-1)^p. Both parities and every integer height are covered over
any commutative ring. Odd rank-one consumers check arbitrary height and
height zero, where the component is the insertion of `sigL`.
No new coherence, scalar-evaluation or triangle hypothesis is imposed.

The remaining targets are the shifted swapping mates, their tensor
support, the residual identity-summand matrix, fusion and joint separation.
No whole-matrix or nondegeneracy consequence is claimed here.

## Inherited Hom crossing and its specified mate

`RouquierHomCrossing.lean` defines `homContentCrossing` using the inherited
same-colour `T.cross`, multiplied by `-koszulSign p p` and conjugated by
the even precomposition associator. `homContentCrossing_app` computes every
component and `homContentCrossing_mem` proves parity p.
`homContentCrossing_mate_app` specializes the SCat mate bridge to this
crossing and expands both normalized adjunction components. It retains
both parity comparisons, the counit sign, and c(k) inverse at the cap edge.
The output/input comparisons now cancel by
`homContentCrossing_coordinates_raw` in `RouquierHomMateCoordinates.lean`.
Equation (10) and the principal word comparison are proved above.
The consumer specializes the expanded mate to the odd
rank-one datum at arbitrary weights; no nonzero model is constructed.

## Normalized Hom adjunction in SCat

`RouquierHomSuperAdjunction.lean` packages the specified
`homContentPreAdjunction T W T.leftAdjoints` as `homContentSuperAdjunction`
in the existing `SCat` 2-supercategory. The unit and inverse-scaled counit
are proved even from their normalized formulas; no new zigzag premise is used.
`rouquierMate_scat_app` unfolds the defined mate, and
`homContentSuperAdjunction_mate_app` specializes it to these Hom adjunctions,
giving the literal unit–mapped crossing–mapped counit component at either parity.
The general bridge accepts an arbitrary crossing; the inherited specialization
is given above. Both shift removals are proved in the raw coordinates above;
`HomPrincipalMate.md` (10) is proved above. All heights, the existing normalization c(k), and gamma(0)
are unchanged. The odd rank-one consumer uses arbitrary weights; it does
not construct a nonzero family.

## Unit output comparison

`homContentPreAdjunction_unit_output_coordinates` removes the output shift
following the specified normalized Hom unit and a homogeneous map of parity q.
It retains the factor `koszulSign sigma q` and all cup associators. Its
odd rank-one consumer allows every height and either parity. This first
shift cancellation is now used in `homContentCrossing_coordinates_raw`
with the prescribed crossing and counit. The input comparison cancels
there as well; equation (10) is proved by `homContentCrossing_coordinates`.

## Unnormalized principal word

`RouquierPrincipalWord.lean` proves `HomPrincipalMate.md` §3 (11) at every
integer height: `RouquierFamily.leftCrossingWord_eq` gives coefficient one
at nonpositive height and `koszulSign p p` at positive height. The proof uses
the signed cup/cap pitchforks and the proved canonical F triangle; no new
left-triangle or principal-comparison premise is added. Local nonnegative
and nonpositive theorems overlap at zero and keep its exceptional pitchfork
coefficient. `principalWord_scalar` proves (16), retaining gamma(0)=(-1)^p.
The importing odd rank-one consumer checks arbitrary heights and -1, 0, 1.

The specified shifted Hom mate is identified with this word by
`homContentCrossing_coordinates` and evaluated by `homContentCrossing_principal`.
No whole-matrix, fusion, or separation theorem follows here.

## Residual windows and execution-order comparisons

`HomResidualWindows.md` computes every corrected central Schur window and
the leading comparison `S mod J = L H Q`, with the nilpotent ideal generated
by positive-degree reservoir supercentral coefficients. The original factor
inverses, c(k), gamma(0), parity lifts and every identity summand are retained.
At zero total height the residual is generally nonempty.
`ProbeWindowInverse.md` supplies a finite two-sided inverse algorithm for
the displayed negative-power probe-window matrices H at every pair of
heights, using the specified whole probe inverse, invertible dots and the
literal mate slide. It retains both nonempty zero-total cases and all
parity lifts. Lifting this inverse to the exact residual and constructing
the required localized factor actions remain separate tasks.

`ExecutionBraidNormalization.md` proves the reversal identity
`-C_ij(z,y,x)=(-q_i)C_ij(x,y,z)` and the conditional even rational comparison,
without changing Q. `ParitySectorComparison.md` gives the actual signed
word removals, the forced conditional identification `H_BA=J^-1 h k`, and
one odd AAB braid component. It does not supply the sorted-sector h or
the complete odd/localized comparison. These are written calculations, not
Lean theorems or a full fusion proof.

## Reservoir dotted coordinates

`RouquierHomReservoirPowers.lean` proves `HomSectorTransport.md` §2 (5)
for all natural powers and every reservoir source height. The dot is the raw
`T.dot ▷ Z`; cups and caps are defined using the same normalized
`homContentPreAdjunction T W T.leftAdjoints`. Removing the output comparison
from the cup gives `koszulSign σ (n*p)` times the raw dotted cup. Moving the
cap comparison past the dot power gives `koszulSign σ (1+n*p)` times the raw
dotted cap, retaining `leftAdjScalar⁻¹ • leftCap`. The power has parity `n*p`,
and its naturality is proved for every homogeneous map, not only even maps.
These are window coordinates for the Hom principal and central comparisons;
no principal-block identification, window inverse, or fusion comparison follows
from these formulas alone. The consumer checks arbitrary odd rank-one heights
and powers, and powers zero, one, and two at nonzero output shift.


## Fixed normalized reservoir adjunction

`RouquierFamily.leftAdjoints` now uses the explicit involutive unit
`leftAdjScalar i x = koszulSign σ σ * (if h < 0 then 1 else koszulSign p p)`
at the source height h, with unit `leftCup` and counit `leftAdjScalar⁻¹ • leftCap`.
Both triangles follow from the canonical triangles; no chosen-scalar uniqueness
or faithfulness is used. `RouquierNormalizedHomAdjunction.lean` specializes the
existing `homContentPreAdjunction` without an additional `LeftZigzags` premise.
It proves the reduced cup/output-shift unit formula and the signed-cap counit
formula of `HomSectorTransport.md` §2. The theorem
`homContentPreAdjunction_leftAdjoints_counit_app` retains the outer
`koszulSign σ σ`, with σ at the reservoir source height, and the inverse-scaled
`leftCap`. Homogeneous comparison naturality cancels the shift-square and
commuting maps; the normalized adjunction itself is unchanged. The odd rank-one
consumer checks this component for arbitrary heights and audits all owned
declarations. No fusion or nonzero model is claimed.

## Canonical F triangle and shifted left adjunctions

`OddMath.SKM.reflection_triangle_scalar` in `RouquierFTriangle.lean`
proves the cup/cap reflection scalar product at every integer height by the
binomial recurrence and involutive signs, including the separating height -1.
`SuperRouquierLoc.leftAdj_triangle_F` applies the E triangle to the explicitly
reflected local data, with the derived reflected crossing squares and braid.
It reads back the horizontal-opposite unitors, associator and whiskerings,
then cancels the canonical cup/cap scalar product. Its coefficient is
`koszulSign σ σ * (if h < 0 then 1 else koszulSign p p)`, where `σ=p(h+1)`.

`RouquierFamily.leftZigF_eq` specializes this to every family edge;
`RouquierFamily.leftZigzags` discharges the existing two-triangle condition.
`RouquierFamily.leftAdjoints` normalizes the cap by the explicit involutive scalar.
There is no new cyclicity, faithfulness or left-triangle hypothesis. The
rank-one odd consumer checks arbitrary heights and the boundaries -1 and 0,
and audits every declaration owned by the new module.

This closes the triangle obligation of `SignedFTriangle.md`, not the existence
of a nonzero odd inversion model, the multicolour action, fusion or separation.

## Content-shifted probe augmented inverse

`HomProbeMatrix.md` supplies a written proof of the probe comparison
(B), without assuming the shifted sector's inverse. For fixed reservoir
content, the prescribed Koszul transport is
`Theta=S(beta_M^-1);xi=S M(z_kappa(M-));z_kappa(MM-)` and
`T_BB=Theta;post(t_B);Theta^-1`; the dots are `S(post(x_B))`.
The explicit unit--map--cap computation gives
`B_s^-1;P(T_BB);B_t=post(sigma_B)` with scalar one. The intermediate
four-strand comparison has endpoint signs `(-1)^kappa` twice and crossing
exchange signs `(-1)^(kappa p)` twice, all cancelling.

All dotted cups/caps retain their raw coordinates, also for negative powers
of the invertible probe dot. Both whole augmented matrices and inverses are
transported, with explicit z lifts on every parity-shifted identity summand;
at zero height the empty-window inverse has no exceptional scalar.
Consequently `I_B=B_t;post(R_B);B_s^-1` and
`Rcal_B=post(R_B)`, conditional only on the specified probe factor local
inverse data and coherent crossing prescription. No bare-crossing inverse
is asserted at nonzero height. This discharges the separate probe-sector
input of `HomCentralFeedback.md`; it does not establish or independently
validate that note's central nilpotence result. The literal C/D convention,
residual inversion, grading and full fusion remain separate. No Lean theorem
is added by this written calculation.

## Equal-colour crossing normalization and central feedback

`CrossingNormalization.md` derives the repaired mixed equal-colour matrix
`[[-q a,J],[-J^-1 a^2,q J^-1 a J]]`. With execution AB (reservoir first),
the previous diagonals gave -q, not 1, in the fixed library slides. That
claim is withdrawn. Both slides and the square are derived using the
specified J/dot transport; the swapping maps, factor crossings, dots and
adjunctions are unchanged. This is a written two-strand correction,
not a Lean theorem. The scalar sector-inversion gauge explains the local
sign change but needs a consistently signed comparison family; the even
rational comparison and its mixed-colour braid correction remain open.

`HomCentralFeedback.md` retains the historical literal series C,D and all
shift coordinates. The corrected literal entries are Cnew=-q C,Dnew=-q D;
C,D are normalized corrected mates, as in `FusedFeedbackComparison.md`.
Feedback is unchanged. It factors through the intrinsic left closures
`U_r;f;V_s`, retaining c(k), gamma(0)=q and every inverse identity window.
Their positive reservoir degrees prove fixed-content feedback nilpotence
conditional on the specified factor actions and finite homogeneous coefficient
quotients. `HomProbeMatrix.md` supplies the probe augmented inverse. No probe
grading or uniform infinite-weight-fiber bound is used. The all-height residuals use
`Knew=-q [[0,C],[D,0]]`, not the historical K; they are not inverted.

Next checks: actual cap/cup residual coordinates and
inversion; rational/source/localization braid comparisons, coherent integer
word shifts, full (TC), fusion and separation. No full-action claim follows.
The older restart paragraphs below are historical where superseded here.

## Content-shifted swapping mates

`HomSwappingMates.md` evaluates the two swapping partial mates of the
specified upward matrix, by unit–map–cap words and the normalized snakes.
With kappa'=kappa+p, the raw mixed coordinates are
`(-1)^(sigma kappa') h_A` and
`-(-1)^(kappa p) h_B;g_B`, where, for an odd colour,
`g_B=(X²-W²)(X²+W²)^(-2)` and W is the right-transposed probe dot.
The xi signs and every parity-removal map are retained. Finite geometric
series give g_B inverse, and the note writes both inverse composites for
both shifted maps. Their projected supports contribute no additional
Schur term to the same-sector central block.

This is a written derivation conditional on the accepted normalized
left snake, not a Lean theorem. It supersedes the swapping-mate open
obligations in the historical paragraphs below, but not full (TC).
Central C,D/feedback transport must still include the principal inverse
`gamma(k) f`, particularly `gamma(0)=(-1)^p`, all dotted windows and
homogeneous comparisons. The chosen upward normalization has swapping
degrees 0 and -4d on the presently specified functors: a common degree
-2d requires an additional coherent integer word-shift construction.
No such construction or probe integer grading is assumed here. Residual
inversion, fusion relations and separation remain open.

## Principal component of the reversed Hom matrix

`HomPrincipalMate.md` derives the unbundled same-colour Hom crossing as
`-(-1)^p` times the inherited reservoir crossing from the reversed-slot
KLR slides. In the specified normalized-left Hom adjunction, all four
shift-removal signs cancel. Signed cup/cap pitchforks then give
`C_src^-1;P_H(tau_H);C_tgt = gamma(k) P_R`, where `R=-sigL`,
`gamma(k)=(-1)^(p k)` for nonzero reservoir height k, and
`gamma(0)=(-1)^p`. The exceptional zero coefficient is retained.

This is a written derivation, not a Lean theorem. Combined with the window
calculations in `ReversedReservoirMatrix.md`, the whole-matrix comparison
rescales every finite identity summand and
gives principal inverse `gamma(k) f`. The principal derivation itself
does not use those window calculations. Shifted swapping mates and their
tensor support, (TC), residual inversion, fusion and separation remain
open; a principal-entry evaluation does not establish them.

## Reversed reservoir window comparison

`ReversedReservoirMatrix.md` derives the Hom reservoir height `-k` from
reservoir height k, identifies its two mixed-word coordinates, and computes
both left dotted windows as ordered antitriangular changes of the original
inverse windows. It proves both inverse identities for the resulting
augmented matrices with principal entry `R=-sigL`; their principal inverses
are the original right mate. Integer/parity shifts, cap normalization and
heights zero and plus/minus one are retained.

These are written component calculations, not Lean theorems. That note
leaves `C_src^-1;P_H(tau_H);C_tgt` unevaluated; the separate principal
calculation above supplies its scalar relative to R without changing the
window argument. Same-height right reflection does not give this
weight-reversing comparison. (TC), shifted swapping mates, residual
inversion and separation remain open.

## Specified Hom-sector adjunction and interchange components

`HomSectorTransport.md` derives the unit and counit of the actual
output-shifted reservoir Hom adjunction and the composed probe adjunction.
The reservoir counit has the extra factor `(-1)^σ`; removing two probe
shifts with bare ζ differs from ξ by `(-1)^κ`. It gives all dotted
cup/cap coefficients and the content-changing swapping map of parity p,
using κ′=κ+p rather than identifying it with raw even interchange.

These are written derivations, not new Lean theorems. The remaining
transport comparison must identify the reversed, normalized-left reservoir
augmented matrix and principal inverse with the intended right-factor
coordinates, then evaluate both shifted swapping partial mates. Neither
principal-feedback nilpotence for the actual Hom realization nor full
fusion follows merely from these component formulas.

## Tensor feedback calculations and the remaining transport

`FusedFeedbackComparison.md` gives the six partial-mate supports, the
untwisted external-tensor rational coefficients, and the supported feedback
sign `-(-1)^(p r s)`. It proves principal-block nilpotence only under its
explicit transport condition (TC). Both augmented elimination formulas retain
the identity summands and the residual matrices at arbitrary factor heights.

These are written calculations, not Lean theorems or a fused action. Raw
even interchange is not the odd content-shifted swapping map. The actual
Hom-sector components are supplied above; reversed reservoir matrix comparison, residual
invertibility, fusion relations and separation remain separate obligations.

## Fixed-content reservoir bounds on paper

`DeformedReservoirBound.md` supplies finite-dimensional coefficient
quotients retaining the independent odd ELV parameters and their relations.
Finite right generation plus the central monic annihilator gives finite
dimension of every fixed-content algebra. The enriched supercentre then
bounds identity transformations on all modules, without asserting arbitrary
Hom-finiteness. Positive-degree principal-inverse closures are jointly
nilpotent at each content and on finite content windows.

This is a written proof, not a Lean theorem. It gives no uniform bound over
an infinite weight fiber. Component-preserving degree-zero inverse families
can assemble without such a bound, but identifying the actual fused feedback,
its tensor-factor signs and supports, the residual identity-summand matrix,
and truncation-compatible separation remain separate obligations.

## Canonical signed F triangle on paper

`SignedFTriangle.md` derives the second triangle for the prescribed
inverse-defined cups and caps by horizontal super-opposition and signed
right transposition. It constructs the reflected local data, including the
prescribed mixed mate and every inverse-component comparison; it assumes
neither cyclicity nor the F triangle. With s=(-1)^p, σ=p(h+1), and
e(h)=1 for h<0 and s for h≥0, the canonical F composite is
koszulSign(σ,σ)e(h) id. The E composite is e(h) id. Rescaling only the
cap by the involutive unit koszulSign(σ,σ)e(h) gives the shifted left
adjunction normalization of `LeftZigzags`.

This is a written proof, not a kernel-certified F triangle. The supporting
all-height E-triangle development and the first right-transposition lemmas
are included here, but the inherited cap/pitchfork chain still needs the
full-package CI gate. `RouquierRightTranspose` proves the actual counit
bending equivalence, its cup–map–cap transpose, parity preservation,
linearity, signed anticomposition, and the power coefficient
`q(n)=koszulSign p p ^ (n.choose 2)`. Its concrete local consumer
`SuperRouquierLoc.rightTranspose_capD` proves that the reflected dotted cap
is `q(n)` times the original `capD n`, at every height and parity.
The full-Hom equivalence `SuperAdjunction.unitBend` is also constructed
from precomposition adjunction, with explicit forward and inverse formulas.
`rightTranspose_unit` proves the second bending identity for the same
counit-defined transpose. `SuperRouquierLoc.rightTranspose_cupD` identifies
the reflected dotted cup with `q(n)` times the original `cupD n`, at its
original weight boundary, for every height and parity. Odd two- and
three-dot cups and caps are exercised on the prescribed composites.
No left triangle, cyclicity, faithfulness, or nonzero-model input is used.

`RouquierCompositeAdjunction` constructs `SuperAdjunction.comp` for
`E₁ ≫ E₂` with right adjoint `F₂ ≫ F₁`. Both triangles are derived by
composing the even underlying right adjunctions. `comp_unit` and
`comp_counit` identify the resulting maps with the nested units and counits,
including every associator and unitor. Its consumer applies the same
full-Hom transpose to an odd crossing at arbitrary height; no odd map is
restricted to the even underlying bicategory.

`RouquierTransposeComparison` proves the typed partial-mate comparison:
`mixedMateBend_rouquierMate` identifies `Q(P(t))` with right transposition
for `A₁.comp A₂`, and `mixedMateBend_symm_rightTranspose` gives `R(M(t))=P(t)`.
Here `P` is the prescribed `rouquierMate`; `Q` uses the existing rectangular
Hom equivalence with the adjunctions interchanged, and its inverse `R` has
an explicit unit–map–counit formula. Counit uniqueness, the composite
counit expansion and even-cap interchange prove the comparison for the
full Hom space, including odd crossings. The consumer specializes to
rational scalars, odd parity and arbitrary integral height, retaining local
inversion data as premises rather than asserting a nonzero model.

`RouquierTransposeWhiskering` proves
`SuperAdjunction.rightTranspose_whiskerLeft` and
`rightTranspose_whiskerRight` for arbitrary maps between independently
right-adjointable source and target 1-morphisms. Both composite adjunctions
are explicit. The counit-bend proof moves each arbitrary argument only past
even counits or coherence maps, so neither law carries a sign.
`rightTranspose_associator_inv` identifies the transpose of the inverse
associator with the inverse associator on the reversed adjoint string,
using the two explicitly bracketed triple composite adjunctions. Its
consumer checks both whiskered odd dots retain parity one.

`HorizontalSuperOpposite` constructs `HOpS B` and its `TwoSupercategory`
instance on the unchanged Hom supercategories, with reversed 1-morphisms,
exchanged whiskerings, inverse reversed associator and exchanged unitors.
Its interchange proof solves the original signed equation using the
self-inverse Koszul sign. `SuperAdjunction.horizontalOpposite` reflects
`E ⊣ F` to `F ⊣ E` with the same unit and counit and exchanged snakes.
The rational odd consumer retains degree-one transposed dots and verifies
the negative odd–odd interchange in the reflected category.

`RouquierHorizontalReflection` proves `rouquierMate_horizontalOpposite`, identifying
the reflected `rouquierMate` with `mixedMateBend.symm` on arbitrary maps.
Only its even prefix and suffix use underlying bicategorical coherence.
Combined with `mixedMateBend_symm_rightTranspose`, it recovers the original
prescribed mixed mate from the reflected mate of the right transpose;
the rational odd consumer checks this for a degree-one crossing.

`RouquierReflectedLocal` constructs `SuperRouquierLoc.horizontalReflection`
at the unchanged height, with transposed dots and crossing `s M(t)`.
Both signed slides follow by transposing the original opposite slide.
The prescribed mixed mate is `s` times its original, and each dotted
window entry is `q(n)` times its original. `SuperSumInvTo.rescale` and
`SuperSumInvFrom.rescale` prove all five augmented inverse equations in
both orientations, including the empty window. Inverse components are
copied explicitly; the four `horizontalReflection_invPos/Neg_f'/g'`
comparison formulas are definitional. `reflectedCross_square` transports
the nilpotent square. The rational odd consumer checks both height-zero
inverses, the negative second-window coefficient, and both boundary windows.

`RouquierReflectedBraid` proves `rightTranspose_associator_hom` by
transposing the inverse identity, and `rightTranspose_bracketed_whiskerRight`
with the explicit triple composite adjunctions. `reflectedCross_braid`
transports the bracketed three-strand braid to the prescribed crossings
`s M(t)`; the equal palindromic transpose signs cancel without any
cyclicity or left-triangle hypothesis.

`RouquierReflectedCupCap` identifies the canonical `sigL`, every `cupN`
and `capN`, the dotted right cups/caps, and both piecewise `cupL`/`capL`
with their original maps times the coefficients of `SignedFTriangle.md`
§5. All integer heights, including zero and both unused zero branches,
are retained. The consumer specializes both canonical comparisons and
the bracketed braid to odd parity over rational scalars.

Still missing in Lean are the symbolic all-integer-height scalar product
`a(h+2)b(h)=koszulSign (p(h+1)) (p(h+1))`, and application of the local
E theorem followed by explicit horizontal-opposite readback. Neither the
canonical F equation nor `LeftZigzags` is discharged yet.
Transport to fusion and regular-bubble detection remains separate.

## Full graded deformed action on paper

`DeformedActionAssembly.md` and `DeformedMixedBraid.md` complete the written
action of the full underlying SKM supercategory over the stated full-ELV
coefficient algebra. The construction includes the prescribed distinct-colour
mate, mixed quadratic parameter normalization with reversed labels, the
arbitrary-exponent corrected braid, and explicit zero out-of-range inverse
components. It uses the same-colour matrix argument below, without a further
kernel or pivot assumption. Tensoring applies to all modules, not just projectives.

`DeformedGradedAction.md` supplies the standard SKM integer grading:
E_i is unshifted induction and F_i1_λ=q^[d_i(h_i(λ)−1)] Res_i1_λ.
It transports the adjunction on each edge and checks every generator and
inverse-component degree. Infinite weight fibers use finite-bidegree Hom
families, not unrestricted products of underlying Hom spaces.
This is not a Lean implementation. Hom-finiteness, fusion, detection and
nondegeneracy remain open.

## Prescribed same-colour inversion on paper

`DeformedMackeyBoundary.md`, `DeformedBoundaryDivision.md`,
`DeformedRouquierMatrix.md` and `DeformedMatrixComparison.md` now give a
written proof that the prescribed tensor-mate/dotted-cup/dotted-cap matrix
is invertible at every height over the stated full-ELV coefficient algebra.
The odd parameters remain independent, with the required coefficient
relations; no exterior-flatness assumption is used. The cap rows require
output parity transport between explicitly twisted bimodule targets.
The kernel-window and semilinear unit-pivot calculation are proved, not
extra inversion hypotheses. The local right-factored g signs in
`DeformedProjectiveResolution.md` and `DeformedGlobalQP.md` are corrected
without changing the definitions, cancellation or final QP formula.

This is not a Lean theorem. The full-coefficient distinct-colour mate and
graded action are supplied above; fusion remains separate. The existing polynomial-coefficient Lean
implementation is narrower. The general nondegeneracy conjecture remains open.

## Deformed right projectivity on paper

`DeformedSquareResolution.md` assembles the written right-projectivity argument
from `DeformedGlobalQP.md` and `DeformedIdealSum.md`. It constructs the actual
central right `B[s]` actions and finite corner-projective PBW modules, proves
P-linearity and injectivity, identifies its cokernel, and lifts a central monic
annihilator through the nilpotent odd-parameter ideal. The coefficient twists
are retained in both raw quotient and right-B-linear tensor coordinates.
These are written arguments, not Lean theorems. Left projectivity and reverse
adjunctions remain separate; prescribed same-colour inversion is supplied above.

## Actual induced-tensor parity grading

`CyclotomicAction/IntertwinerGrading.lean` constructs `qSourceSpace` and
`qTargetSpace` on the **existing** `InductionAlong.Ind` carriers. The raw tensor
is the original integral tensor. Its odd projection is the sum of even-odd
and odd-even tensor projections. `InducedParity.relation_odd_mem` proves that
the original balancing submodule is stable, by homogeneous decomposition of
the corner, balancing algebra, and coefficient. Restricting its scalars to
`k` leaves the quotient carrier unchanged; no comparison equivalence is assumed.

`qSourceSpace_tmul_mem` and `qTargetSpace_tmul_mem` give total tensor degrees;
`qSourceSpace_smul_mem` and `qTargetSpace_smul_mem` prove grading of the actual
left action. Corner projection stability follows from the even idempotent,
and append/prepend and coefficient action grading are proved, not postulated.
The imported consumer exercises all-odd height three and mixed height two,
both with nonzero coefficient shift, and audits the module's declarations.

`contentMove_parity` now proves the matrix degree `p(i)p(β)` from
`intertwinerHom_parity` and `moveHom_parity`, including the equal-odd polynomial
intertwiner. The finite matrix sum uses its actual content support and the
order-independent multiset parity. `parityCyclotomicContentQ_even` proves
Q-evenness on these existing source and target spaces, using the pure-tensor
criterion and the two cancelling parity shifts. `parityCyclotomicContentQLinear`
is only scalar restriction of the existing Q, not a replacement map.
The consumer specializes actual Q-evenness and pure-tensor membership at
all-odd height three and mixed height two, both with shift one, and audits
all owned declarations. Right-dot degree is now proved in
`IntertwinerDotGrading`; full right-superalgebra structure remains open.
Source comparison: KKO I, arXiv:1206.5933v2, Proposition 8.4 and (8.13),
PDF page 42. Finite colours, positive indexing and
`CyclotomicPolynomialParity` are retained. Ordinary coefficients
`I → Polynomial k` are still narrower than full odd-coefficient deformations.
No full Proposition 8.4, QP formula, or nonzero categorical inversion model
is asserted.

## Finite polynomial operators on the moving-strand quotients

`CyclotomicAction/IntertwinerRightPolynomial.lean` evaluates every finite
ordered family `∑ t^m ⊗ c_m` on the same `qSourceSpace` and `qTargetSpace`.
`sourceRightPolynomial` and `targetRightPolynomial` are additive maps to
endomorphisms; their constant-unit law is proved. `rightPolynomial_Q`
proves equivariance for every such family, from the existing dot and
coefficient formulas, without any assumed action interface.

`sourceRightMonomial_comp` and `targetRightMonomial_comp` prove the
ordered multiplication law: composing the operator for `t^r ⊗ b` with
that for `t^s ⊗ c` gives `(-1)^(s p(i) q)` times the operator for
`t^(r+s) ⊗ bc`, when `b` has degree `q`. Composition reverses right
products. All natural powers are retained; odd variables are not exterior
variables. Consumers exercise odd and mixed data with nonzero target
shift, finite two-term polynomials, and both signs at exponents one and two.

`CyclotomicAction/IntertwinerSkewAction.lean` now constructs the associative
parity-skew polynomial ring using Mathlib's `SkewPolynomial` and the proved
`coefficientParityAction`. The underlying coefficient map is the sign
endomorphism `φ(c)=(-1)^(p(i)|c|)c`; its multiplicativity and unit law follow
from the existing cyclotomic grading. No action law is assumed.
`sourceRightSkew` and `targetRightSkew` are ring homomorphisms into ordinary
opposite endomorphism rings on the same induced quotients, including the
shifted target. Their multiplication law is reverse composition, and
`rightSkew_Q` proves Q equivariance for every skew polynomial.

Coefficient-first `c X^m` acts as `T^m C_c`. The `*_dotFirst` and
`*_coefficientFirst` theorems prove both order conversions: dot-first
`X^m c` is coefficient-first `φ^m(c) X^m`, with
`φ^m(c)=sgn(m p(i))(c)`. The twist is involutive, so the inverse conversion
uses the same formula. All natural powers remain; odd dots are not exterior.
The consumer checks ring products, Q equivariance, and order/sign conversion
on odd and mixed data with nonzero target shift.

`CyclotomicAction/IntertwinerSupertensorAction.lean` identifies the
scalar-balanced tensor product `k[t_i] ⊗[k] R^Λ(n)` with the parity-skew
polynomial ring. `polynomialTensorSkewEquiv` is a ground-ring-linear
equivalence, sending `t^m ⊗ c` to `φ^m(c) X^m`; its inverse monomial
formula is proved. `polynomialSupertensorSkewRingEquiv` preserves the
transported associative ring multiplication, and
`polynomialSupertensor_mul_tmul` proves the exact Koszul product
`(t^r ⊗ b)(t^s ⊗ c) = (-1)^(s p(i) q) t^(r+s) ⊗ bc` for homogeneous
`b` of parity `q`. The transported unit is `1 ⊗ 1`. The multiplication
and semiring projections are selected explicitly; the ordinary unsigned
tensor-product instances are neither used for this product nor disabled.

`sourceRightSupertensor` and `targetRightSupertensor` transport the ring
representations onto the same quotient carriers, retaining the target shift.
Their pure-tensor formulas recover the dot-first operators, and
`rightSupertensor_Q` proves equivariance for every balanced tensor.
`polynomialSupertensorAlgebra` preserves the existing tensor scalar action,
and `polynomialSupertensorSkewAlgEquiv` bundles the normal-order comparison
as a ground-ring algebra equivalence. Scalar centrality follows from the
linearity of the coefficient parity twist. `qCoefficientScalarTower` proves
compatibility of the ground-ring and affine-algebra scalar actions on the
existing shifted coefficient superspace. Neither quotient is replaced.
`IntertwinerSupertensorScalars.lean` now proves
`sourceRightSupertensor_smul` and `targetRightSupertensor_smul`: both
representations send `r • f` to `r • ρ(f)` in the existing ground-ring
endomorphism modules. Balancing transfers the scalar to the corner as
`algebraMap k B r`; the existing quotient scalar tower identifies this
with its superspace scalar action. No new quotient module is introduced.
The coefficient and skew-polynomial actions satisfy the same scalar law.
`rightSupertensor_scalarQ` gives equivariance for scalar multiples of Q.
The importing consumer checks arbitrary scalars and tensor arguments in
odd and mixed data with nonzero target shifts, and audits every declaration
owned by the scalar-compatibility module against the standard axioms.

Odd and mixed consumers check both signs at exponents one and two,
nonzero target shifts, the algebra-map identity, and definitional agreement
of the algebra scalar action with the original tensor module. This is
the balanced algebra comparison for the right action in KKO I,
arXiv:1206.5933v2, Proposition 8.4, not its complete statement.
`IntertwinerSupertensorGrading.lean` proves that the dot-first monomial
`t^m ⊗ c` with coefficient parity `q` acts with degree `m p(i) + q`.
`polynomialSupertensorPart` is the ground-ring span of these homogeneous
tensors in the existing scalar-balanced tensor product.
`sourceRightSupertensor_parity` and `targetRightSupertensor_parity` extend
the degree statement to every element of this span, including finite sums
and scalar multiples, on the unchanged source and shifted target.
`rightSupertensor_Q_gradedSquare` combines these results with the proved
evenness and equivariance of Q, without additional premises.
The homogeneous spans are not yet bundled as a direct-sum grading.
The right actions use ordinary left-module compatibility; a separate
signed-left condition is not required. The fixed-content restriction is
proved below. A separate tensor comparison over the unital content algebra,
zero-height, full-ELV coefficients and QP remain open.

## Right cyclotomic coefficients and the polynomial variable

`CyclotomicAction/IntertwinerRightCoefficient.lean` descends right
cyclotomic multiplication to the existing source induced quotient and the
shifted `qCoefficient.ract` to the existing target. The descent uses
`InductionAlong.Ind.map`: coefficient right multiplication is proved
left-affine-linear, so the integral balancing relations are preserved.
Both resulting operators remain endomorphisms over the larger affine algebra.
Their unit, product (reverse composition), zero and addition laws are proved.

`qCoefficientInsert_mul` derives right-linearity of the canonical insertion
from its superbimodule homomorphism law, with **no additional sign**.
`rightCoefficient_Q` then proves Q equivariance by its pure-tensor formula.
`sourceRightCoefficient_parity` and `targetRightCoefficient_parity` give the
homogeneous coefficient degree on `qSourceSpace` and `qTargetSpace`.
`sourceRightDot_coefficient` and `targetRightDot_coefficient` prove
`R_t ∘ R_c = (-1)^(p(i)q) R_c ∘ R_t` for a coefficient of degree `q`.
The sign comes from the coefficient parity involution, including on the
shifted target; no square-zero condition on the odd variable is imposed.

This is the right-coefficient and dot/coefficient part of KKO I,
arXiv:1206.5933v2, Proposition 8.4, with the right action setup preceding
Lemma 8.1. The consumer checks all-odd height three and mixed height two,
both with shift one, and uses a concrete odd cyclotomic dot for the grading
and supercommutation hypotheses. These are quotient examples, not nonzero
inversion models. Full polynomial-supertensor action packaging, comparison
with the source's fixed-content corners, full-ELV coefficients and QP remain
open. Finite colours, positive quotient indexing and
`CyclotomicPolynomialParity` are unchanged.

## Graded polynomial-variable square

`CyclotomicAction/IntertwinerDotGrading.lean` proves `sourceRightDot_parity`
and `targetRightDot_parity`: both existing right-dot operators have degree
`D.parity i` on the constructed induced gradings. The proof uses homogeneous
corner products with `affineLastDot_parity` and `affineFirstDot_parity`, and
preservation of coefficient degree by the sign involution. In particular,
the target still uses the parity of its shifted coefficient.

`sourceRightDotLinear` and `targetRightDotLinear` only restrict scalars of
these operators. `rightDot_Q_square` is the existing `targetRightDot_Q`
on the graded carriers. `rightDot_Q_gradedSquare` combines this equality
with Q-evenness and both dot degrees, giving the polynomial-variable
portion of KKO I Proposition 8.4 on these quotients. The imported consumer
checks all-odd height three and mixed height two, both with shift one,
and audits all owned declarations.

These are graded right operators, not signed left-superlinear morphisms.
No square-zero relation for an odd polynomial variable is asserted. Full
right-superalgebra structure, full Proposition 8.4, full-ELV coefficients,
QP and nonzero inversion models remain separate obligations.

## Constructed right dots and Q compatibility

`CyclotomicAction/IntertwinerTargetDot.lean` constructs `targetRightDot`
on the actual prepend-corner induced module with coefficient `qCoefficient`.
It sends `a ⊗ c` to `a x_first ⊗ sgn(p(i))(c)`. The theorem
`targetDotCoefficient_insert`, derived from `Envelope.ζPow_inv_mem` and
`SVec.sgn_comp_of_mem`, proves that on `c = π^η b`, with `η = p(i)p(β)`,
this is exactly `(-1)^η a x_first ⊗ π^η φ_i(b)`. Both factors are present.

`affineFirstDot_twist_comm` derives balance from homogeneous superinterchange.
`contentMove_firstDot` assembles `dot_comp_moveHom` into the signed matrix
identity, respecting reversal of diagram composition by matrix multiplication.
`targetRightDot_Q` proves the equality of actual linear-map composites
`targetRightDot.comp parityCyclotomicContentQ =
parityCyclotomicContentQ.comp sourceRightDot` by balanced-tensor induction.
Neither balance nor the matrix identity is assumed. The imported consumer
checks the equality on all-odd height-three and mixed height-two contents,
both with nonzero coefficient shift, and audits the owned declarations.

Source comparison: KKO I, arXiv:1206.5933v2, (8.13) and Proposition 8.4,
PDF page 42, give precisely this target `t_i` formula and compatibility.
The theorem retains finite colours, content projection, positive quotient
indexing, and `CyclotomicPolynomialParity`. It does **not** establish the
induced tensor super grading, full right-superalgebra action, or full
Proposition 8.4; no QP relation is claimed.

## Source right-dot operator

`CyclotomicAction/IntertwinerRightDot.lean` constructs `sourceRightDot` on
`Ind (CyclotomicAlgebra a n) (appendAlgebra i (n+1))`. It is an ordinary
left `Hn (n+2)`-linear endomorphism with pure-tensor formula
`a ⊗ b ↦ a x_last ⊗ φ_i(b)`. The coefficient involution is the regular
cyclotomic supermodule's `SVec.sgn`; `rightDotCoefficient_of_mem` gives
its homogeneous sign. `affineLastDot_twist_comm` derives balance from
`affineLastDot_comm`, and `rightDotCoefficient_smul` supplies the matching
coefficient twist. There is no assumed balance or assumed intertwining.
Mixed and all-odd consumers use the existing cyclotomic balanced tensor;
the mixed consumer checks the minus sign on odd coefficients.

The source and target right-dot endomorphisms and their Q compatibility are
now constructed as described above. The induced-tensor grading is now supplied
by `IntertwinerGrading`, including Q-evenness; the dot degrees are supplied by
`IntertwinerDotGrading`. The full superbimodule assertion remains open. Finite colours, positive quotient
indexing, and `CyclotomicPolynomialParity` are retained.

## Canonical parity-shifted coefficient target

`CyclotomicAction/IntertwinerParity.lean` refines the target of the existing
`cyclotomicContentQ`. `qCoefficient` is the existing `Envelope.piPow` of the
regular cyclotomic superbimodule, with exponent `p(i)p(β)`;
`qCoefficientInsert_mem` proves the coefficient parity, and
`qCoefficientInsert_smul` proves the actual semilinear coefficient identity.
`qCoefficientTransfer` moves the involution out of the right corner action,
and `parityCyclotomicContentQ` composes this with the already descended map.
`parityCyclotomicContentQ_tmul` retains the actual moving-strand representative.
No new balance hypothesis, flatness assumption, or duplicate parity-shift
interface was introduced. Mixed and all-odd consumers activate a nonzero
shift, use the actual cyclotomic quotient, and audit all owned declarations.

Source-statement comparison: KKO I, arXiv:1206.5933v2, Proposition 8.4 also
requires the induced super grading and signed right `t_i` compatibility.
The latter is now proved by `targetRightDot_Q`; induced grading is now supplied
by `IntertwinerGrading`, while Q-evenness remains open.
Its target right action contains both
`(-1)^{p(i)p(β)}` on the first-dot action and the coefficient involution
`φ_i(b)`; the latter cannot be dropped when balancing across odd coefficients.
The new coefficient grading requires `CyclotomicPolynomialParity`; the old
ungraded map remains unchanged and more general. The `[Fintype I]` scope,
content projection (zero on the other blocks), and positive-height indexing
`CyclotomicAlgebra a n` over `Hn (n+1)` are unchanged. This is not full
Proposition 8.4, not a graded superbimodule-map theorem, and not QP.

## Rectangular mates and the capped pitchfork

`SKM/RouquierMixedMate.lean` defines `rectangularMate` for independent outer
adjunctions and proves its explicit cup–map–cap formula and both naturality
laws. `rouquierMate_postTranspose` identifies the prescribed rightward mate
with the postcomposition transpose; `rouquierMate_pitchfork_cap` then follows
from the Hom-adjunction inverse. Its triangle is the existing right-adjunction
E-strand triangle, not a left zigzag. `rouquierMate_parity` derives homogeneity
without inversion data, and `rouquierMate_cross_interchange` proves the single
odd–odd exchange with coefficient `koszulSign p p` (minus one at odd parity).

The three-adjunction signed expansion is now `rouquierMate_comp_mate`:
`P = koszulSign p p • M(B ≫ A)`, with the final output associator included
in `M`. Its proof transports the existing odd interchange through the even
outer unit and applies the derived capped pitchfork. No exchange or mixed
identity is assumed. Only pure coherence is checked in the underlying-even
bicategory; the odd crossing exchange remains in the supercategory.
`rouquierMate_mixed_braid` derives `C ≫ P = P ≫ D` from the explicitly typed
upward braid and the two rectangular naturality laws. Its coefficient is one
at both parities: the common expansion coefficient is not cancelled or inverted.
The importing consumer exercises both headlines at parity one, including the
minus sign in the expansion, and audits every owned declaration. It retains
the supercategory and adjunctions as parameters; no nonzero inversion model
is constructed.

`SuperRouquierLoc.sig_capCross` now follows by postcomposing the sign-free
mixed braid with the upper left cap, without exchanging that cap.
`sig_capCross_of_neg` computes its crossing component at `h < 0`, with
`h' = h + 2`: it is zero except at `h = -1`, where its coefficient is
`s = koszulSign p p`. `whiskerRight_hom_ext_of_nonpos` extracts equality
from the total augmented inverse equation, and `capCross_eq_of_neg`
assembles the crossing and all dotted-cup components. Writing
`C = L.capL ▷ E₂ ≫ λ.hom` and
`R = α.hom ≫ E₂ ◁ A₂.counit ≫ ρ.hom`, its formula is
`U.capCross = s • (-C + R)` at `h = -1`, and `U.capCross = -C` at
`h < -1`. In particular, the odd boundary is `C - R`; scaling only `R`
would fail the undotted-cup equation. Inputs are the adjacent local data,
both upward square relations, the upward braid, and the height relation.
The proof uses no assumed left zigzag or target cap relation.

The imported `RouquierCapSwap` consumer specializes the boundary to both
parities, applies the theorem to the local data of a `RouquierFamily`
(deriving the height shift and using its square/braid fields), and audits
101 owned declarations. `capL_pitchfork_at_neg_one` derives the left-cap
pitchfork at `h = -1` from the cap swap and the positive inverse; its
coefficient is `s`, with an importing odd-parity consumer.
`capL_pitchfork_below_neg_one` proves the remaining negative-height case,
with coefficient one, by `whiskerLeft_hom_ext_of_nonpos` at upper height
`h+2` and `curlEG_cupD_zero`. Its importing consumer tests arbitrary parity
at height `-2` and all lower heights for a `RouquierFamily`.
`leftAdj_triangle_E_of_neg` now proves the canonical E-strand zigzag is
`𝟙 E₂` for every `h < 0`, including `h = -1`: at the boundary the common
cap-swap sign cancels, and below it the pitchfork reduces to
`curlEG_cupD_self`. `RouquierFamily.leftZigE_of_neg` gives this directly for
`leftZigE`, with the existing `leftCup` and `leftCap`, without rescaling.
The consumer checks arbitrary parity and negative height and the family API.
These remain parametric consumers, not a nonzero odd inversion model.
The positive augmented inverse now gives `cupCross_eq_of_nonneg`, using
all its crossing and dotted-cap components rather than an unsigned duality.
Writing `R = ρ.inv ≫ E₂ ◁ U.cupL`, the cup-side double crossing equals
`-s • R` at `h = 0` and `-R` at `h > 0`. The component calculation
`cupCross_capD_boundary` retains both the crossing/dot interchange sign
and the positive single-curl coefficient. `cupL_pitchfork_of_nonneg`
then has coefficient `s` at zero and one above zero. It assumes the same
adjacent-height relation, both upward squares, and upward braid as the
cap pitchfork; it does not assume left zigzags.

Consequently `leftAdj_triangle_E_of_nonneg` and
`RouquierFamily.leftZigE_of_nonneg` prove the canonical E zigzag is
`s • 𝟙 E₂` for `h ≥ 0`, **not** an unsigned identity at odd parity.
`RouquierFamily.leftZigE_eq` assembles all heights: coefficient one below
zero and `s` at nonnegative height. No cup or cap was rescaled. Importing
consumers check both parities at zero and arbitrary positive height,
the signed cup pitchfork, and the actual family API.

The canonical F triangle and a common normalization remain open. For
`σ = leftAdjParity D i x` and E coefficient `e` just computed, the remaining
compatible F formula is `leftZigF = (koszulSign σ σ * e) • 𝟙 F`.
`RouquierFamily.leftZigzags_iff_leftZigF` now proves that this exact F
formula is equivalent to `LeftZigzags`. The reverse implication constructs
`c = koszulSign σ σ * e` as a unit with inverse itself. For the forward
implication, `SuperAdjunction.smul_id_right_of_left` transfers equality of
scalar multiples of `𝟙 E` to `𝟙 F` using the existing right-adjunction
triangle. It does not assert scalar faithfulness or infer F from E alone.
The named `FNormalizationChecks` consumers check even parity and odd
heights zero and one, and construct `RouquierLeftAdjoints` **conditional
on the exact F equation** via the existing `leftAdjointsOfZigzags`.
The canonical F equation itself, hence unconditional normalized left
adjunctions, is still unproved in Lean at every height.
[SignedFTriangle.md](SignedFTriangle.md) now gives a written mathematical
proof by explicit right-mate reflection, including the signed vertical
composition law, horizontal opposite, comparison of the prescribed mixed
mate, and every field of the mirrored local inversion data. With
`s=(-1)^p` and `q(n)=s^(n(n-1)/2)`, the mirrored crossing is `s M(t)`;
the dotted components and their inverses are scaled by `q(n)`.
The reflected canonical cup and cap have coefficients `a(h+2),b(h)`
whose product is exactly `s^(h+1)=koszulSign σ σ`. Applying the already
proved local E theorem to these mirrored data therefore gives the
canonical F coefficient `s^(h+1)` for `h<0`, and `s^h` for `h≥0`.
The document is not kernel-checked; formalizing the generic mate calculus
and the mirrored local construction remains necessary. No cyclicity,
left adjunction, or scalar faithfulness is assumed in the argument.
No nonzero odd inversion model or full-root certification is claimed.

## Reservoir closure audit

[FusionReservoirLemma.md](FusionReservoirLemma.md) audits the inversion argument
of `NondegeneracyProof.md`. The proposed graded proof gives the correctly typed
closure `cap_s ∘ principalInverseBlock ∘ cup_r` degree `2d_i(r+s+1)`;
bounded-above reservoir grading support then gives joint nilpotence in every
parity and at every height. This is a written argument, not a new Lean theorem.
The draft's ordinary-centre formulation and radical/degree-zero equivalence
need correction. More importantly, nilpotence of these closures does not prove
fused inversion: the augmented factor inverses leave a residual matrix on
positive-height cap rows and negative-height cup columns. The even
`RouqCoproduct.isIso_lift_of_schur` and `schur_const_eq` explicitly retain and
invert this matrix. The all-height super residual matrix and its dotted-window
comparison remain open; §5.4's two-by-two reduction cannot yet be used as a
proved reduction to Lemma β alone.

## Cyclotomic deformation coefficients

`CyclotomicDeformationProof.md` gives proposed written proofs, not new Lean
claims. Arbitrary homogeneous exterior-coefficient cyclotomic polynomials
need not be flat: over `Λ(d,e,f)`, the one-strand relation
`x²−xd+ef=0` forces `def=0`. KKO's permitted even-coefficient deformations
and their odd-cutoff exterior translates have a general freeness argument
from KKO tower projectivity, graded splitting and compatible translation.
The full ELV family must use its relation `d_iχ_(i,m)=0` at even cutoffs;
its coefficient ring is itself not flat over the exterior subalgebra.
Multicolour freeness over the full ELV ring still needs the balanced
deformed projective resolution. Nilpotent lifting of the specified Rouquier
matrix needs only `Tor₁(A/J,target)=0`, but also exact base-change comparison
of its corners, tensor adjunction, signed generators and cup–crossing–cap
mate, and a proof of invertibility of that reduced matrix (A1-map).

## Deformed cyclotomic transport and repeated-odd cancellation

`DeformedProjectiveResolution.md` gives a proposed written proof, not a Lean
theorem, of full ELV polynomial transport through arbitrary multicolour
intertwiner chains. The coefficient sign and dot sign combine to the uniform
polynomial-parity sign. In the first-dot polynomial balanced module this
proves `f(x)τg=f(x)(x²+y²)` by cancelling the monic square difference, not
by assuming cyclotomic freeness. The even-cutoff normalizer defect before
imposing the ELV coefficient relation is exactly `2χ_m d_i`.
The document specifies the twisted balanced K₀, K₁, K₁′ and the global QP
formula. The all-prefix induction, P balance and tensor-map assembly are
still open; no full projectivity or action theorem is claimed. Once those
steps are supplied, the central-square argument gives projectivity over the
preceding block without an A-flatness assumption on that block.

## All-prefix deformed QP calculation

`DeformedGlobalQP.md` gives a proposed written proof of the all-prefix
identity, using the affine pitchfork to put the killed relation at old
position 2 before cancelling the moving square difference. The two
repeated-odd prefix signs cancel; repeated-even strands contribute no
factor. A separate old-generator P balance argument retains total
coefficient parity and the shift `p(i)(N_i+p(β))`. These arguments are
not Lean theorems and still require independent review. The separate
ideal-sum argument is recorded below. The exact projective resolution and
resulting global projectivity remain conditional; the central-monic lemma
is not applied.

## Deformed cyclotomic ideal sum

[DeformedIdealSum.md](DeformedIdealSum.md) gives a proposed written proof of
KKO I Lemma 8.2 for the full ELV coefficient ring. First-strand parabolic
normality, with total coefficient parity and `x₁ ↦ x₁−2d_i`, replaces
centrality. Choosing affine PBW words adapted to the tail parabolic proves
`H F₁ H = Σ_a H F₁ τ₁⋯τ_a`, hence
`(H F₁ H)e(β,i) = H F₁ ι_R(R) + H F₁ τ₁⋯τ_n e(β,i)`.
Both inclusions and all old factors are retained; no cyclotomic flatness
is assumed. This identifies the kernel of the old-to-new quotient map.
Identification with `im P` is conditional on the separately proposed P
balance/descent. A projective `B[s]` resolution additionally requires the
reviewed QP injectivity argument and specified square-right actions and
projective module structures. The proof awaits independent review; no
full action or new Lean theorem is asserted.

## Moving-strand balance on arbitrary Hom entries

`CyclotomicAction/IntertwinerNaturality.lean` proves `hom_comp_moveHom` for
any morphism `f : H(t,t')`, including inhomogeneous morphisms:
`(1_i ⊗ f) ≫ move(t') = move(t) ≫ (twist_(p(i)p(t))(f) ⊗ 1_i)`.
The proof uses the normal-form spanning theorem, not a homogeneity
assumption on `f`. `cl_mem_chainParity` identifies the positioned-word
parity with its actual parity in the presented category. The hypotheses
are only a Cartan superdatum, its scalar system, and a commutative base ring.

`CyclotomicAction/IntertwinerCorners.lean` now assembles these entries in
`Hn`: `contentMove` is the finite sum over words of content β, and
`contentMove_balance` proves
`append(twist_(p(i)p(β))(z)) * G_β = G_β * prepend(z)` for arbitrary
inhomogeneous `z`. The only additional hypothesis is `[Fintype I]` for
the height-algebra colour sums. `prependAlgebra` and
`homMatrixTwistAlgebra` use the existing finite-support Hom coordinates.

`CyclotomicAction/IntertwinerTensor.lean` constructs `contentQ` on the
existing `InductionAlong.Ind` balanced quotient, with formula
`a ⊗ b ↦ a G_β ⊗ b`; no balance/descent hypothesis is assumed.
`cyclotomicContentQ` takes the actual cyclotomic quotient as coefficient
module. The target right action is `prepend ∘ twist_(p(i)p(β))`.
This is an underlying left-module descent, not yet the full Q of
Proposition 8.4: identification with the explicitly parity-shifted
coefficient superbimodule and signed right `t_i` compatibility remain.
The QP identity of Theorem 8.5 remains downstream. No flatness statement
is used. `scripts/NonVacuity/IntertwinerTensor.lean` checks all-odd and
mixed-parity asymmetric data and audits all declarations in both modules.
The consumer `scripts/NonVacuity/IntertwinerNaturality.lean` exercises
arbitrary Hom entries and identity plus an odd dot on an all-odd
asymmetric two-colour datum, and audits the module's axioms.

## Fixed-content restriction of Q

For KKO I, arXiv:1206.5933v2, Proposition 8.4,
`CyclotomicAction/IntertwinerContent.lean` restricts the previously constructed
Q to the right images of the cyclotomic content idempotent. The construction
cuts to content rather than identifying the whole height quotient with it. The source projection is
`x ⊗ b ↦ x append(e_β) ⊗ b`; the shifted target projection is
`x ⊗ πb ↦ x prepend(e_β) ⊗ πb`. Both equalities are proved by balancing
and multiplication on quotient representatives. The corresponding induction
principles show that these cut representatives generate each summand.

`appendContent_mul_contentMove` removes the redundant append idempotent.
`contentCornerQ_tmul` gives `x e(β,i) ⊗ b ↦ x G_β v ⊗ πb`, using
multiplication by `contentMove` and the canonical coefficient insertion. `contentCornerQ_left`,
`contentCornerQ_rightCoefficient` and `contentCornerQ_rightDot` prove the
three module compatibilities on the restricted carriers.
`targetContentRightDot_tmul` retains the sign `(-1)^(p(i)p(β))`, first dot,
and coefficient involution. No module action is transported along a chosen
equivalence; ordinary right multiplication is left-linear, without an extra
signed-left condition.

This establishes restriction and representative generation inside the
height-balanced quotients. It does not yet give a separately defined tensor
over the unital algebra `R(β)` with a two-sided comparison to these summands.
Finite colours, positive quotient height (`n+1`) and polynomial parity remain.
The zero-height formula, full ELV coefficients and QP are still open.

## Global content indices

`GlobalProduct.lean` constructs the full weight supercategory
`globalWeightSpace`, the product of all `GlobalContentModules β` of the
given weight. The pointwise parity decomposition works for arbitrary
products; it does not require finitely many contents. This constructs the
objects of the weight action, not yet its induction and restriction maps.

`GlobalHeight.lean` adds the empty-word algebra and supermodule category to
the tower without altering a positive-height quotient. `heightAppend` is
the vacuum map at zero and the existing quotient inclusion thereafter;
`heightAppend_parity` proves every such inclusion is even.
`GlobalContentModules β` uses height `β.card`, including zero.

`GlobalSupport.lean` retains both parity components on full content
subcategories, with `fullSupercategory`, `fullLiftTrans`,
`globalBlockInduction` and the odd `globalBlockDot`. The dot's homogeneous
parity is the colour parity, and its naturality is the original signed
naturality. These constructions do not discard odd module morphisms.


`GlobalInduction.lean` extends superinduction to every height of the tower,
including the vacuum: `heightSuperInduction` uses the colour-cut bimodule over
`heightAppend`, and `heightSuperInduction_succ` is definitional agreement with
`cyclotomicSuperInduction` at positive height. `heightContentSupported_induction`
moves content `β ↦ {i} + β` at all heights (at zero via `vacuumAppend_content`).
`globalContentInduction (h : {i} + β = δ)` is the superfunctor between global
content categories, composed with the identity transport `heightContentCast`
along `β.card + 1 = δ.card`.

`GlobalRestriction.lean` restricts `cyclotomicSuperRestriction` to content
blocks (`globalBlockRestriction`) and the even unit and counit to
`globalBlockAdjunction : globalBlockInduction ⊣ globalBlockRestriction`; both
components are even (`globalBlockUnit_mem`, `globalBlockCounit_mem`). This is
the positive-height block adjunction; the vacuum unit and counit are open.

`GlobalWeightRestriction.lean` ports `globalF`: `heightSuperRestriction` is the
colour-cut restriction bimodule along `heightAppend` at every height,
definitionally `cyclotomicSuperRestriction` at positive height
(`heightSuperRestriction_succ`), and restriction from one strand to the empty
word uses `vacuumAppend`. `globalContentRestriction (h : {i} + β = δ)` lands in
the vacuum condition `β = 0` at height zero, and
`globalF i h : globalWeightSpace y ⟶ globalWeightSpace x` is the product of
these superfunctors along `blockSucc`, retaining odd morphisms.

`GlobalWeightInduction.lean` ports `globalE`. Each block has at most one
predecessor (`blockSucc_injective`), so the component at `δ` is
`globalContentInduction` from it (`inductionComponent_blockSucc`) and the zero
supermodule otherwise (`inductionComponent_isZero`, `globalZero_isZero`).
`globalE i h : globalWeightSpace x ⟶ globalWeightSpace y` is the resulting
superfunctor.

`GlobalHeightAdjunction.lean` restates the corner pairing, even unit and
counit and both triangle identities along `heightAppend` (they only use a
unital even multiplicative strand map), so the adjunction now also covers the
empty word to one strand. `heightContentAdjunction` restricts it to content
blocks at every height, and `globalContentAdjunction (h : {i} + β = δ)` gives
`globalContentInduction h ⊣ globalContentRestriction h` (composed with the
mutually adjoint transports `heightContentCastAdjunction`).

`GlobalWeightAdjunction.lean` assembles `globalWeightAdjunction :
globalEFunctor ⊣ (globalF).toFunctor` from the blockwise adjunctions,
transported along `inductionComponent_blockSucc`, with zero counit at blocks
without predecessor; unit and counit are even (`globalWeightUnit_mem`,
`globalWeightCounit_mem`). `globalActionAdjunction` packages it as
`SKM.SuperAdjunction (globalActionE i h) (globalActionF i h)` in the `SCat`
target of `ActionSupercategory`, i.e. the `adj` field of `RouquierFamily` on
weight spaces.

`GlobalHeightDot.lean` defines the last dot of the extended tower
(`heightLastDot`; at one strand the image of `affineLastDot` in the
height-one quotient) and restates the signed corner map of `SuperDot` along
`heightAppend`: `heightSuperInductionDot`, homogeneous of parity `|i|`, its
content restriction and `globalContentDot`. `GlobalWeightDot.lean` transports
it along `inductionComponent_blockSucc` to `globalWeightDot`, with
`globalActionDot_mem : globalActionDot i h ∈ parity (globalActionE i h) _ |i|`,
the `dot`/`dot_mem` fields of `RouquierData` on weight spaces.

`GlobalHeightCrossing.lean` defines the last-pair crossing of the extended
tower (`heightLastCrossing`; on two strands the image of
`affineLastCrossing` in the height-two quotient) and restates the two-colour
corner, functor comparison, signed corner crossing and transported crossing
along `heightAppend`: `heightSuperInductionCrossing`, homogeneous of parity
`|i||j|`, now also from the empty word. `GlobalHeightBlockCross.lean` proves
`heightLastCrossing_square` (at two strands from `affineLastCrossing_square`),
`heightSuperInductionCrossing_square`, and restricts the crossing to content
blocks with explicit target content at every height (`heightBlockCross`,
`heightBlockCross_square`). `GlobalWeightCross.lean` identifies two global
content inductions with `heightBlockInduction₂` followed by a height
transport (`globalContentInduction_comp`), and transports `heightBlockCross`
blockwise to `globalWeightCross`; both composites vanish off two-step
successor blocks (`globalEFunctor_comp_isZero`). `globalActionCross_mem` is
the `cross`/`cross_mem` field of `RouquierData` on weight spaces.
`GlobalRouquierData.lean` proves `globalActionCross_square` and assembles
`globalRouquierData Λ : SKM.RouquierData D` in `cyclotomicActionTarget`
(weight-space induction, dot, and the even file's signed crossing
`globalActionSignedCross`: `-ψ` for equal colours, `ψ` otherwise), with
`globalRouquierData_square`; `globalActionAdjunction` supplies `adj`. Open
toward `RouquierFamily`: the braid field on weight spaces (port of
`GlobalBraid`/`GlobalBraidQ` through `blockSucc₃`, using A's `Braid`), the
slides (`GlobalSlides`), nilpotence (needs an odd cyclotomic analogue of
Brundan–Kleshchev Lemma 2.1, absent), and `GlobalLoc` (local inversion is stream A's pending statement).

`GlobalSlideAlgebra.lean` proves the equal-colour dot slides on the last pair of
strands. Locally `x₁ τ - s τ x₂ = 1` and `τ x₁ - s x₂ τ = 1` (`s = (-1)^{|i|}`,
`inductionStrand_slide_left/right`, from relations (1.8) via `Centre.slide_left_eq`);
whiskered by an old word (`induction_slide_left/right`) and summed, in the algebra
`c y₁ - s y₂ c = θ(1)` and `y₁ c - s c y₂ = θ(1)`, where `c` is the last-pair crossing,
`y₁` the appended and `y₂` the new last dot (`affineLastCrossing_slide_left/right`,
and at every height of the extended tower `heightLastCrossing_slide_left/right`).
`GlobalHeightSlides.lean` lifts these to the two inductions: on the equal-colour corner
`T = C θ(1)` signed right multiplication by `y₂` and by `y₁` are superbimodule
endomorphisms (`heightCompositionRightMul`, hypotheses `CornerMulData`); the comparison
`F ≅ T ⊗ -` sends the outer dot to `y₂` and the inner dot to `y₁`
(`heightComparison_dot_outer_app`, `heightComparison_dot_inner_app`), so
`ψ x₁ - s x₂ ψ = s` and `x₁ ψ - s ψ x₂ = s` on components (`heightInduction_slide_left/right`,
diagrammatic order). For the Rouquier crossing `t = -ψ` these are exactly
`SuperRouquierLoc.slide_left/right`; the transport to weight blocks is still open.
`GlobalBraidAlgebra.lean` gives the algebra half of the equal-colour braid: with
`c₁ = φ(c)` the appended crossing and `c₂` the last-pair crossing on three strands of
colour `i`, `c₁ c₂ c₁ = c₂ c₁ c₂` on each word (`induction_braid_same`, positional
`braid_ne`), in the affine algebra and at every height (`heightLastCrossing_braid_same`).
The functor half (three-fold corner comparison and transport through three successor blocks)
is still open.
Stream H restart point (paused 2026-10-26): (a) slides to weight blocks: lift
`heightInduction_slide_left/right` through `heightBlockInduction₂`/`fullLiftTrans` and the
`globalWeightCrossVia`/`globalWeightDotVia` eqToHom transports, in the shape of
`GlobalRouquierData.globalActionCross_square` (t = `globalActionSignedCross` = -ψ for i = i);
(b) braid functor half: a three-fold corner `C θ₃(1)` with comparison
`Ind ⋙ Ind ⋙ Ind ≅ T₃ ⊗ -` (copy `heightInductionFunctorComparison`), carrying
`heightLastCrossing_braid_same` to components, then blocks; (c) `GlobalNilpotent` needs
an odd algebra-level BK Lemma 2.1 (none exists in odd-lean yet); not started.

`GlobalCross.lean` defines two-step block induction `globalBlockInduction₂`
with explicit target content and restricts the constructed crossing
`cyclotomicSuperInductionCrossing` (`globalBlockCross`, parity `|i||j|`).
`globalBlockSignedCross` is the Rouquier convention of the even file (`-ψ` for
equal colours). `cyclotomicSuperInductionCrossing_square` transports
`compositionSuperCrossing_square` through the comparison isomorphism, giving
`globalBlockCross_square` and `globalBlockSignedCross_square`, the shape of the
`square` field of `RouquierFamily`. Distinct-colour squares, dot slides and
braids are not yet transported to blocks.

`CyclotomicAction/Global.lean` supplies the content indices and boundary sign
for the global cyclotomic action: `WeightBlocks`, injective `blockSucc`, its
subsingleton fibres, `exists_blockSucc_iff`, `blockSucc_comm`,
`blockLoc_weight`, and `pair_nonpos_of_not_mem`. The convention is
`weight(β) = sum β - Λ`. Empty content is retained. `blockWeight_not_card`
shows why positive-height categories alone do not give weight spaces: already
the singleton contents of two distinct simple roots have different weights.
This ports the index layer, not yet the global superfunctors. Concrete content
projectors and induction support are in `ContentBlocks` and `ContentSupport`.


Branch `research/odd-nondegeneracy`. Rules for this branch: `AGENTS.md`, "Workflow and
evidence". This file is updated in the same push as the results it describes. Status
words: *Lean* means compiled on this branch and covered by full CI; *proposed* means a
written argument in `docs/Nondegeneracy/` that is not checked; *open* means neither.

Target: [BE2] §8 Nondegeneracy Conjecture (`SKM.NondegeneracyConjecture`), i.e.
injectivity of `MatchingBasisChoice.expansion` over the abstract `SYM` (polynomial even
generators, exterior odd generators), for odd and mixed data. No unconditional full nondegeneracy
theorem is claimed. B0 is complete: `nondegeneracy_of_upward_independence` derives
the conjecture from upward independence at every weight; the latter remains open.

Scope: compatible symmetrizable Cartan superdata with finitely many colours and homogeneous
scalars, over a field, followed by integral descent as in the even case. Nonsymmetrizable data
and nonhomogeneous scalars are outside the target.

Route: the super analogue of Webster's proof of the even case (formalized in
categorification-lean): deformed cyclotomic super actions with ELV odd parameters at highest and
lowest weight, the family `Hom(T(-μ₊), W(μ₋))` reaching every weight `μ₋ - μ₊`, detection of the
upward part and of bubble products there, and the reduction of the conjecture to upward
independence. Proposed theorem graph: [GeneralRoute.md](GeneralRoute.md). The product-datum Hom family
must still be fused to the original superdatum. The exact test in
`scripts/Nondegeneracy/nilpotent_hom_fusion.py` refutes zero/zero fusion with
inherited blockwise dots: the necessary odd crossing equation has coefficient
rank 32 and augmented rank 33. The separated zero/nonzero alternative remains
proposed and retains all odd coefficients in one connected reservoir, not in
the invertible probe; its all-content categorical inversion is still open.

`separated_fusion_relations.py` checks zero/nonzero cross-polynomial units in
all colour-parity combinations, including a nonsemisimple probe. Its adjacent
odd affine A1 test includes one reservoir i strand, one probe i strand and one
reservoir j strand: all six labelled shuffles satisfy the two-strand relations
and the two nonzero repeated-colour braid corrections. Both independent
reservoir exterior generators survive. This is an affine corner test, not an
induction/restriction construction or an all-content inversion theorem.
[SeparatedFusion](SeparatedFusion.md) gives the proposed local denominator
argument, the conditional all-height Schur argument and an explicit Lean plan.
The categorical multicolour Hom-sector comparisons and their actual mate
coordinates remain open; no all-content A2 theorem is claimed.
`commute_inverse_square_difference` and `separated_diagonal_crossing` prove
in Lean that `(x-y)/(x²-y²)` has both odd dot slides and square
`(x²+y²)/(x²-y²)²`. The smallest actual nonvacuum rank-one mate was rechecked:
its 72-by-72 matrix has determinant one, with square-zero feedback of rank four.
`klr_cyclotomic.py` builds verified two-colour KKO cyclotomic quotients from
the presentation. `rouq_sig_multicolour_check.py` runs the separated mate checks
on them; partial results are in SeparatedFusion §7. Mutation controls are not
done, so these results are not evidence about crossing data.
[NondegeneracyProof](NondegeneracyProof.md) records the proposed proof with a
status for each step. The claimed reduction of fused inversion to reservoir
closure nilpotence alone has been withdrawn: the all-height residual
identity-summand matrix and its dotted-window comparison remain open.

## Super Rouquier interface

The named projection obligation is
`OddMath.SKM.SuperRouquierLoc.MateProjectionFormula`, in
`OddMath/SKM/RouquierMateProjection.lean`. It equates the two sector projections
of the normalized cup–crossing–cap mate `-q • rouquierMate` with
`C = Σ_r q^r u_{A,r} v_{B,-r-1}` and
`D = -Σ_r q^(r+1) u_{B,-r-1} v_{A,r}`. It is a **Prop definition, not a theorem**.
The inclusions, projections, dotted factor maps and finite nilpotence bounds
are explicit arguments; their content-shifted Hom realization is still open.
The odd specialization uses the raw mate, whereas the even specialization
uses its negative, matching the normalized slide in SeparatedFactorInversion.
`NonVacuity/MateProjectionFormula.lean` checks both parity specializations.
This interface assumes neither an inversion nor a proof of A2.

`OddMath/SKM/RouquierHomContent.lean` defines `contentParity`,
`homContentShift`, the original-weight category `homWeightSector`, and the
content-shifted `homContentPostE`/`homContentPostF` with
`homContentPostAdjunction`. The shift is `p(i) P(β₊)`; its change across a
reservoir `j` edge is `p(i)p(j)` (`homContentShift_add_single`). The Π-action
is the full superfunctor action, and its self-adjunction is derived from the
even Π² comparison. `scripts/NonVacuity/HomContentShift.lean` consumes this
adjunction in the integral parity envelope and checks the nontrivial sign on
its odd comparison map. Finite content is retained separately from weight.
The raising precomposition functor `homContentPreE` has the correct negative
factor weight indices. Its right adjoint comes from the factor's left
adjunction, not from the given right adjunction (see below).

`OddMath/SKM/RouquierShiftedAdjunction.lean` defines
`ShiftedSuperAdjunction F E σ`: a left adjunction `F ⊣ E` whose cup and cap have
parity `σ`. The zigzag on `F` is the identity and the zigzag on `E` is `(-1)^σ`
(the sign of BE Proposition 6.2, (6.6)). `homPreShiftAdjunction` proves
`homPre E ⋙ S ⊣ homPre F` on the full Hom supercategories for any parity-`σ`
shift `S` with a supernatural comparison (`ParityShiftDatum`). The odd sign of
the `E`-zigzag cancels exactly against the super interchange of the cap with
the odd comparison `ζ`. `homContentPreAdjunction` then gives
`homContentPreE ⊣ homContentPreF`, where the lowering precomposition is
shifted by `leftAdjParity D i = p(i)(h_i+1)`, constant along the edge
(`leftAdjParity_edge`). Its input is `RouquierLeftAdjoints T`, the factor's
shifted left adjunctions. `OddMath/SKM/RouquierLeftCupCap.lean` defines the
leftward crossing, cups and caps from the local inverses (`sigL`, `cupN`,
`capN`, `cupL`, `capL`, as in `RouqSl2`), proves they have parity
`p(i)(h_i+1)`, and packages `RouquierFamily.leftCup`/`leftCap`. The super
analogue of Brundan Theorem 4.3 is the named Prop
`RouquierFamily.LeftZigzags`: both zigzags of the leftward cup/cap equal `c`
and `(-1)^σ c` for a unit `c`. It is stated up to `c`, so it does not depend
on a sign normalization; super interchange of the cup with itself forces the
ratio `(-1)^σ` whenever the cup is nonzero. `leftAdjointsOfZigzags` turns it
into `RouquierLeftAdjoints`. `RouquierInverseRelations.lean` ports Brundan
Lemma 3.1 ((3.3), (3.5)–(3.9)): the sign-free inverse-matrix relations among
`sig`, `sigL`, dotted cups/caps, and the bubble values `ccw_self`, `cw_self`.
`RouquierDotSlide.lean` proves the signed iterated dot slide
`powComp_sig`: `X^m σ = s^m σ Y^m - ∑_{j<m} s^(m-j) capD_j cupD_(m-1-j)` with
`s = (-1)^p`, Brundan (3.14) (`cupL_powComp_sig`) and both expansions (3.18).
It also proves the infinite Grassmannian relation for `h ≥ 0` with signs
(`infGrass_nonneg`):
`∑_{j<m} s^(m-j) P_j Q_(m-1-j) + s^m P_(-1) Q_m + ∑_{n≤h} P_(m+n) Q_(-n-1) = 0`.
`infGrass_nonpos` is the `h ≤ 0` case, proved directly without a dual:
`∑_{j<m} s^(m-j) P_j Q_(m-1-j) + P_m Q_(-1) + s^m ∑_{n≤-h} P_(-n-1) Q_(m+n) = 0`.
At every weight the term `P_r Q_(m-1-r)` therefore carries `s^(m-r')`, with
`r'` the clamp of `r` to `[0,m]`. This is a candidate sign normalization for
the super fake bubbles. `RouquierCurl.lean` ports the curl calculus:
`curlG`/`curlEG` (closing the left/right strand of a two-strand map), with
atoms on the closed strand absorbed into the cup or cap without sign and atoms
on the open strand leaving with the Koszul sign of the cup or cap they pass.
It proves the pitchforks `sig_counit_pitchfork`, `unit_sig_pitchfork` (no
sign), Brundan Lemma 4.1 (`curlG_dotted`, `curlEG_dotted`) and the boundary
self-curls: `curlG cupL (capD h) t = -ε` with `ε = 1` at `h = 0` and
`ε = s` for `h > 0` (`curlG_capD_self`), and `curlEG (cupD (-h)) capL t = 1`
for `h ≤ 0` (`curlEG_cupD_self`). The `h ≤ 0` statements are proved directly,
without a dual. `RouquierPitchfork.lean` adds two direct inputs for the
leftward pitchfork calculation: `curlEG_cupD_zero` proves vanishing with
`n < -h` dots on the cup, and `curlEG_double_dotted` proves, for `0 < n ≤ 1-h`
and `t ≫ t = 0`, that the closed double crossing `t ≫ x₁^n ▷ E₂ ≫ t` is zero
below the boundary and `-s^n • 𝟙 E₁` at the boundary. Its ordered expansion is
`powComp_right_tau`; no mirror is used. The same module now defines `capCross`
and proves `unit_capCross_zero`, `dottedUnit_capCross`, and
`dottedUnit_capCross_boundary`. Moving `n` dots past the rightward crossing
contributes `s^n`; multiplied by the double-curl boundary `-s^n`, this gives
`-𝟙` in both parities. Thus the dotted-cup component of the cap-swap is
proved, including undotted vanishing. The low capped-crossing expansion is now
proved by `sig_capL_low`: for `h ≤ 1`, it is `capD 0 ≫ cw (-1)` plus `capD 1`
exactly at `h = 1`, in either parity. `sig_capD_closed` and
`cross_sig_capD_closed` retain the factor `koszulSign p (n*p)` from moving the
open-strand dot power past the rightward crossing. For a square-zero upward
crossing, `cross_sig_capD_zero` vanishes and `cross_sig_capD_one` is `s` times
the undotted right-cap pitchfork, where `s = (-1)^p`. The upward sandwich
`tau_dot_tau_left` itself has coefficient one; the factor `s` comes from
interchange. The mixed braid and full negative-height cap swap are now proved
as recorded above, together with both negative-height cap-pitchfork cases and
the canonical negative-height E triangle. Brundan Lemma 4.2, (4.5)–(4.7),
supplies the decomposition followed. BE Proposition 7.2's full pitchforks use
(6.6), so they cannot be imported as independent inputs to the missing
adjunction triangles.
The odd- and even-parity specializations in `NonVacuity/Pitchfork.lean` assume
local Rouquier data: they are signature and axiom checks, not a constructed
nonzero categorical example. No existing concrete instantiation of the local
inversion data has been supplied here; the cyclotomic global local-inversion
comparison remains open. The canonical E-zigzag scalar is now determined
at every height, as recorded above. **Open:** proving `LeftZigzags` by
establishing the F-zigzag through a mirror into a super horizontal opposite
`HOpS B`. That opposite is a 2-supercategory with the same Koszul signs. A
first analysis found that right mates are anti-multiplicative *with* a sign:
`mate (x ≫ y) = koszulSign |x| |y| • (mate y ≫ mate x)`. Consequently
`mate (x^n) = s^(n choose 2) • (mate x)^n`, and the mirror crossing must be
`s •` (full mate of `t`). The mirror's rightward crossing is then
`s • sig`, its dotted caps and cups are `s^(n choose 2) •` L's, and its
`sigL`, `cupL`, `capL` agree with L's only up to explicit signs, not by `rfl`.
Signed anticomposition, powers, and the dotted-cap comparison are now checked
in `RouquierRightTranspose`. The remaining reflected-data comparisons have
not been checked in Lean; their precise coefficients are in `SignedFTriangle.md`. The
nilHecke square and braid transfer to the mirror. Suggested construction: the
mirror crossing is `(homMateEquiv A₁.hop A₂.hop _ _).symm (s • sig)`, and
mate injectivity comes from `recover (φ ▷ E ≫ counit) = φ`. The next even inputs
are the fake-bubble identities, the inverse-cup
expansions (3.12)–(3.13) (`RouqCurl`), the dotted curls (`RouqDottedCurls`),
pitchforks and `RouqTriangleE`. The dual statements need a super horizontal
opposite with Koszul signs (`RouqLoc.dual`, `RouqLoc.mirror`), which does not
exist yet. The even proof is
`RouqLoc.leftAdjunction` via `RouqPitchfork`, `RouqTriangleE`,
`RouqAdjunction`, `RouqCurl`, `RouqDottedCurls`, `RouqGrass` and
`FakeBubbles` in categorification-lean, about 2500 lines. The
original-datum rational crossings must also be constructed before these
sectors can be assembled into A2. `scripts/NonVacuity/ShiftedAdjunction.lean`
checks the odd comparison on the integral parity envelope and the odd
leftward parity. For the Hom adjunction it is only a signature check.

`OddMath/SKM/RouquierHomContentCoherence.lean` supplies `homParityShiftAdd`,
`homParityShiftCommute` and its compatibility with homogeneous supernatural
transformations. `homContentPostOutAdjunction` puts both postcomposition
adjoints in the output-shift convention via the even β comparison.
`homParityShiftCommute_pi` retains the negative Π self-interchange; the
integral parity-envelope fixture proves that this comparison is not the
identity (`scripts/NonVacuity/HomContentCoherence.lean`). These parity-shift
comparisons are not the missing original-datum multicolour KLR relations.

`OddMath/SKM/RouquierMateSlide.lean` proves
`rouquierMate_normalized_slide`: multiplying the raw cup–crossing–cap mate
by `-q` gives the normalized dot slide, directly from the upward relation.
`mate_slide_projection` then projects this ordered relation along specified
dot-intertwining sector maps. Neither theorem assumes an inverse.
`scripts/NonVacuity/MateSlide.lean` checks the projection on a noncommutative
integral matrix fixture. The construction of the required sector intertwining
maps, not the scalar normalization, remains open.

`OddMath/SKM/RouquierMateSeries.lean` proves the signed ordered finite
expansions `mate_series_probe_source` and `mate_series_probe_target`.
They invert only the probe dot; nilpotence of the reservoir dot kills the
tail. The first expansion has coefficients `q^r`, and the second has
coefficients `-q^(r+1)`, without any exchange of factors. The four integral
matrix fixtures in `scripts/NonVacuity/MateSeries.lean` check both expansions
for both signs with a nonzero square-zero reservoir dot and a coefficient
not commuting with that dot. These are algebraic series tests, not a proof
that the categorical sector coordinates have been constructed.

`OddMath/SKM/RouquierMateCoordinates.lean` proves
`SuperRouquierLoc.MateProjectionFormula.of_coordinates`. It starts from the
upward slide and the cup–crossing–cap composite, uses the two projected
slides, and derives the named projection predicate from explicitly listed
sector dot intertwiners, cap–cup factorizations, ordered power coordinates,
probe-dot inverses and reservoir nilpotence bounds. In particular it does
not assume the projection predicate or any inverse of the coupled mate.
The signature/axiom check is `scripts/NonVacuity/MateCoordinates.lean`;
this check is not a nonvacuum categorical example. The categorical content
of the listed coordinate hypotheses remains open, so this conditional
reduction does not close A2 or supply its all-height negative windows.

`OddMath/SKM/RouquierMateSectors.lean` proves
`SuperRouquierLoc.MateProjectionFormula.of_sectors`. Source sectors
(`SourceSector`: summands `E₁ₛ, F₁ₛ` with even inclusions, a sector
adjunction to which the coupled counit restricts, and a sector dot) and
target sectors (`TargetSector`: projections, unit and dot) realize all
intertwiners, cap–cup factorizations and ordered power coordinates of
`of_coordinates`. The coordinates are the actual dotted sector cups and caps,
with negative indices given by powers of the inverse probe dot (`probeCup`,
`probeCap`). The remaining hypotheses are exactly: the upward slide of the
coupled crossing, inverses of the two probe dots, and nilpotence of the two
reservoir dots. No biproduct completeness of the sectors and no inverse of the
coupled mate are used. Still open: constructing the coupled raising functor of
the Hom family with its post/pre sectors and coupled crossing (needs
`RouquierLeftAdjoints` and the original-datum rational crossing), and proving
its slide. `scripts/NonVacuity/MateSectors.lean` is a signature/axiom check with
self-sector evaluations.

`OddMath/SKM/RouquierFeedbackIdeal.lean` proves whole-matrix nilpotence from
a vanishing multiplicative filtration of two-sided coefficient ideals.
`FeedbackIdealFiltration.matrix_pow_mem` controls all entries of every
power, and `isUnit_of_feedback_filtration` feeds the resulting nilpotence
into `isUnit_of_nilpotent_feedback`. Its concrete integral residue-ring
fixture has nonzero square-zero feedback and noncommuting off-diagonal
blocks (`scripts/NonVacuity/FeedbackIdeal.lean`). Construction of the
categorical closed-coefficient filtration and feedback membership is still
open. [HomSectorCoordinates](HomSectorCoordinates.md) specifies the exact
remaining adjunction, original-datum coherence and coordinate obligations.

`OddMath/SKM/RouquierDotConjugation.lean` proves
`mate_dot_conjugation_source` and `mate_dot_conjugation_target` at arbitrary
length, retaining the finite ordered cap–cup correction terms of
SeparatedFactorInversion (3)–(4). No nilpotence is needed for these identities.
`scripts/NonVacuity/DotConjugation.lean` consumes them at all lengths on
noncommuting integral shear dots, with nonzero corrections for both signs.
Their identification with the categorical negative windows remains open;
these are not assertions that the uncorrected windows are invertible.

`OddMath/SKM/RouquierData.lean` defines `RouquierData`, `RouquierFamily`,
`SuperAdjunction`, `SuperRouquierLoc`, and the homogeneous matrix interfaces
`SuperSumInvTo`/`SuperSumInvFrom`. The ambient `TwoSupercategory` retains
super-interchange; it is not an ordinary bicategory. The common inverse
component has parity `|i|`, and dotted identity component `n` has parity
`n |i|`; these are the explicit parity shifts of the formal direct sums.
`rouquierMate` is the ordered cup–crossing–cap composite. `boundaryPos_eq`
and `boundaryNeg_eq` consume its inverse to obtain the normalized Kronecker
window. These declarations pass the scoped warning-free build; full CI
remains the branch-wide verification gate.

`OddMath/SKM/RouquierHom.lean` constructs the linear parity-preserving
`homPre`/`homPost` functors on full Hom supercategories, their homogeneous
`SuperNatTrans` transformations, and `homSectorInterchange`. Its
`homSector_exchange` theorem retains the Koszul sign for opposite-sector
transformations; two odd transformations anticommute. This is the Hom-sector
generator layer, not multicolour affine coherence or categorical fusion.

`OddMath/SKM/RouquierHomAdjunction.lean` proves `homPostAdjunction` and
`homPreAdjunction`, including both triangles and evenness of all unit/counit
components. Precomposition reverses the two adjoints. The proof uses the even
underlying bicategory only for triangle coherence; the functors and naturality
remain on the full Hom supercategories. Content-dependent parity-shifted
comparisons and the coupled affine action remain to be constructed.

`OddMath/SKM/RouquierBoundary.lean` adds the actual finite dotted-unit
`RouquierBoundary.Coefficients`. `Coefficients.ofVacuumInverse` extracts it
from negative local inversion when the common summand vanishes.
`Coefficients.cap_mem`, `cup_cap`, and `hom_ext` prove the cap parity,
normalized top-coefficient pairing, and boundary detection. The cutoff-two
odd example has an odd cap; no unshifted opposite adjunction is inferred.

`OddMath/SKM/RouquierMate.lean` identifies the ordered `rouquierMate` with
`homMateEquiv`, proves both strand naturality laws, and derives
`rouquierMate_slide` from the upward dot slide without any inversion
hypothesis. Its interface consumer is `SuperRouquierLoc.mate_slide`:
`σ ≫ (x₂ ▷ F₂) - q • ((F₁ ◁ x₁) ≫ σ) = ε₁ ≫ η₂`.
The proof retains odd crossings; only the even prefix and suffix use ordinary
coherence. This is the unprojected categorical recurrence. Identifying its
sector projections with both ordered finite formulas is still missing.

`OddMath/SKM/RouquierSchur.lean` supplies associative block factorization,
`isUnit_of_schur`, and `isUnit_of_nilpotent_feedback`. Nilpotence concerns
the whole feedback operator. This removes the need for a commutative
coefficient determinant in the algebraic lifting step, but does not identify
the actual fused mate or its feedback. A2 remains open at the super analogue
of `RouqCoproduct.rouqSig_eq`, followed by the all-content negative-window and
nilpotent-ideal comparison; see SeparatedFusion §7. No separated-fusion
counterexample is asserted, and no fused inversion is assumed to prove A2.

This is the factor-action interface, including same-colour square, braid,
and local inversion. Multicolour affine relations and distinct-colour mixed
inversion are separate obligations. In particular no construction of a
fused action or theorem A2 is asserted. Detection still requires the bubble
normalization outside the finite inverse window and its comparison with the
connected reservoir coefficients.

## One-strand cyclotomic algebra coordinates

`QuiverHecke/CyclotomicAbsentColour.lean` proves `singlePolynomialEquiv` for
the existing quiver Hecke one-strand endomorphism algebra, including odd
colours. `singleCyclotomicEquiv` identifies its polynomial-ideal quotient
with `AdjoinRoot`; `singleCyclotomicFinEquiv_apply` gives the monic finite
coordinate map as the sum of scalar multiples of descended dot powers.
These are underlying-algebra results over any commutative ring. A super
quotient requires homogeneous polynomials. The superfunctors and adjunction
are constructed below; KKO local inversion remains open.
[ActionLeanPlan.md](ActionLeanPlan.md) places exterior ELV coefficients after
the even-parameter action theorem, and targets the existing
`SKM.SuperRouquierLoc` rather than a second local-data interface.

`QuiverHecke/CyclotomicAction/Quotient.lean` equips the existing finite-support
Hom algebra with a unit for finitely many colours, defines its genuine
two-sided first-dot polynomial ideal, and constructs `CyclotomicAlgebra` and
`cyclotomicMk` at every positive strand number. `cyclotomicMk_generator`
proves that the defining cyclotomic polynomials vanish. This supplies the
underlying quotient algebra; its homogeneous grading is supplied below.
The projectivity and Mackey statements needed for inversion remain open.

`CyclotomicAction/Induction.lean` constructs `appendAlgebra` by actual right
whiskering of affine Hom entries, proves `appendAlgebra_mem_ideal`, and
obtains the descended nonunital algebra map `cyclotomicAppend`. The associated
`cyclotomicInduction` is a genuine induction functor on underlying modules.
These inclusions run from height `n+1` to height `n+2`; the vacuum map remains
separate. The supermodule enhancement is given below. No ordinary
naturality claim is made for odd dots.
`CyclotomicAction/Restriction.lean` adds `cyclotomicRestriction` as truncation
by the unit-image idempotent and proves the underlying module adjunction
`cyclotomicIndResAdjunction`, without a flatness hypothesis. Its unit and
counit are those of the actual descended nonunital map, not assumed maps.
This underlying construction is distinct from the super adjunction below
and does not prove KKO inversion.
`CyclotomicAction/Slides.lean` proves the actual affine signed naturality
`induction_dot_slide`; `induction_dot_slide_odd` specializes it to the minus
sign for an odd new dot and an odd lower morphism. This supplies the corrected
homogeneous intertwiner equation rather than the false unsigned equation.
`CyclotomicAction/Parity.lean` equips affine `Hn` with its parity grading
independently of any integer symmetrizer. The coefficient-support condition
`CyclotomicPolynomialParity` proves homogeneity of the actual first-dot
polynomial generators and, in `cyclotomicIdeal_homogeneous_of_polynomials`,
of the entire two-sided ideal. Right multipliers are decomposed into
homogeneous parts; they are not silently assumed homogeneous.
`CyclotomicAction/SuperQuotient.lean` now descends that parity to the actual
`CyclotomicAlgebra`, with `cyclotomicParity_graded`, homogeneous affine lifts,
and `cyclotomicAppend_parity`. `CyclotomicSupermodules` is the existing
superbimodule category with trivial right scalar algebra. These constructions
do not replace the quotient by a polynomial model or forget its odd part.
`CyclotomicAction/SuperInduction.lean` constructs the actual colour-cut
superbimodule `inductionCorner = B φ(1)` and its balanced-tensor
`cyclotomicSuperInduction`. This is an additive, `k`-linear superfunctor,
including on odd morphisms, using the signed tensor whiskering.
`CyclotomicAction/InductionComposition.lean` constructs `compositionCorner`
with right action through the composite inclusion and proves the even
superbimodule isomorphism `inductionCompositionIso : C eᵢ ⊗_B B eⱼ ≅ C φᵢ(eⱼ)`.
Its forward map is `x ⊗ y ↦ x φᵢ(y)` and its inverse is `z ↦ z ⊗ eⱼ`;
both algebra actions and both parity compatibilities are proved. The scoped
warning-free build and declaration axiom audit pass. This supplies coordinates
for composing two positive-height inductions, not crossing, braid or KKO
inversion relations.
`CyclotomicAction/LastCrossing.lean` constructs the finite matrix sum
`cyclotomicLastCrossing` from the literal last-pair crossing `[i,j] → [j,i]`.
It proves parity `|i||j|`, both colour-cut identities and signed intertwining
`θᵢⱼ(r) τ = (-1)^{|r||i||j|} τ θⱼᵢ(r)` for the two composite inclusions.
Rows are targets, so right multiplication goes from `C θᵢⱼ(1)` to
`C θⱼᵢ(1)`. The scoped warning-free build and declaration axiom audit pass.
`CyclotomicAction/SuperCrossing.lean` now constructs the homogeneous map
`compositionSuperCrossing : compositionCorner i j ⟶ compositionCorner j i`,
with parity `|i||j|` and formula `x ↦ (-1)^{|i||j||x|} x τ` on homogeneous
inputs. Signed left linearity and ordinary right linearity follow from the
proved global intertwiner, not an assumed relation. Its scoped warning-free
build and declaration axiom audit pass. Square, braid and inversion relations
remain separate obligations.
`CyclotomicAction/InductionFunctorComparison.lean` constructs the even natural
isomorphism `inductionFunctorComparison` from successive cyclotomic induction
to tensoring by `compositionCorner`. Its pure-tensor formula is
`x ⊗ (y ⊗ m) ↦ (x φᵢ(y)) ⊗ m`; the inverse uses the existing balanced-tensor
associator and the proved corner isomorphism, with no inverse hypothesis.
`CyclotomicAction/CrossingTransformation.lean` transports
`compositionSuperCrossing` along these comparisons to
`cyclotomicSuperInductionCrossing`, a supernatural transformation between the
two orders of composed induction, homogeneous of parity `|i||j|`.
Signed naturality holds on the full supermodule categories. Both modules pass
the scoped warning-free build and owned-declaration axiom audit. Square,
braid and inversion relations, and the KKO decomposition, remain open.
`CyclotomicAction/SuperRestriction.lean` similarly represents restriction by
`restrictionCorner = φ(1) B`; `cyclotomicSuperRestriction` is additive,
`k`-linear, and parity preserving. The positive-height indexing still leaves
the vacuum step separate; the KKO decomposition is not proved.
`CyclotomicAction/CornerPairing.lean` gives even superbimodule maps
`cornerEvaluation : B e ⊗_A e B → B` and
`cornerCoevaluation : A → e B ⊗_B B e`, together with the two elementary
idempotent triangular identities. These use actual multiplication in the
cyclotomic quotient.
`CyclotomicAction/SuperAdjunctionUnit.lean` constructs the even natural
transformation `cyclotomicSuperUnit`, from the identity to induction followed
by restriction, i.e. each module maps into `e B ⊗_B (B e ⊗_A M)`. Naturality is proved
for odd as well as even module maps; both inserted idempotents have parity
zero.
`CyclotomicAction/SuperAdjunctionCounit.lean` constructs
`cyclotomicSuperCounit` by `(x ⊗ (y ⊗ m)) ↦ (xy)m`. Its naturality proof
accounts for both tensor-whiskering signs and the signed left-linearity of
an odd supermodule map.
`CyclotomicAction/SuperAdjunction.lean` proves both triangular identities and
bundles `cyclotomicSuperIndResAdjunction`. Both directions of its Hom
bijection preserve parity. This is an actual super induction-restriction
adjunction, not only the underlying ordinary adjunction. Remaining action
obligations are the vacuum inclusion, the square, braid and mixed
comparisons for the constructed dot and crossing transformations, and the
projective Mackey/local-inversion theorem with the prescribed parity shifts.

`CyclotomicAction/LastDot.lean` constructs `cyclotomicLastDot` as the image
of the finite diagonal sum of rightmost dots on words ending in the induction
colour. `cyclotomicLastDot_parity` proves parity `D.parity i`, and
`cyclotomicLastDot_corner` proves both unit-image corner identities without
a polynomial-parity hypothesis. `cyclotomicLastDot_comm` proves
`φ(r)c = (-1)^(p |i|) c φ(r)` for every parity-`p` quotient element, using
homogeneous affine lifts. The indexing is height `n+1` to height `n+2`.
`CyclotomicAction/SuperDot.lean` constructs `inductionSuperDot` on this
corner: on homogeneous `x` it is `(-1)^(|x| |i|) x c`, as proved by
`inductionSuperDot_apply`. The concrete last-dot relation gives ordinary
right linearity; the parity sign gives signed left linearity.
`inductionSuperDot_parity` proves degree `|i|`, and balanced-tensor signed
interchange gives `cyclotomicSuperInductionDot`, a `SuperNatTrans` on
`cyclotomicSuperInduction`, homogeneous of degree `|i|`. These declarations
pass the scoped warning-free build. Square, braid, crossing and KKO
comparisons remain open; unsigned right multiplication is not substituted
for the signed-left superbimodule convention.

`CyclotomicAction/ActionSupercategory.lean` packages these supermodule
categories as `cyclotomicActionObject` in the existing `SCat` 2-supercategory,
with bundled target `cyclotomicActionTarget : TwoSCat k`.
`cyclotomicActionInduction` and `cyclotomicActionRestriction` are its
1-morphisms; `cyclotomicActionAdjunction` inhabits the existing
`SKM.SuperAdjunction` and proves both triangles with even unit and counit.
`cyclotomicActionDot_mem` gives the colour parity of its dot 2-endomorphism.
No local inversion or new action interface is assumed. The concrete
positive-height adjunction, dots and crossings above form the action data,
not yet a representation satisfying all defining relations. Vacuum extension
and the parity-shifted Mackey decomposition remain open.

`CyclotomicAction/ContentBlocks.lean` defines `contentIdempotent` as the finite
sum of word identities with a prescribed multiset of colours. Its centrality
uses `hom_eq_zero_of_content_ne`, proved by induction on the presented Hom
space, not a hypothesis about content preservation. The quotient elements
`cyclotomicContentIdempotent` satisfy `_sq`, `_central`, and `_orthogonal`
in `CyclotomicAlgebra`. `wordContent_append` records the colour added by
rightmost strand insertion. These pass a scoped warning-free build and
owned-declaration axiom audit; full CI remains the branch-wide gate.
`contentIdempotent_appendAlgebra` and `cyclotomicContentIdempotent_append`
prove the projector identity for the actual strand-inclusion maps.
`ContentSupport.lean` defines `ContentSupported`, its full subcategory
`CyclotomicContentModules`, and `cyclotomicContentInduction`.
`inductionCorner_content` identifies the left target projector with the right
source projector on the actual corner; `contentSupported_induction` then
uses the balanced tensor relation to prove the content shift `β ↦ {i} + β`.
The full subcategory retains all module morphisms; separate supercategory
instances on this wrapper and the height-zero vacuum extension remain open.

## Proof architecture

| Step | Statement | Status |
| --- | --- | --- |
| Assembly | sorted-boundary independence + source exchange descent + target exchange descent imply the conjecture | Lean: `SKM.nondegeneracy_of_contextual_descent` |
| Sorted boundaries | full upward independence implies independence of every sorted family `(ups u ++ dns r, dns l ++ ups v)`, at every external weight, over full `SYM` | Lean: `WeakMate.sorted_independence` (no action, field, finite-colour or faithfulness hypothesis) |
| Choice independence | expansion injectivity does not depend on the permitted choice of representatives, points and serializers | Lean: `expansion_injective_choice_iff` |
| Target exchange, distinct colours | `TargetExchangeDescent` for `i ≠ j` | Lean: `SKM.distinct_target_exchange_descent` |
| Source exchange, distinct colours | complete adapted families and native coefficient twist | Checked: `distinct_source_exchange_descent` |
| Target exchange, same colour | requires the residual deletion `L ++ Q` | Checked: `same_colour_target_exchange_descent` |
| Source exchange, same colour | requires the residual deletion `L ++ Q` | Checked: `same_colour_source_exchange_descent` |
| B0 headline | upward independence at every weight implies the full conjecture | Checked: `nondegeneracy_of_upward_independence`; also `nondegeneracy_iff_upward_independence` |
| Upward independence | finite observations at fixed weight imply `UpwardIndependence` | Lean: `upward_independence_of_finite_observations` |
| Cyclotomic separation | cofinal colourwise cutoffs jointly detect the full coefficient-extended Hom with fixed spectators; a degree-bound criterion for moving spectators | `cofinal_elv_quotients_with_spectators_detect`, `spectator_images_detect_of_bounds`; moving-family hypotheses remain open |
| Observations | extracted regular-projective evaluation on words including spectators; joint algebraic detection remains an input | `SpectatorEvaluation`, `upwardCoefficientMap_injective_of_spectators`; [SpectatorDetection.md](SpectatorDetection.md) |
| Multicolour deformed action | KKO-type cyclotomic action with ELV odd parameters, even cutoffs at odd colours | proposed: [MulticolourActionTheorem.md](MulticolourActionTheorem.md) |

## Reduction route comparison

[ReductionRoute.md](ReductionRoute.md) compares contextual descent with a graded-dimension
reduction. Contextual descent is now complete, including actual complete source
and target choices and all coefficient columns. `hom_laurentian` already supplies the
finite-dimensionality needed by the alternative field route; the missing super rank recursion
and comparison basis prevent treating the even Orzech argument as an immediate reduction.

`exists_cup_completed_choice` constructs a complete choice from unpaired representatives
and literal cups on a complete residual family, with a sum-label equivalence and exact
layer equations. `exists_choice_with_literal_cups` constructs its inputs from arbitrary
complete choices, with no independence premise. Both orientations with nonempty contexts
are exercised in `CupCompletedChoiceExamples.complete_paired_sector`.
`exists_same_colour_adapted_choices` and `exists_same_colour_adapted_equiv` now
construct simultaneous complete same-colour target choices: a single label
equivalence, literal unpaired terminal crossings, and a common paired embedding
`ℕ × B.Labels` with both cup serializers. Their coefficient comparisons remain open.

## Reservoir-vacuum detection

The separated-sector consumer is now `FusedFixedWeightFamily`, not a family
of moving spectators. Conditional declarations in `ReservoirVacuumDetection`
derive the joint bounded observation identity from composition, connected
reservoir affine coordinates, and the named `NormalizedBubbleFormula` on the
elementary and exterior generators. They then apply bounded ELV separation to
obtain `upwardCoefficientMap_injective` at the same external weight and
`upward_independence_of_fused_fixed_weight_families` for the reduction.
`reservoir_parity_cutoffs_detect` covers arbitrary colourwise even/odd schedules.
`SpectatorEvaluation` remains the one-sector consumer and is not used to
supply the new family's coverage premise.

`ReservoirWeights` constructs cofinal paired cover levels with even probe
level, reservoir parity equal to the prescribed coroot pairing, and exact
level difference. `odd_pairing_invariant` proves invariance under signed root
words. `exists_weights_of_pairing_surjective` realizes the levels in a
pairing-complete lattice; `exists_extended_weights` does so for every datum
in the explicit extension `X × (I → ℤ)`, without changing its Cartan matrix
or parity. `ReservoirWeights.restrictRouquierFamily`, in the
`ReservoirWeightRestriction.lean` module, restricts the actual super
Rouquier factor interface along `μ ↦ (μ,0)`, retaining local inverses and
all parity shifts. Full multicolour action and fused-family construction
remain open.

`QuiverHecke.reservoirWindowCoordinates` in `ReservoirCoordinates.lean`
splits the bounded connected ELV injection over a field and recovers the
whole joint coefficient/PBW window.
`exists_bounded_reservoir_extraction` extends any linear source coordinate
map on that window, without a global finite-quotient automorphism. It does
not identify the regular quotient with the fused vacuum; the latter's
`affine_coordinates` law and normalization comparison remain open.

`ReservoirRegular.lean` constructs the connected quotient's actual cyclic
operators by descending postcomposition. `ReservoirSourceCoordinates.lean`
proves that source coefficient followed by affine action differs from the
joint tensor coordinate by its Koszul diagonal involution, then constructs
`exists_reservoir_source_coordinates` on every C0 window. The involution
preserves bounded windows; it is not asserted to preserve the ELV ideal.
`ReservoirCoverage.lean` supplies `regularVacuumWindow_coordinates` at all
cutoffs, including the zero-window fallback, and
`regularVacuumWindow_covers` for the balanced reservoir schedule.
`exists_regular_vacuum_window` also realizes literal external weight in the
pairing extension. The concrete two-odd consumer is
`scripts/NonVacuity/ReservoirRegularCoordinates.lean`.

`ReservoirFusedVacuum.lean` proves fused-vacuum `affine_coordinates` and
categorical `covers` from a `RegularVacuumIdentification` of the vacuum word
modules with these regular modules (vacuum, affine operators, reservoir
coefficients). `ReservoirFusedBubbles.lean` specializes the first identity of
`SuperRouquierLoc.MateProjectionFormula` to a probe cup and reservoir cap
(`mate_projection_sector_bubble`) and derives `bubbles = reservoir` on all of
`SYM` (`fused_bubbles_eq_reservoir`), the odd bubble being the reservoir's
exterior coefficient (`fused_odd_bubble`).
`upward_independence_of_fused_vacuum_actions` in
`ReservoirFusedDetection.lean` assumes only `FusedVacuumAction` (A0/A1: vacuum
words, regular identification, probe and reservoir coefficient values; A2:
capped mate composite = fused bubble of each generator) and the mate
projection formula. `ReservoirFusedSectors.lean` discharges the mate projection
formula from sector summands through `MateProjectionFormula.of_sectors`, so
`upward_independence_of_fused_sector_actions` assumes only sector summands
with slide, probe inverses and reservoir nilpotence, the vacuum values, the
regular identification and the fused bubble identification. Consumer:
`scripts/NonVacuity/ReservoirFusedDetection.lean`.

`RouquierCoupled.lean` constructs the coupled structure from two separated
factors (`CoupledFactors`: sector decompositions `SectorDecomp` of the coupled
`E₁, F₁, E₂, F₂` into reservoir and probe summands). It builds the diagonal
`coupledAdjunction` with both triangles, the diagonal dots, and the coupled
crossing `coupledCross` as a block matrix on the four summands of `E₁ ≫ E₂`:
factor crossings on the diagonal sectors, the rational position-preserving
cross-sector entries `coupledRationalLeft/Right` (finite series inverting
`y - q x`, nilpotent reservoir and invertible probe; no centrality, odd `q`
allowed), and given sector-swapping blocks intertwining the dots.
`CoupledFactors.slide` proves the coupled upward slide; `sourceSector` and
`targetSector` restrict counits, units and dots as `of_sectors` requires, and
`CoupledFactors.mateProjectionFormula` is the projection formula for the
actual coupled data. `RouquierCoupledSectors.lean` turns this into
`CoupledSectorBubble.toVacuumSectorBubble` and
`upward_independence_of_fused_coupled_actions`. Consumer:
`scripts/NonVacuity/RouquierCoupled.lean`. Remaining inputs of
`FusedCoupledAction`: the family (regular identification), the factor data of
`CoupledFactors` (the sector decompositions of the coupled Hom-family functors
into post/pre summands, sector adjunctions incl. the shifted left adjunctions
of the pre summand, factor dots and diagonal crossings with slides, swap
blocks, probe inverses, reservoir nilpotence), the vacuum values
`probe`/`reservoirValue`/`normalize`, and `fusedBlock`. `RouquierCoupledMate`
proves that a sector projection of the coupled mate is the sector mate of the
corresponding crossing block (`sector_mate_block`, via the transport lemmas
`sectorIn_rouquierMate`/`rouquierMate_sectorOut`), so `fused` reduces to
`fusedBlock`: the probe cup, the sector mate of the rational block
`rationalPR`, and the reservoir cap act as the fused bubble. No `FusedCoupledAction` is
constructed. The quadratic and braid relations of `coupledCross` are not proved
(the projection formula does not use them).

`SKM.reservoir_coefficients_recovered` proves finite triangular inversion of a
specified ordered probe convolution; `reservoir_exterior_recovered` removes a
unit factor from an odd coefficient. The categorical convolution and its
bounded coordinate comparison remain open, as does construction of the fused
family. The connected two-odd examples test the algebraic inputs, not family
existence. See [ReservoirVacuumDetection.md](ReservoirVacuumDetection.md).

## Action review

`CyclotomicAction.SignedMultipliers` checks the signed right-multiplier
composition and a nonzero rational matrix instance: negating both odd
crossings still changes a constant quadratic relation from 1 to -1.
[SignedInductionComparison.md](SignedInductionComparison.md) records the exact
scope. This rules out the uniform-sign, unchanged-parameter assignment, not
an action with a proved directed-sign or parameter comparison. The full
multicolour square and braid comparison remains open. The connected all-odd
`AsymmetricParameters` example has Cartan entries -2,-4 and `Q=u²+v⁴`:
no common crossing-product scalar absorbs the opposite signs of square and
fourth-power dot transport. A valid transported family `Q'=u²-v⁴` and its
conditional signed mixed-square transfer are checked. Thus directed signs
alone with unchanged parameters are insufficient in general; a full
parameter/presentation transport remains necessary.

`CyclotomicAction.Intertwiner` checks the same-colour intertwiners of KKO
(arXiv:1206.5933v2) (8.7)–(8.8) on any signed nilHecke family, hence on two
adjacent equal-colour strands of every word (`oddTwo_block`, `evenTwo_block`).
With the family relations, KKO's `τ_a` is `-εT_j`. Odd colour:
`φ=(v-u)-(v²-u²)T` with `vφ=-φu`, `uφ=-φv`, `φ²=(v-u)²`; the variant `g`
reuses `OddNilHecke.Intertwiner.element` (`g²=-(v²-u²)²(u²+v²)`,
`Tg=T(v-u)(v²-u²)`); far dots and crossings anticommute with `φ` and `g`
(Lemma 8.3, (8.11)–(8.12), (8.15)). Even colour: `φ=1+(v-u)T`, `φ²=1`,
`g²=-(v-u)²`, `Tg=T(v-u)`. The consumer `scripts/NonVacuity/CyclotomicIntertwiner.lean`
uses the all-odd two-colour datum and the polynomial nilHecke representation.
`CyclotomicAction.IntertwinerWords` defines `intertwinerHom l r i j`, KKO's
`g_a e(ν)` from `l++[i,j]++r` to `l++[j,i]++r` (the crossing if `i≠j`, the
variant above if `i=j`), and checks (8.11) for `b=a,a+1`:
`dot_comp_intertwinerHom`, `dot_succ_comp_intertwinerHom`, sign
`(-1)^{|i||j|}`. These are the transports of `x_1` through `g_n⋯g_1` used in
(8.16)–(8.17). `moveHom i l ν` composes them to `g_n⋯g_1 e(i,ν)` (KKO's `Q`,
Proposition 8.4), and `dot_comp_moveHom` is the second identity of (8.13),
`x_{n+1}g_n⋯g_1e(i,ν)=(-1)^{p(i)p(ν)}g_n⋯g_1x_1e(i,ν)`. Far dots pass through
each `g` with sign `(-1)^{p(ν_b)p(ν_a)p(ν_{a+1})}` (`dot_left_comp_intertwinerHom`,
`dot_right_comp_intertwinerHom`), and `dot_mem_comp_moveHom` is the first
identity of (8.13) for dots: `x_b g_n⋯g_1 = (-1)^{p(ν_b)p(i)p(ν)} g_n⋯g_1 x_{b+1}`.
`CyclotomicAction.IntertwinerBalance` moves crossings: `variants_comp_of`
(a morphism intertwining `u,v,T` up to a common sign intertwines both `g`),
`cross_left_comp_intertwinerHom`, `cross_right_comp_intertwinerHom` ((8.12),
sign `(-1)^{p(x)p(y)p(i)p(j)}`) and `cross_left_comp_moveHom`. For crossings of
`R(β)` the first identity of (8.13) is `cross_comp_moveHom` (sign
`(-1)^{p(j)p(c)p(i)p(ν)}`), proved from the three-strand step `meetLeft = meetRight`
(`ψ_{a+1} g_a g_{a+1} = g_a g_{a+1} ψ_a` on `(i,j,c)`). That step is proved for
`i≠j,c` (`meetLeft_eq_of_ne`, braid relation), `i=j=c` (`meetLeft_eq_self`) and
`i=j≠c` (`meetLeft_eq_of_eq_ne`: exact braid on `(i,i,c)` plus dot slides through
`variants_comp_of`); `meetLeft_eq` and `cross_comp_moveHom_of` cover every case but
one. Open: `c=i≠j`,
where the `(i,j,i)` braid correction (`braid_iji`) must cancel against
`cross_cross_ne`; this is the remaining computation (KKO Lemma 8.3, mixed colours).
The braid identity `τ_aφ_{a+1}φ_a=φ_{a+1}φ_aτ_{a+1}` of Lemma 8.3 is checked on
three strands of one colour, for `φ` and for `g`, both parities
(`IsSignedNilHeckeFamily.braid_phiOdd`, `braid_element`, `braid_phiEven`,
`braid_gEven`). Open for KKO Theorem 8.5 (`QP`): the braid identity when the
three colours are not all equal, the composite `g_n⋯g_1` on `(i,ν)`, the map `Q` and the reduction modulo
`R a^Λ(x_2) R^1(β)`.

[ActionReview.md](ActionReview.md) is a proposed source comparison of the seven
steps of the even-cutoff argument. The normality, balanced-ideal, norm and cap-row
repairs survive; the explicit comparison from the super-opposite induction
endomorphisms to the specified upward presentation remains open. Ordinary reversal
for projectivity and super-opposite reversal for natural transformations must not
be identified. No multicolour action is yet claimed in Lean.

`CyclotomicAction.Normality` checks the first-dot normality and inverse
balance equations for even cutoff, the square-zero deformation term and
conjugate square-annihilator, and the odd-cutoff normality and square.
These are ring identities with coefficient commutations and top-coefficient
annihilation explicit, not a constructed normalizing automorphism or a
balanced all-content bimodule. In particular the even inverse-balance dot
is `x+2d`, not `x-2d`. `LocalRelationExamples` checks both balances on
exterior creation/contraction matrices with `x²=1` and `d≠0`, and proves
that using the normalizer instead of its inverse fails. It also constructs
a single directed-sign crossing operator whose constant square is the identity.
Its headline axiom inventory uses only the permitted standard axioms.

[OddCutoffAction.md](OddCutoffAction.md) gives a proposed exterior-translation
reduction for odd cutoffs: `f_i=(x-d_i)C_i(x²)`, with no top-coefficient relation.
The normalizing automorphism acts by parity on coefficients and is involutive;
copying the even-cutoff inverse twist gives the wrong sign. The relative action
extension preserves inversion by triangular dot-row changes. Its unconditional
use still requires the all-content diagram and presentation comparison.

`CyclotomicAction.ExteriorTranslationRelations` proves simultaneous
mixed-dot anticommutation, invariance of arbitrary square-variable mixed
polynomials, and the entire alternating repeated-outer-colour braid
polynomial with a second translated odd middle colour. Its rational
four-dimensional exterior matrices retain a nonzero product of the two
parameters and supply mixed-dot and nonzero braid-correction consumers.
The category equivalence, strand-inclusion compatibility and cyclotomic
quotient descent have not been constructed.

[LowestWeightAction.md](LowestWeightAction.md) records that the proposed
`E=induction`, `-Λ+β` convention is already lowest weight. The opposite orientation
is proposed by signed Chevalley transport into the super-opposite target, reusing
`SKM.chevalleyTwo`. The Hom construction instead reverses one lowest-weight factor
horizontally; it gives two copies of the datum, not their fusion. A nonzero Hom
vacuum and original-datum fusion remain separate requirements.

[ActionLeanPlan.md](ActionLeanPlan.md) orders the proposed construction from
signed induction presentation comparison and simultaneous exterior translation,
through balanced quotients, projectivity, inversion, the action, opposite transport
and the product-datum Hom family. Each module names a consumer and existing
inputs. The next bounded action result is the signed mixed-colour presentation
comparison, not a new abstract action interface.

## Open obligations

1. **Same-colour exchange descent**, source and target. The distinct-colour target proof is
   the template; the equal-colour case must absorb the residual deletion term and its bubble
   corrections.
2. **Distinct-colour source descent**: assemble `SourceExchangeDescent` for `i ≠ j` from the
   adapted-family results above.
3. **The observation interface.** `FiniteUpwardObservations μ t t'` asks for maps into the ELV
   quotient of the coefficient category on the words `t, t'` alone. Over a field it follows from
   upward independence at `μ` (compose the quotient map with the inverse of the coefficient map),
   so it is a restatement of the target, not a weaker statement. An action at lowest weight `-Λ`
   evaluates `E_t 1_μ` only after adding spectator strands `s` with `μ = -Λ + wt(s)`, and `μ` is
   fixed while the cutoff grows. The separation theorem therefore has to be extended to
   cyclotomic quotients with spectators, or the interface restated, before an action can
   discharge it. `SpectatorEvaluation` now states the regular-projective component with
   a specified affine whiskering and bubble lifts on the whole word. Its product law and
   joint detection are still open for an action-derived family. The conditional consumer
   `upward_independence_of_spectators` makes neither of those assertions. Fixed-spectator
   cofinal quotient separation is proved, but does not allow the spectator word to grow
   with the cutoff. The existing quadratic crossing-loss bound fails whenever total
   strand number `n ≥ 3` and cutoff `N ≤ 2n` (`spectator_crossing_bound_obstruction`).
   The next target is a sharper spectator-corner theorem or a fixed-weight reservoir-vacuum
   extraction; neither the failure of this bound nor separate bubble independence decides
   joint detection.
4. **The deformed action.** Independent review of the proposed even-cutoff theorem, in
   particular the balanced maps, the norm audit and the parity conventions of the
   negative-height cap conversion; extension to odd heights at odd colours (the parity of
   `⟨h_i, Λ⟩` is constant on a root-lattice coset when `i` is odd); bubble images at a fixed
   weight with spectators.
5. **Fixed-weight coverage.** Dominant weights are cofinal in each root-lattice coset only in
   finite type, and there odd colours occur only at the short end of `B_n`, never adjacent.
   For general symmetrizable data every weight is `μ₋ - μ₊` with `μ±` dominant, reached by the
   family `Hom(T(-μ₊), W(μ₋))` as in the even case; the super version of that family, and the
   joint detection of the odd bubbles of adjacent odd colours in it, are open. For odd `i`,
   `⟨h_i, μ⟩ mod 2` is constant on root-lattice cosets, so odd cutoffs at odd colours are needed.

## Strict residual serializers
**Strict residual choice interface (checked).** `StrictResidualChoice` rebuilds a complete matching choice using `PointedMatching.ofStrict` on every member. Its `strictResidualLabels` equivalence preserves the exact strict-serializer layers, and `strictResidualChoice_independent` transfers independence by choice invariance. Thus residual independence can be applied to the serializers used in cup completion without identifying them with an unrelated chosen serializer. Contextual same-colour descent is now checked on both sides as recorded below.

`exists_same_colour_cup_rows` now gives complete original, swapped, and residual choices together with the exact evaluated left- and right-cup rows at every dot count and external weight. The unpaired exchange equations are retained. `SameColourCupRowsExamples.complete_cup_rows` checks the interface for a two-colour odd datum over ℚ with both contexts nonempty; its axiom print contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Full contextual target descent

`same_colour_target_exchange_descent` derives independence of the original boundary from independence of its swapped and shortened residual boundaries. The proof kills unpaired coefficients using the actual inverse-crossing formulas modulo the paired output rows, then invokes `pairedExpansion_injective`; both height signs and the zero boundary are included. `target_exchange_descent` combines this with distinct-colour descent and proves the entire `TargetExchangeDescent cs` interface over any commutative coefficient ring admitted by `Sc`. No homogeneity, field, grading, action, or bubble-injectivity hypothesis is added. The concrete two-odd-colour consumer `SameColourTargetFrameExamples.all_target_exchanges` and both headline axiom prints use only the three permitted axioms. `source_exchange_descent` now proves the corresponding full `SourceExchangeDescent cs`.

`SourceFrozenSwap.ren` and `crit` preserve strand renaming and critical IDs. `SourceIdRelabel` now transports validity, full states, cap renamings, and critical lists through injective ID maps fixing fresh IDs; `reducedData_iff` preserves all reducedness data. A cap-containing consumer moves ID zero and checks the actual transports. `SourceCrossState.start_cross` identifies the actual initial-crossing state with the frozen transposition and initial-ID swap, retaining its cap-renamed history in `cross_run`. `SourceCrossAttachment.attach` supplies strict pointed representatives, actual count equivalences and literal initial-crossing serializers. `exists_adapted_pointed_pair` covers both crossing orientations. The complete source choices and coefficient descent use this transport as described in `SourceContextualSorting.md`.

`SourceCapState.start_cap` now identifies the exact initial-cap state, including the reversed frozen endpoints, surviving strand ID and fresh counter. `cap_matching`, `cap_strict`, `cap_layers`, `ren_cap` and `crit_cap` give validity, strictness, layer orientation and full suffix transport. The nonempty-context two-colour consumer checks these identities. `SourceCapAttachment` supplies the residual comparison by inserting the frozen pair and shifting fresh IDs by four. `attach` constructs actual cap-adapted pointed representatives, `cap_family_complete` proves coverage of every paired source class from a complete residual family, and `labelEquiv`/`attach_layers` provide the full count bijection and literal serializer compatibility. The fresh-cup and later-cap consumers check both creation and subsequent ID joins. `SourceCompletedChoice` now assembles the cap and unpaired sectors. `exists_source_same_colour_adapted_equiv` supplies complete choices, the full label equivalence and paired embedding with literal cap serializers on both sides; residual serializers are exactly `PointedMatching.ofStrict` on `B.members`. `exists_source_adapted_distinct_colour_choices` gives complete distinct-colour choices and both initial-crossing cases. These constructions add no independence hypotheses. `distinct_source_exchange_descent` now proves the distinct-colour source branch using these actual complete choices and `distinct_source_adapted_independent`, with the native full-SYM crossing twist. It requires only swapped-boundary independence. `SameColourSourceFrame.kernel_supported_paired` eliminates the unpaired kernel using the actual inverse crossing. `PairedSourceUpwardColumns`, `PairedSourceCupColumns` and `PairedSourceDetection` prove all-height paired detection, retaining inverse-block corrections and negative-height low-cup components. `source_cap_downward_triangular` converts the actual downward-dot serializer to upward-dot columns with a unit leading coefficient and the odd-bubble correction; `pairedExpansion_injective` retains this correction. `same_colour_source_exchange_descent` and `source_exchange_descent` conclude source descent over arbitrary permitted commutative coefficient rings, without field, grading or homogeneity assumptions. The two-odd-colour consumer `SameColourSourceFrameExamples.all_source_exchanges` and its nonempty-context full-SYM column use only the permitted axioms.

## Upward-to-oriented reduction

`SKM.nondegeneracy_of_upward_independence` in `UpwardNondegeneracyReduction.lean` combines `WeakMate.sorted_independence` with both proved contextual exchange descents. Its only independence premise is `WeakMate.UpwardIndependence cs`, at every weight over full abstract `SYM`. `nondegeneracy_iff_upward_independence` supplies the converse. No field, finite-colour, symmetrizer, grading or coefficient-homogeneity restriction is added by the reduction. The concrete two-odd-colour consumer is `UpwardNondegeneracyReductionExamples.two_odd_colour_reduction`. Both headline axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. This closes B0, not the action or upward-detection obligations needed to establish its premise. The source and target sorting notes record the checked status as well as the mathematical formulas.

## Next targets

**Actual paired target columns (checked).** `SameColourTargetFrame` attaches the complete adapted choices to finite principal columns at every local height, retaining arbitrary abstract `SYM` inputs and both boundary contexts. `positive_column` and `nonpositive_column` identify their expansions with actual postcomposition by the same-colour crossing. `PairedTargetCapColumns` constructs the normalized low-cap columns. `targetPositiveColumns_detect` and `targetNonpositiveColumns_detect` prove finite coefficient detection by the actual unit pivots, with both inverse-block and dot-slide corrections included. `SameColourTargetFrameExamples` checks positive and negative local heights in a two-colour odd datum with nonempty contexts and residual labels. Full target and source descent and B0 are now checked as described above.

`SameColourTargetFrame.pairedExpansion_injective` proves all-height independence of the actual paired sector from swapped and residual independence. Its positive-height proof uses the actual low cap outputs; its nonpositive-height proof needs only swapped independence. `plcW_comp_at` supplies composition through a propositionally equal contextual boundary. The axiom print uses only `propext`, `Classical.choice`, and `Quot.sound`.

These statements were proved by the methods recorded in the linked notes but are not yet on
this branch:

- all-height paired target coefficient columns; source crossing state and point transport;
  contextual source-cap families (complete same-colour target adapted choices are now in Lean)
  ([ContextualSorting.md](ContextualSorting.md), [SourceContextualSorting.md](SourceContextualSorting.md));
- bounded ELV coefficient recovery with locally triangular inversion, and nilpotence of the
  coefficient dot ideal ([UpwardSeparation.md](UpwardSeparation.md));
- odd Frobenius resolvent identities beyond `FrobeniusResolvent`, and the first separated-sector
  chart lemmas ([SpectralCompensation.md](SpectralCompensation.md));
- the parity involution on the coefficient basis and the source/target `β` placement identity;
  the negative-height cap-row conversion ([MulticolourCyclotomicAction.md](MulticolourCyclotomicAction.md)).

## Mathematical guardrails

- Abstract `SYM` has a distinct exterior generator for each odd colour. Spectator strands do
  not show that categorical bubbles realize those generators.
- Signed choice transitions lower crossing/open-dot complexity; closure transport adds dots at
  fixed crossings. Do not conflate the two orders.
- Right coefficient extension uses `d*p`, not `p*d`.
- Inverting an even ELV constant kills the odd parameter of that factor
  (`CyclotomicExteriorObstruction`); separate nilpotent factors are not excluded.
- Squared-dot spectral blocks preserve parity; odd-dot scalar eigenblock compression is not a
  multiplicative coefficient detector.
- The odd intertwiner has norm `-(y²-x²)²(x²+y²)`; generic transport needs both difference and
  sum units.
- At even cutoffs the cyclotomic element is normal, not central: `ν(x) = x - 2d`, and right
  multiplication uses `ν⁻¹(x) = x + 2d`. KKO's centrality step does not apply verbatim.
- [ELV] Theorem 4.5 supplies the rank-one deformed action with odd coefficients and
  Proposition 4.7 its bubble values; the universal-equivalence part of that proof uses rank-one
  nondegeneracy and must not be used circularly.
- The isomeric Heisenberg action is reduced (odd bubble zero) and cannot detect exterior
  coefficients by itself.
- The two-colour connected degree-two model has `δ_i δ_j ≠ 0` but `(reverse crossing)·δ_i δ_j = 0`,
  so joint detection of crossings and bubble products is a separate requirement.
- Finite Python models in `scripts/Nondegeneracy/` test particular instances; none is a proof of
  a general statement.

## Notes

[PROGRESS.md](PROGRESS.md) (status board), [OrientedReduction.md](OrientedReduction.md),
[MatchingChoiceTransition.md](MatchingChoiceTransition.md), [UpwardSeparation.md](UpwardSeparation.md),
[MulticolourActionTheorem.md](MulticolourActionTheorem.md),
[MulticolourCyclotomicAction.md](MulticolourCyclotomicAction.md),
[SpectralCompensation.md](SpectralCompensation.md), [CoupledBubbleEvaluation.md](CoupledBubbleEvaluation.md),
[OddUnfurling.md](OddUnfurling.md), [RewritingAlternative.md](RewritingAlternative.md).

### Vacuum strand inclusion

`CyclotomicAction/Vacuum.lean` supplies `vacuumAppend`, the nonunital algebra map
from `Hn D Sc 0` to `CyclotomicAlgebra D Sc a 0` obtained by adding the first
strand and applying the existing height-one quotient map. `vacuumAppend_one`
and `vacuumAppend_scalar` identify its unit and scalar images with the
single-colour cut; the cuts are idempotent, mutually orthogonal, and act as
units on the corresponding images. `vacuumAppend_parity` and
`vacuumColourCut_parity` give the homogeneous-parameter parity formulas.
This closes the algebra-map boundary at height zero; vacuum superinduction
and the categorical inversion relations are not asserted here.

`CyclotomicAction/VacuumExamples.lean` proves that the vacuum unit and the
scalar two have nonzero images for the rational odd rank-one datum and
zero cyclotomic polynomial. The proof reduces the defining ideal to zero
and uses affine normal-form independence; it is not a positive-degree
monic or finite-dimensional cyclotomic nonvanishing theorem. The scalar
two also lies in the even quotient component. Both vacuum modules pass
targeted warning-as-error builds and an owned-declaration axiom audit.

### Three-strand cyclotomic braid

`CyclotomicAction/Braid.lean` defines the first-pair and last-pair crossing
matrices on the actual `w ++ [i,j,c]` corners. `tripleMatrix_mul` proves that
multiplication of these finite families is reversed pointwise composition.
`affineTriple_braid` and `cyclotomicTriple_braid` prove the uncorrected braid
when the outside colours differ or all three colours coincide, with arbitrary
old words and arbitrary colour parities. These are concrete algebra identities,
not yet the braid between three composed superinduction functors. The latter
still requires comparison with the balanced-tensor associators.
`CyclotomicAction/BraidCorrection.lean` supplies the separate repeated-outside-
colour polynomial relation: `affineTriple_braid_correction` and
`cyclotomicTriple_braid_correction`. Its explicit dot polynomial retains
`(-1)^(|i|(|j|+s))` in every divided-difference term. Both braid cases now hold
in the actual quotient; neither statement assumes a categorical representation.

`BraidOperators.lean` proves the homogeneous degrees of both triple crossing
matrices and carries both quotient identities to signed operators on the
existing graded regular module. `cyclotomicSignedTriple_braid` has no
additional sign. `cyclotomicSignedTriple_braid_correction` retains the
factor `(-1)^(|i||j|)` on signed multiplication by the explicit correction.
No parity restriction on the three colours is imposed. These regular-module
operator identities still do not identify triple induction associators.

### Equal-colour crossing square

`CyclotomicAction/Square.lean` identifies the associator-defined last crossing
with its positioned-word diagram. `cyclotomicLastCrossing_square` proves
square-zero in the concrete quotient. `compositionSuperCrossing_square` proves
square-zero for the actual signed superbimodule map on the composition corner;
it is not merely a statement about an unsigned multiplier. No local inversion
or projectivity is used or concluded.

`CyclotomicAction/Comparison.lean` transports this identity through the existing
even balanced-tensor isomorphism. `inductionCrossingApp_square` concerns the
actual composed superinduction functors; `cyclotomicSuperInductionCrossing_vcomp_app`
shows that every parity component of the supernatural vertical square is zero.

### Mixed quadratic polynomial

`CyclotomicAction/MixedComparison.lean` defines `wordQuadratic` by the specified
`t` and `s` coefficients and the two actual positioned dots.
`cyclotomicLastCrossing_mixed` identifies the product of opposite crossings
with its image in the concrete quotient, for both connected and disconnected
colours. `compositionSuperCrossing_mixed_apply` proves the resulting identity
on every homogeneous element of the actual composition superbimodule. Its
factor is `(-1)^(|i||j|)`, independent of input parity; dropping it would give
the unchanged-parameter error. This is an upward quadratic comparison, not
the mixed induction–restriction Mackey isomorphism.

`ParameterTransport.lean` constructs `parameterTwist`, an involutive
transformation of valid even scalar families, and proves preservation of
homogeneous support. Its monomial sign exponent is
`|i||j| + |i|⌊p/2⌋ + |j|⌊q/2⌋`; the support conditions exclude odd powers
of an odd dot. `oddRight_iterate_even` proves the half-exponent sign for
all even powers of a signed odd multiplier. These coefficient statements
are not by themselves compatibility of all categorical generators.

`ConcreteRelationExamples.lean` checks this coefficient family on the
all-odd datum `[[2,-2],[-4,2]]`, recovers the transported leading units,
and proves the quadratic-minus-quartic identity in the actual affine and
cyclotomic algebras. It checks the minus sign on the actual composition
superbimodule. The repeated-colour polynomial is the last dot minus the
first dot, and the corresponding affine matrix braid is proved. These
are relation consumers, not nonvanishing or local-inversion theorems.

## Parity-compatible probe reachability

[ProbeReachability.md](ProbeReachability.md) separates the proved weight
choice from the remaining categorical vacuum construction. Specializing
`exists_regular_vacuum_window D Sc μ t t' d`, together with `probe_even`,
already gives every original weight an even probe cutoff and a cofinal
reservoir cutoff of the required parity, with exact extended difference
`(μ,0)` and injective regular ELV coordinates. No finite-type or original
pairing-surjectivity assumption is used. The extension retains coroot-kernel
coordinates as well as the prescribed pairings.

`restrictRouquierFamily` restricts the supplied factor interface, not a
constructed full fused action. The remaining regular-vacuum obligation is
to construct the actual `FusedVacuumWords` and the maps and three identities
of `RegularVacuumIdentification` for the same balanced cutoffs. The
`FusedCoupledAction.family` field assumes these data; its sector fields
still require the vacuum values, normalization and fused bubble block.
Thus A3's parity-compatible arithmetic and algebraic regular windows are
closed, while full-action restriction, regular-vacuum identification and
the actual bubble comparisons remain open.

[RegularVacuumComparison.md](RegularVacuumComparison.md) gives a proposed
module-level derivation: contract the defining representable induction
tensor by `b ⊗ m ↦ b ≫ J_i(m)`, with inverse `h ↦ h ⊗ 1`, and take the
source-word component. A content-zero-supported Hom vacuum kills every
probe term by the corner equation `e_0 B_i^probe e_β = 0`, not by numerical
weight arithmetic. The contraction gives the three coordinate identities
for these defining tensor maps. Still missing is the identification of the
connected ELV factor's induction bimodules and signed dots/crossings with
these representable maps, together with the content-supported Hom vacuum
and fusion's upward-block comparison. This is a written derivation, not a
new Lean theorem or a construction of `RegularVacuumIdentification`.
The normalized bubble inverse-block comparison remains separate.

