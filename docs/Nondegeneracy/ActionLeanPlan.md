# Plan for the deformed action in Lean

## Globalization: content and height-zero prerequisites

The even `CyclotomicAction/Global.lean` starts with `CycKLR β` for every
multiset, including `β = 0`. The positive-height super API instead has
`CyclotomicAlgebra a n = H_(n+1)/(a)`. Replacing its index by the weight is
not a type-correct port: for distinct simple roots, singleton contents have
the same height but different weights. `CyclotomicAction.blockWeight_not_card` proves
this obstruction; a pair of orthogonal odd roots is a concrete smallest
instance. `ContentBlocks` supplies central, mutually orthogonal content
projectors, and `ContentSupport` proves induction preserves the appropriate
content. The empty source must be the empty-word algebra, not
`CyclotomicAlgebra a 0`, which already has one strand.

The precise missing boundary for the crossing chain is the crossing of two
inductions **starting at height zero**, and its compatibility with the
positive-height crossing after one more induction. For the braid this is
already required at `β = 0` and three appended colours (three strands total).
`cyclotomicTriple_braid` in `Braid.lean` supplies the algebraic identity at this height,
but its transport through the balanced-tensor comparisons and associator is
separate. The existing functor-level comparison starts at a source
`CyclotomicSupermodules ... n`, hence at one strand. Extending that comparison
to the empty-word source is a construction obligation, not a counterexample
to the super action.

`GlobalNilpotent` additionally requires a quotient-level nilpotence theorem
for the undeformed powers `a_j = X^(Λ_j)` and the appropriate homogeneous
super parameters. Polynomial parity alone is not the theorem's hypothesis.
Even after blockwise nilpotence, a single exponent on a weight product needs
a uniform bound; the even file assumes at most one content per weight.
Neither arbitrary deformation parameters nor infinitely many unbounded
blockwise exponents can be silently substituted for those assumptions.

The local inversion target remains `SKM.SuperRouquierLoc`: the prescribed
cup–crossing–cap mate and dotted caps/cups must possess the parity-indexed
`SuperSumInvTo` and `SuperSumInvFrom` inverses at height `D.h i x`. A family
of independently chosen inverse maps is not a substitute. The conversion
from the block convention is `CyclotomicAction.blockLoc_weight`; the absent-colour
boundary sign is `CyclotomicAction.pair_nonpos_of_not_mem` under dominance.


Status: **proposed formalization plan**. No proposed declaration name below
is an existing theorem. Existing inputs are named separately. The scope is
the compatible symmetrizable homogeneous-parameter case over a field with
the required scalar units; both cutoff parities at odd colours are retained.
Integral descent and nondegeneracy are downstream, not part of this action
acceptance boundary.

## First useful result and stop conditions

The first useful result is an explicit, signed affine presentation comparison
on the regular induction bimodule, including a mixed-colour crossing square
and a repeated-outer-colour braid. This addresses the gap in ActionReview.md
before building a large abstract representation interface.

The complete action result must construct functors and natural transformations
for the specified SKM presentation, using the original tensor adjunction and
proved inversion matrices. A structure whose fields assume these relations is
not completion. Conversely, action existence does not include coefficient
faithfulness, nonzero Hom vacua in an arbitrary target, or fusion of a product
datum. LowestWeightAction.md and GeneralRoute.md separate those obligations.

The order below is a proposed implementation decomposition, not an additional
mathematical hypothesis. The main theorem should quantify over a cutoff vector
with a supplied weight-pairing equation, not infer a weight from arbitrary
natural numbers in an unspecified weight lattice.

## Even-parameter implementation boundary

The first implementation stage has a commutative, purely even coefficient
ring. Odd colours are retained. Exterior ELV coefficients are a second stage:
no exterior-parameter extension is needed to state the first action theorem.
The underlying one-strand polynomial quotient exists for arbitrary monic
polynomials, but its super grading requires homogeneity; these assertions must
not be conflated.

`QuiverHecke/CyclotomicAbsentColour.lean` starts the port with the actual
one-strand endomorphism algebra. `singlePolynomialEquiv` identifies evaluation
at its dot with a polynomial algebra, using the existing affine normal-form
basis. `singleCyclotomicEquiv` identifies its cyclotomic quotient with
`AdjoinRoot`, and `singleCyclotomicFinEquiv` gives the monic finite coordinates.
This is only the vacuum-boundary algebra input, not an induction functor or a
local inversion theorem.

The positive-height algebraic and super-adjunction prerequisites are now
implemented in `CyclotomicAction/{Quotient,Induction,Parity,SuperQuotient,
SuperInduction,SuperRestriction,CornerPairing,SuperAdjunctionUnit,
SuperAdjunctionCounit,SuperAdjunction}.lean`. They use the actual two-sided
polynomial ideal in `Hn`, its homogeneous quotient, and the colour-cut
superbimodules `B φ(1)` and `φ(1) B`. `cyclotomicSuperIndResAdjunction` has
even unit and counit and parity-preserving Hom bijections. These statements
need the coefficient-support condition `CyclotomicPolynomialParity`, but no
monicity or flatness assumption.

`LastDot.lean` and `SuperDot.lean` now supply the concrete quotient dot and
its homogeneous supernatural transformation. `InductionComposition.lean`
identifies the balanced tensor of two colour-cut induction bimodules with
the corner of the composite inclusion. `LastCrossing.lean` and
`SuperCrossing.lean` supply the concrete quotient crossing and its signed
superbimodule map; `InductionFunctorComparison.lean` and
`CrossingTransformation.lean` transport it to composed induction
superfunctors. `ActionSupercategory.lean` packages the category, functors,
dot and even adjunction in the existing `TwoSCat` and `SKM.SuperAdjunction`
interfaces.

The vacuum algebra inclusion is now in `Vacuum.lean`; its superinduction
boundary is still separate. `Square.lean` and `Comparison.lean` prove
square-zero for the actual signed corner crossing and for composed
superinduction. `MixedComparison.lean` proves the explicit two-dot polynomial
square on the actual quotient and the super-opposite sign on composition
corners. `Braid.lean` and `BraidCorrection.lean` prove both three-strand
relations in the actual quotient. These algebra identities do not identify
the three crossings with whiskered transformations through the triple
balanced-tensor associators.

The projective resolution and the projective Mackey/local-inversion theorem
are not implemented. The finite monic coordinates above are not a proof of
those higher-content assertions. In particular, the even
`CyclotomicAction/KangKashiwara.lean` is only the final transport: it invokes
`ConcreteAdjunction.loc` and `BoundaryAdjunction.coefficients`, not just the
quadratic and braid relations. Their signed analogues are still required.
The final same-colour inversion must instantiate `SKM.SuperRouquierLoc` from
`SKM/RouquierData.lean`, with the prescribed mate and parity-indexed inverse
entries. Do not replace its odd shifted summands by ordinary copies of the
identity. The unchanged-parameter obstruction and corrected directed crossing
in `SignedInductionComparison.md` remain part of the comparison obligation.

After the even-parameter local inversion compiles, extend coefficients by the
ELV algebra, prove the homogeneous normal first-dot relations and compatibility
with strand inclusions, then carry the balanced projective resolution and mate
matrix through the extension. Only then restore exterior-translated dots and
verify both odd cutoff parities. The detailed exterior steps below specify
that second stage, not prerequisites to the even-ring port.

## Signed naturality at the induction boundary

The next nonliteral port is the ordinary intertwiner used by
`InductionAlong.natTrans` in the even induction file. Its premise for a new dot
`c` is `f(r) * c = c * f(r)` for every element `r` of the lower algebra.
For an odd new colour this must instead be the homogeneous equation
`f(r) * c = (-1)^(|r||c|) * c * f(r)`. In the two-strand odd polynomial
corner over `ℚ`, take `r = x₁` and `c = x₂`: the affine PBW monomial
`x₁ x₂` is nonzero and `x₂ x₁ = -x₁ x₂`. Thus the unsigned intertwiner is
false already in this affine input; it cannot be used to manufacture an
ordinary natural endomorphism of induction. This is not a failure of the
super action route. The replacement is a homogeneous transformation, or an
even transformation to the parity-shifted functor, with the signed balanced
tensor formula.

The exact target, suppressing integer grading shifts, is the decomposition in
Kang–Kashiwara–Oh, arXiv:1303.1916v2, §8.3, Theorem 8.13. For
`h = ⟨hᵢ, Λ-β⟩ ≥ 0` it is
`Πᵢ Fᵢ Eᵢ ⊕ (⊕_{0≤r<h} Πᵢ^r Id) ≅ Eᵢ Fᵢ`; for `h < 0` it is
`Πᵢ Fᵢ Eᵢ ≅ Eᵢ Fᵢ ⊕ (⊕_{0≤r<-h} Πᵢ^(r+1) Id)`.
The same section defines the homogeneous monic polynomial in (8.12), the
actual two-sided quotient in Definition 8.10, and the induction/restriction
superfunctors before Theorem 8.12. These are distinct obligations: an ordinary
module adjunction after forgetting parity does not prove Theorem 8.13.

## Dependency order and concrete consumers

### 1. `QuiverHecke/CyclotomicAction/Presentation.lean`

**Proposed headline:** `induction_upward_relations` for the precise signed
right-multiplier assignment. Start at the affine regular bimodule, with word
order and crossing scalars explicit. Include the source/target polynomial
parameter equality, not just preservation of parity.

**Existing inputs:** `QuiverHecke.pres`, the affine generators and relations;
`QuiverHecke.alphaPrime` in `QuiverHecke/AlphaPrime.lean` is a model for an explicitly
super-opposite source, not itself the induction comparison.
`OddMath.SKM.chevalleyTwo` supplies the signed source symmetry if the
comparison uses that route. `Categorification.KLR.CyclotomicAction`'s
presentation and global-family modules give the even blueprint, not a
super theorem to instantiate unchanged.

**Consumer:** actual dot and crossing transformations in Step 7, and the
mate calculation in Step 6. A rank-one odd dot-slide, an odd/odd distinct
crossing square, and a repeated-outer-colour braid are required nonvacuity
consumers. Stop and repair the parameter assignment if any fails; do not
hide failure by restricting to even colours.

### 2. `QuiverHecke/ExteriorTranslation.lean`

**Proposed headline:** `exteriorTranslationEquiv`, an equivalence of the
coefficient-extended affine category fixing crossings and translating each
chosen odd colour by its own exterior coefficient. Its inverse negates all
translations. State compatibility with word concatenation and strand
inclusions, not merely an equivalence of individual endomorphism rings.

**Existing inputs:**
`OddNilHecke.DotTranslation.square`, `even_pow`, `odd_pow`, `slide`,
`braidPolynomial_translate`; the signed coefficient extension used by
`QuiverHecke.elvCyclotomic`.

**Consumer:** Step 3's odd-cutoff quotient equivalence and the restoration
of prescribed dots in Step 7. Prove the simultaneous two-odd-colour case;
translation at one colour alone is not that consumer. This step can be
checked independently of Step 1.

### 3. `QuiverHecke/CyclotomicAction/Quotient.lean`

**Proposed headlines:** `cyclotomicHomQuotient`,
`oddCutoff_translationEquiv`, and the strand-inclusion maps. Present the
coefficient algebra as the prescribed ELV quotient, with independent odd
parameters. State the parity of each first-strand polynomial explicitly.

**Existing inputs:** `QuiverHecke.ELVGenerator`, `ELVRelationSpan`,
`elvCyclotomic`, `evenCyclotomic`, `SKM.SYM.elvMonicCoefficient` and
`SKM.SYM.elvCoefficientIdeal`. Reuse the existing relation spans rather
than introducing a second quotient with no comparison map.
`QuiverHecke.Hn.basis`, `QuiverHecke.linearIndependent_nf`, and
`QuiverHecke.extensionBasis` provide affine coordinates; they do not imply
that the cyclotomic quotient is free over its parameter algebra.

**Consumer:** balanced induction/restriction bimodules in Step 4 and
comparison of action evaluation with `ELVRelationSpan` for later detection.
Prove equality of the new quotient kernel with that span, including the
coefficient relations, rather than only one ideal inclusion.

### 4. `QuiverHecke/CyclotomicAction/Balanced.lean`

**Proposed headlines:** `P_balanced`, `Q_balanced`, `range_P_eq_kernel`.
Define K₀,K₁ and all parity/normality twists, preserving
`Π_i^(N_i+p(β))` for arbitrary cutoff parity. The coefficient parity
involution must act on the coefficient algebra. Prove the balance equation
on old dots, old crossings and coefficient generators before using a tensor
quotient lift.

**Existing inputs:** Step 3's quotient, the affine PBW/shuffle decomposition
(`QuiverHecke.shuffleBasis`), and the existing signed affine relations.
The written calculations in MulticolourCyclotomicAction are specifications,
not declarations to import. Even cyclotomic modules from categorification-lean
are proof patterns only: their central polynomial action is not the present
normal polynomial action.

**Consumer:** injective projective resolution in Step 5 and the exact Mackey
diagram in Step 6. Include the first nontrivial old-crossing balance with
repeated outside colour as a concrete consumer.

### 5. `QuiverHecke/CyclotomicAction/Projective.lean`

**Proposed headlines:** `QP_eq_norm`, `P_injective`,
`induction_projective_both_sides`, `PQ_eq_norm`.

Order within the file or its smaller dependency modules:

1. Prove the actual QP product; distinguish the repeated-colour S factor
   from the intertwiner square `−Δ²S` and the longest-crossing factor `−Δ²`.
2. Derive injectivity by leading polynomial coordinates.
3. Obtain a central square-variable monic annihilator directly from f;
   propagate it using affine relations.
4. Restrict the resolution to B[s], s=t², and apply the central-polynomial
   projectivity lemma. Repeat on the ordinary opposite with parameter sign.
5. Deduce PQ by factorization through the annihilated cokernel.

**Existing inputs:** Step 4 and affine coordinates; the even
Kang–Kashiwara argument represented in categorification-lean is a blueprint.
A generic central-variable module lemma may be reused if its hypotheses
match exactly; no declaration implementing the deformed application is
currently identified. Do not claim reuse of a theorem merely because it
has the word “projective” in its name.

**Consumer:** restriction preserves projectives, exactness under tensoring,
and the companion norm used to prove Step 6's filtered degree estimate.
No fibrewise flatness argument and no use of PQ to prove the projectivity
that is needed to derive PQ.

### 6. `QuiverHecke/CyclotomicAction/Inversion.lean`

**Proposed headlines:** `mackey_exact`, `phi_leading`,
`sameColour_inversion`, `distinctColour_inversion`.

Define the same mate map used by the tensor unit and counit. Establish the
semilinear recurrence and the filtered defect with exact coefficient order.
Construct both signs of the height matrix, including height zero. Identify
the unit leading coefficient and the correspondence between KKO's height
and weight −Λ+β.

**Existing inputs:** Step 5;
`OddMath.SKM.OddDotTranslation.kko_cap_rows`, `cap_rows_eq_shiftedCap`,
`cap_rows_recovered`. These prove the cap conversion after its operator
hypotheses are supplied by the actual bimodule formulas.

**Consumer:** Step 7's inverse generators. A theorem merely asserting two
functors are isomorphic does not identify the needed matrix.

### 7. `SKM/CyclotomicAction.lean`

**Proposed headline:** `cyclotomicAction`, a graded two-superfunctor from
the specified SKM category to the concrete completed projective-supermodule
target, with generator evaluation lemmas. Give `E=induction`,
`F=restriction`, `weight=−Λ+β`, and the actual unit/counit explicitly.

**Existing inputs:** Steps 1 and 3–6, the native SKM presentation and its
two-superfunctor infrastructure. The even
`Categorification.KLR.CyclotomicAction.cyclotomicFamily`,
`cyclotomicFamily_upKLR`, `cyclotomicFamily_brundanUpKLR`, and
`cyclotomicFamily_mixedInversion` describe the corresponding completion
boundary, not a proof for the super coefficient algebra.

**Consumer:** concrete lowest-weight reservoir, its bubble evaluation,
and the opposite/Hom constructions. Use Step 2 to obtain the odd-cutoff
parameter extension while preserving the specified dot images. A compiled
nonzero vacuum and evaluation of a single odd dot at cutoff one are small
consumer checks. Do not add a faithfulness field.

### 8. `SKM/CyclotomicAction/Opposite.lean`

**Proposed headline:** `highestWeightAction`, obtained by super-opposite
transport of Step 7 and `chevalleyTwo`. State its weight support and vacuum
annihilation, with generator equations carrying the crossing sign.

**Existing inputs:** `SKM.chevalleyTwo`, `chevalleyQTwo`,
`chevalleyQReverseTwo`, plus target-side opposite infrastructure. Do not
reprove the source Chevalley theorem. Where a concrete opposite-algebra
identification is used, include the cutoff-dependent coefficient transform
from LowestWeightAction.md.

**Consumer:** highest-weight test objects and comparison of their
normalized bubbles. Horizontal reversal for the next step is not this
vertical super-opposite functor.

### 9. `SKM/SuperHomProduct.lean`

**Proposed headline:** `homProductAction` for the product datum, on
`Hom(T(−x₂),W(x₁))`, with super-interchange and a concrete nonzero vacuum.

**Existing blueprints:**
`Categorification.TwoRep.RouqFamily.reverse`, `yoneda`, `homProduct`,
`homProduct_upKLR`, `homProduct_mixedInversion`;
`Categorification.KLR.Unfurling.coverProduct`. Reuse their separation of
postcomposition and precomposition, not their unsigned mixed calculations.
Use the existing super-bicategorical infrastructure for homogeneous maps.

**Consumer:** the separated-sector fusion theorem in GeneralRoute.md.
This module must not export an original-datum action just by summing the
two weights. Original-datum fusion is a separate research acceptance
boundary, not hidden in the implementation plan for cyclotomic actions.

## Verification and claim discipline

Each headline has a concrete downstream consumer above. Alongside scoped
module checking, the consumer should use actual presented objects and
maps, not a trivial ring or an empty colour type. The mixed-colour checks
must include two distinct odd colours where the datum permits them.
Allow only the repository's standard logical axioms and no unproved action
or independence assumptions disguised as global instances.

The source comparison has identified signs and normality as the first
failure modes. Check those before generalizing the target bicategory.
A proposed written argument requires independent mathematical criticism
before it is used as a claimed proof; Lean completion then requires the
usual build and axiom audit. No additional proof-management infrastructure
is needed for this boundary.

## Detection is a separate consumer

`QuiverHecke.even_elv_quotients_jointly_detect` and
`elv_quotient_injective_on_extendedAtMost` already detect finite affine
coefficient data in their specified quotients. They do not produce an
SKM action at arbitrary fixed weight. The eventual bridge needs the
explicit evaluation from Step 7, spectator strands or a fused Hom vacuum,
and the normalized bubble comparison. It must not use
`FiniteUpwardObservations` as an assumed consequence of action existence:
that is the very bridge still to be proved.

The next bounded deliverable recommended by this plan is Step 1, followed
by Step 2's simultaneous translation equivalence. Do not begin with a new
general theory of all supermodule bicategories before the first signed
presentation comparison is checked.
