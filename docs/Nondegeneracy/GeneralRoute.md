# A proposed route to super nondegeneracy

**Status: proposed.** This is a dependency graph, not a proof of
`SKM.NondegeneracyConjecture`. Statements labelled proposed remain obligations
unless an existing Lean declaration is explicitly named. Finite tests below do
not establish a categorical action.

## Scope and the even comparison

The target is finite-colour compatible symmetrizable Cartan superdata with
homogeneous scalar parameters, including mixed parity and adjacent odd colours.
The ground field must satisfy the prescribed scalar-unit hypotheses, including
invertibility of two when odd colours occur. First prove the field result; then
prove presentation base change and integral descent over the appropriate universal
parameter ring. Do not silently replace general homogeneous parameters by KL
parameters or exclude odd coroot heights.

The comparison is Webster, arXiv:1603.06311v3, Theorem 3.6 and its proof, pp. 37–39.
There are two uses of spectral labels: independent bubble coordinates and isolation
of strand diagrams. His proof separates the two signed collections of connected
spectral components before reversing one collection. The even Lean proof packages
this using `KLR.Unfurling.coverFamily`, `coverProduct`,
`TwoRep.RouqFamily.homProduct`, `TwoRep.Furling.*`, and the generic evaluation.
The proposed super route replaces strand-label separation by the existing signed
PBW/ELV separation theorem. This replacement does **not** automatically replace
the categorical construction that joins the two weight sectors.

In particular, `homProduct` is a family for the **product root datum**. It is not
already an action for the original datum at the difference of its two weights.
The missing step is fusion of the duplicated colours, with the original upward
relations and mixed inversion. The distinction remains even if the two factors
are individually faithful.

## Dependency graph

The labels A (action), B (reduction), C (detection) designate mathematical
work packages. Each node lists its statement, even analogue, existing input,
new obligation, and risk. Arrows denote logical dependence, not completion.

```text
A0 coefficients and cyclotomic actions ──> A1 opposite/Hom product
          │                                      │
          └──> A2 separated-sector fusion <───────┘
                         │
                         ├──> A3 arbitrary fixed-weight test objects
                         └──> C1 normalized bubble transport
C0 bounded signed affine separation ──────────────┐
A3 + C1 ──> C2 simultaneous cyclic coordinates ───┤
                                                v
                                      C3 upward independence
                                                │
                                                v
                                      B0 oriented reduction
                                                │
                                                v
                           B1 field NondegeneracyConjecture
                                                │
                                                v
                                      B2 integral descent
```

### A0. Deformed cyclotomic super actions — A

**Proposed statement.** For every sufficiently large dominant cutoff vector,
including either parity at each odd colour, the deformed cyclotomic supermodule
towers define the specified SKM induction/restriction action. Dots, crossings,
units, counits and inverse matrices must be the presentation's maps. Construct
both weight orientations with the required parameter and parity changes.

**Even analogue:** `KLR.CyclotomicAction.theta` is the upward comparison; the
action input is the cyclotomic Rouquier family used by `coverFamily`.
**Existing:** affine super PBW, local intertwiner/norm identities, coefficient
superextension, and the proposed even-cutoff argument in
[MulticolourActionTheorem.md](MulticolourActionTheorem.md). The branch's local
norm proofs are not the all-content action. **New:** balanced bimodule maps,
projectivity, exact sequences, inversion, and odd-cutoff extension.
**Risk: high.** Even-cutoff polynomials are normal rather than central; an
unmodified central-coefficient argument is invalid.

### A1. Super opposite, Yoneda and Hom product — A

**Proposed statement.** Given the two actions, precomposition with the suitably
reversed first and postcomposition with the second act on
`Hom(T(-μ₊), W(μ₋))` as a super family for two disjoint copies of the datum.
The object and all parity shifts must be specified in a concrete super-bicategory.

**Even analogue:** `TwoRep.RouqFamily.reverse`, `yoneda`, `homProduct` in
`TwoRep/RouqProduct.lean`. **Existing:** generic categorical infrastructure and
super-interchange in the dependency libraries; no super `homProduct` discharging
this assertion is identified here. **New:** super-opposite signs, odd natural
transformations, parity-shifted adjunctions and nonzero vacuum objects.
**Risk: medium for the product, high if confused with fusion.** Ordinary
bicategorical interchange only handles the even skeleton directly.

### A2. Separated-sector fusion — A

**Proposed statement.** Fuse the two sector families into an action of the
original superdatum. Retain a connected, nilpotent, exterior-deformed reservoir;
use an oppositely oriented probe whose even dot coordinates are invertible.
The fused dot and crossing formulas must satisfy the affine relations, and their
mates and dotted cups/caps must give the required inversion at every content.

**Even analogue:** `coverProduct`, `TwoRep.Furling` and its upward/mixed inversion
comparisons; the local matrix blueprint is `TwoRep/RouqCoproduct.lean`, including
`schur_const_eq`, `isIso_lift_of_schur`, `isIso_rouqMap_of_nonneg` and the negative
version. **Existing:** [SpectralCompensation.md](SpectralCompensation.md) gives
proposed zero/nonzero transport and vacuum calculations; local resolvent and
matrix lemmas exist, not the full fused action. **New:** coherent shuffle maps,
all-content Schur-complement identification and super inversion.
**Risk: highest.** Neither units in the upward algebra nor a dimension count
identifies the inverse of the categorical mate. Cross blocks need not vanish.
The variant with both sector spectra zero is the falsification target below.

### A3. Fixed-weight coverage — A, with C as consumer

**Proposed statement.** For every external weight μ and every finite observation
window, choose growing cutoffs and a nonzero cyclic test object of the fused
family at exactly μ, with the probe at its highest vacuum and upward words
remaining in the reservoir. All intermediate contents used in the window must
be included in the action comparison.

**Even analogue:** `GenericFields.rouqFamily`, `GenericFields.sum_level_difference`
and the vacuum of `GenericFields.unfurledEval`. **Existing:** weight arithmetic
and the candidate construction in SpectralCompensation; no general fixed-weight
observation is supplied by the algebraic quotient theorem. **New:** realization
of the dominant weights and the cyclic object, all parity classes, and the
coordinate comparison at those objects. **Risk: high.** With an odd-colour probe
`g_i(x)=(x²-a_i)^{M_i}`, the height is `2M_i-N_i`; odd heights require odd `N_i`.
Dominant cutoffs inside one root-lattice coset are not generally cofinal. Any
weight-lattice enlargement used to realize prescribed coordinates needs a
faithful presentation comparison, not merely coordinate arithmetic.

### C0. Bounded coefficient-extended affine separation — C

**Statement already available in Lean.** Each finite coefficient/PBW span
survives sufficiently large specified ELV relation quotients, without assuming
an SKM action faithful. In the uniform bound, `N > d + 2*choose(n,2)` suffices.

**Even analogue:** the affine corner comparison via `KLR.CyclotomicAction.theta`
and the cyclotomic coordinate separation used by `unfurledEval`.
**Existing:** `weighted_quotients_jointly_detect`,
`even_elv_quotients_jointly_detect`, `elv_quotient_injective_on_extendedAtMost`,
and the polynomial/exterior description of `SYM`.
**New:** an action-compatible consumer, and spectator-coordinate extraction if
the test uses added strands. **Risk: low algebraically, high at the interface.**
The theorem is about the specified quotient, not an arbitrary representation
with similar-looking relations. Small fixed cutoffs can kill crossing times
exterior products even when the exterior product alone survives.

### C1. Normalized bubbles in the fused action — C, with A supplying maps

**Proposed statement.** On the chosen cyclic objects, source-placed
`betaSYM` is a bounded invertible triangular substitution of independent
reservoir coefficients. For example, a sufficient law is
`C_i(t)=(1+u_i δ_i t) E_i(t²) P_i(t²)` at odd colours, where `u_i` is an even
unit and `P_i(0)=1` is fixed independently of all reservoir generators.
Use the actual normalization and indexing; this displayed law is a target,
not a claimed formula at arbitrary content.

**Even analogue:** `GenericFields.bubbleEval_indep`,
`GenericFields.klVacuumBubbleMap_independent`, and the comparison identifying
the categorical vacuum map with its scalar formula.
**Existing:** `oddBubble_zero_inverse_mate`,
`normalized_bubL_zero_inverse_mate`, and
`bubble_convolution_right_cancel_upto`; rank-one finite calculations in
[CoupledBubbleEvaluation.md](CoupledBubbleEvaluation.md).
**New:** multicolour normalized evaluation and bounded triangular recovery at
all test contents. **Risk: high.** A coherent gauge of adjunctions cannot create
new bubble coefficients. Do not infer the formula from independent scalar
variables that have not been identified with categorical bubbles.

### C2. Simultaneous upward and bubble coordinates — C

**Proposed statement.** Evaluation on a cyclic vector followed by a linear
coordinate map sends each finite source-placed coefficient/PBW vector to its
image in one sufficiently large ELV quotient, possibly after an explicitly
inverted finite triangular substitution. This is one joint identity, not two
independence assertions in unrelated models.

**Even analogue:** `TwoRep.RouqFamily.upEval`, `upEval_bubMap`,
`TwoRep.Furling.upCorner_toUEnd`, `theta_toUEnd_basis`, and
`GenericFields.unfurledEval` (whose basis-image equation combines both inputs).
**Existing:** `cyclicObservation`, `FiniteUpwardObservations`, canonical
matching/PBW comparison, and the source-placement conventions in
[UpwardSeparation.md](UpwardSeparation.md). **New:** construct the observation
without assuming upward injectivity; account for spectators if present.
**Risk: high.** The observation interface is strong enough to imply the desired
injectivity; restating it as an action premise does not discharge it.

### C3. Upward independence — C

**Statement already available conditionally in Lean.** C2 implies
`WeakMate.UpwardIndependence cs` for every permitted matching choice at every
weight. **Even analogue:** `linearIndependent_posB_of_unfurledEval`.
**Existing:** `upwardCoefficientMap_injective_of_observations`,
`upward_independence_of_finite_observations`.
**New:** supply C2, rather than a new version of the implication.
**Risk: low once C2 is proved.** Keep full `SYM`, including exterior products.

### B0. From upward to oriented independence — B

**Proposed remaining statement.** Establish contextual source and target
exchange descent, including the same-colour identity remainders, and combine
with sorted-boundary independence. **Even analogue:**
`KL3.Diagram.calculusNondeg_of_positive`.
**Existing:** `WeakMate.sorted_independence`,
`expansion_injective_choice_iff`, `SKM.distinct_target_exchange_descent`,
and distinct-source adapted families. **New:** remaining source descent and
same-colour descents, or a separately justified shorter oriented reduction.
**Risk: medium.** Principal mixed crossings alone lose the identity remainder;
source and target use different height conventions.

### B1. Field endpoint — B

**Proposed statement.** Under the scope above, every permitted matching expansion
is injective, hence `SKM.NondegeneracyConjecture`.
**Even analogue:** `calculusNondeg` and `GenericFields.calculusNondeg_charZero`.
**Existing:** `SKM.nondegeneracy_of_contextual_descent` and spanning of the
presented SKM Hom spaces. **New:** instantiate C3 and B0 with no residual
faithfulness or observation assumptions. **Risk: low as assembly, unresolved
as a theorem until A2 and C2 are established.**

### B2. Integral descent — B

**Proposed statement.** Build the integral matching basis over the universal
homogeneous-parameter ring (with the prescribed units), then identify
specialization with the presented SKM Hom spaces. Deduce the same basis over
all allowed ground rings. **Even analogue:** `IntegralSpanning.span_twoB`,
`IntegralScalars.homBaseChange`, `integralNondegBasis`,
`calculusNondeg_of_rational`. **Existing:** super spanning and abstract `SYM`
coefficient bases; the even descent proof is a blueprint.
**New:** super presentation base change and an integral independence argument
for general scalar parameters. **Risk: medium/high.** Rational independence
at one scalar specialization is not independence at every specialization;
base change need not preserve an arbitrary injection. A universal-ring basis
and the presentation comparison must be proved. Do not extend odd SKM claims
to characteristic two against the prescribed unit hypothesis.

## Where the odd coefficients live

**Proposed design.** Keep all odd colours' independent `δ_i` in the same
connected nilpotent reservoir coefficient superalgebra. In even ELV degree
`2m`, the relation `δ_i χ_(i,m)=0` forbids inverting the top even coefficient
while retaining `δ_i`. A fraction field of the whole deformation ring is
therefore not a coefficient detector. The coefficient algebra must retain
exterior directions; the ground field being a field does not make that
superalgebra a field.

For adjacent odd `i,j`, impose neither `δ_i δ_j=0` nor spectral separation
inside the reservoir. Their interaction at `Q_ij(0,0)=0` remains the original
connected super KLR interaction. C0 is precisely what can detect a bounded
crossing multiplied by `δ_i δ_j` there. C1 and C2 must transfer that joint
vector to the action; a tensor product of unrelated rank-one bubble tests
cannot do so.

Use zero/nonzero separation only **between the two weight sectors**, not
between odd colours inside the reservoir. The probe may be a specialization
of the ELV family with its own odd coefficients zero. All exterior coefficients
needed for detection then come from the reservoir. If instead both weight
sectors must retain independent nonzero odd coefficients, their common zero
spectra invalidate this separated-sector construction; a different coupling
would be required. The difference-weight Hom notation alone provides none.

## Is unfurling necessary?

**Proposed conclusion.** A full refined Cartan/Clifford unfurling theorem is
not a demonstrated prerequisite. Signed affine PBW separation and a proved
coefficient substitution could replace its two independence roles. However,
generic cyclotomic parameters alone do not construct the fused Hom action.
The currently specified route still needs spectral separation of its two
sectors, or a genuinely different construction handling their collision.

The economical remaining candidate is the original-superdatum zero/nonzero
coupling of SpectralCompensation: retain every interaction within each sector,
and prove its categorical fusion directly. No isolated rank-one replacement
of connected spectral components is justified. This is not permission to
assume the mixed inversion theorem; that theorem is the main open node.
Nor is it a claim that every conceivable proof must use nonzero spectra.

## What can actually be reused?

The ordinary categorical results with no odd morphisms in their hypotheses,
such as `blockResAdjunction` and finite biproduct/adjunction manipulations,
can be reused on the even skeleton of a parity-completed target. Linear
algebra, finite geometric inverses and the underlying weight arithmetic are
likewise reusable at their stated types.

`RouqFamily.homProduct` is **not** directly a super action constructor:
it is typed for ordinary Rouquier data and ordinary interchange. Its pattern
of pre/postcomposition can be ported, but odd transformations and their signs
must be added. Similarly `upEval` and `upEval_bubMap` evaluate the even KL
presentation, not SKM. They guide the super presentation comparison rather
than proving it by instantiation. `theta` concerns ordinary KLR; the signed
coefficient category must supply the super replacement.

`coverFamily`, `coverProduct`, spectral `Furling`, and the generic bubble
independence declarations are not callable substitutes for the odd nodes.
In particular the even cover requires no edges between labels over one
colour, whereas odd opposite squared spectra can interact. No such cover
is constructed here. `SYM` also has exterior generators, so algebraic
independence into an ordinary field is the wrong replacement for C1.

## Decisive test target

The riskiest proposed shortcut to A2 is **Hom fusion without spectral
separation**: two nilpotent factors, with the inherited blockwise dot maps,
are asserted to give the original-colour upward relations on their shuffle
blocks. Test its necessary rank-one odd nilHecke relation before attempting
bubbles or adjunctions.

Use the undeformed degree-two odd factors over `ℚ`, reducing every exterior
parameter to zero. On the cross-sector ordered tensor block take the regular
module of `Λ(x,y)`, so `X²=Y²=0`, `XY=-YX`, and `X≠Y`. The odd relation
`τX+Yτ=1` implies `τX²-Y²τ=X-Y`. Thus the proposed blockwise dots are a
particularly small potential obstruction; a test must solve for an arbitrary
linear `τ`, not assume a guessed crossing formula. Include the reversed
shuffle block, and allow all linear maps between them. Failure even without
imposing parity or the other nilHecke relations refutes this shortcut.

A second check should retain two independent exterior coefficients over the
nilpotent squared-coordinate ring `ℚ[z,w]/(z²,w²)`: for the admissible adjacent
odd datum with Cartan matrix `[[2,-2],[-2,2]]`, choose `Q_ij=z+w`. Test whether
localizing at this cross-sector denominator can preserve `δ_iδ_j`.
This is a denominator test, not a construction of that datum's full action.

### Executed exact instance and outcome

Reproducer: `python3 scripts/Nondegeneracy/nilpotent_hom_fusion.py`.
It uses exact rational elimination with no numerical tolerance. On the ordered
basis `1,x,y,xy`, let `X₀` and `Y₀` be left multiplication by `x` and `y`.
The two-shuffle test uses `X=diag(X₀,Y₀)`, `Y=diag(Y₀,X₀)` on dimension eight.
Its unknown `τ` is an arbitrary eight-by-eight matrix, including all maps
between the two blocks. It imposes only `τX+Yτ=I`, a necessary odd upward
relation. The actual output is:

```text
shuffle dimension=8; rank(T -> TX+YT)=32; augmented rank=33
NO crossing T satisfies TX+YT=I, even without parity restrictions
adjacent-odd coefficient algebra dimension=16; ranks(Q,Q^2,Q^3)=8,4,0; rank(delta_i delta_j)=4
Q^3=0: making Q invertible makes 1=0; the exterior product is lost
separated control Q=1+z has rank=16 and inverse 1-z; the exterior product survives
```

**Falsification: the blockwise zero/zero fusion shortcut is false.** The
proposed mathematical explanation is already the matrix identity above:
`X²=Y²=0` would force `X=Y`. The chosen `X` and `Y` are different even after
allowing all crossing matrices. Thus changing a guessed crossing formula,
or adding the other nilHecke relations, cannot repair these inherited dots.
This is not a counterexample to the odd nilHecke algebra: its polynomial
divided difference need not descend to the separate-factor ideal `(x²,y²)`.
A construction allowing extensions that alter the prescribed dot action is
outside the assertion tested here.

For the adjacent-odd denominator check the algebra is explicitly
`ℚ[z,w]/(z²,w²) ⊗ Λ(δ_i,δ_j)`; its basis is
`z^a w^b δ_i^e δ_j^f` with all four exponents in `{0,1}`. The exterior
product is nonzero, but `Q=z+w` has cube zero. Inverting it forces the whole
ring to vanish, not just a difficult crossing coefficient. The separated
control replaces this denominator by `1+z`, retaining both exterior variables
in the reservoir coefficient algebra. Its inverse is `1-z`; this verifies
only the elementary unit mechanism, not A2 or the bubble laws.

**Consequence for the programme (proposed).** An unqualified assertion that
two deformed nilpotent Hom sectors automatically give the original action is
not usable. Require the separated-sector A2, or replace it with an explicitly
new collision construction and prove its dot and crossing formulas. The
zero/nonzero candidate is not falsified by this test; neither is the
Nondegeneracy Conjecture. In particular these tests do not show that nonzero
spectra are logically necessary for every proof. They rule out the simple
nilpotent-sector reuse of the even Hom/fusion recipe.

The next decisive theorem is A2 with one exterior-deformed connected
reservoir and an exterior-free invertible probe, including its all-content
mixed inversion. In parallel, A0 needs odd cutoffs, and C1–C2 need one
explicit multicolour cyclic coordinate calculation with `δ_iδ_j` retained.
No new Lean declarations are proved by this document or its reproducer.
