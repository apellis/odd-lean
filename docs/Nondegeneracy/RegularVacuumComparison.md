# Regular coordinates from the two-factor vacuum

**Status: proposed mathematical derivation, not a Lean construction.** The
three coordinate laws follow by contraction of representable induction
modules, provided the concrete factor induction modules are the ones described
below. The current library does not yet identify the connected ELV factor
with those modules. This is a local factor-action comparison, not an assumed
`RegularVacuumIdentification` and not an identification of the whole fused
action. No new nondegeneracy theorem is claimed here.

The untransported factor identification is obstructed as explained in
`ELVVacuumGeneratorComparison.md`: the signed factor dot does not agree
with the coordinate dot while fixing the raw coefficient action, and this
note's probe-input/reservoir-output orientation is not the assignment in
`HomSectorTransport.md`. The representable calculation below retains its
stated hypotheses; it does not discharge either comparison. The detection
interface permits k-linear coordinate recovery with a constructed, possibly
transported, reservoir coefficient action.

## 1. The quotient and the projectives

Fix an external weight and one of the balanced cutoffs of
`ReservoirWeights`. Write C(s,t) for `ReservoirQuotient D Sc cutoff s t`.
It is the quotient of the coefficient-extended Hom by `ELVRelationSpan`,
with the signed composition of `CoefficientExtension`, not an unsigned
polynomial tensor product. This discussion uses the category obtained by
quotienting by that two-sided ideal. In particular the even-cutoff relations,
including `d_i χ_(i,m)=0`, remain imposed. No coefficient is inverted and no
flatness over an unrestricted exterior algebra is used.

Let P_t be the right representable module

    P_t(s) = C(s,t),       h · a = a ≫ h.

The source index is essential: the underlying space of P_t is the direct
sum over s of C(s,t), not just End(t). A word-changing affine operator need
not carry End(t) into End(t'). Projection to the s component will be the
coordinate map. For infinite colour sets this is a locally unital direct
sum; no sum of all word idempotents is required.

Evaluation at the identity gives the usual projective Hom coordinates:

    Hom(P_s,P_t) → C(s,t),       φ ↦ φ_s([1_s]).

The inverse sends h to postcomposition by h. Both inverse equations follow
from naturality on a ∈ C(r,s): φ_r(a) = a ≫ φ_s(1_s). This is stated in
unshifted enriched notation; the homogeneous components require the
corresponding parity shifts. In the existing graded right-module convention
`FiniteHomMatrix.GSMod.rowHomEquiv`, `rowModuleHomEquiv`, and their `_apply`
lemmas give the precise generator-evaluation form. They do not yet provide
an instance for the ELV quotient category.

## 2. Contract the defining induction tensor, not a guessed isomorphism

Suppose the reservoir upward induction is extension of scalars along the
strand-append functor J_i on the coefficient quotient. In right-module
notation its defining bimodule is

    B_i(s,u) = C(s,J_i u).

For a right module M, its value at s is the balanced sum of
`B_i(s,u) ⊗ M(u)` over u, with relation

    (b ≫ J_i(a)) ⊗ m = b ⊗ (a ≫ m).

Here a:u→v, b:s→J_i u and m:v→t when M=P_t. The contractions are explicit:

    κ_i,t : B_i ⊗_C P_t → P_(J_i t),
    κ_i,t(b ⊗ m) = b ≫ J_i(m),
    ι_i,t(h) = h ⊗ 1_t.

The displayed balancing relation and functoriality prove that κ is
well-defined. They also prove

    κ(ι(h)) = h,
    ι(κ(b ⊗ m)) = (b ≫ J_i(m)) ⊗ 1_t = b ⊗ m.

Thus no dimension count, projective-basis choice, mixed inverse matrix, or
assumed regular-word isomorphism is needed for this contraction. Compose
these maps along t, beginning with P_empty. All tensors and associators
must be the super balanced ones. The displayed order has no interchange of
homogeneous factors; reordering the tensor factors requires Koszul signs.
The contraction is even, so conjugation by it introduces no further sign.

There is a concrete missing prerequisite here: construct J_i on the exact
ELV quotient and identify the factor's induction bimodule, including its
left/right parity convention, with B_i. For a factor implemented by signed
right multiplication on left superbimodules, the identification has to
include its right-module/opposite transport. It cannot be declared to be
ordinary right multiplication merely because its underlying tensor is the
same. The existing ordinary-polynomial `CyclotomicAction/Vacuum.lean` only
computes the first-strand corner; it does not establish this ELV statement.

## 3. Why probe summands vanish

The Hom vacuum is an object (a functor), not a vector in a Hom between two
unrelated modules. Let the probe tower retain its formal content grading.
Let z be its content-zero regular projective. Define the vacuum functor V
by projecting the input to content zero and sending that summand to the
reservoir vacuum by extension of scalars. For the exterior-free probe the
height-zero ring is k; its rank-one generator goes to P_empty. In a common
coefficient-base implementation use extension over that base instead of
incorrectly tensoring two copies of the reservoir coefficients over k.

The reversed probe upward sector is precomposition with probe induction.
A positive probe word therefore makes V see a positive-content module.
The content-zero projection of that module is zero. Explicitly, for an
induction bimodule of content α_i,

    e_0 B_i^probe e_β = 0          for every β ∈ N[I].

Indeed that corner can be supported only at `0 = β + α_i`, impossible in
the free content monoid. Each of its elements is zero, so its balanced
tensor with any module is zero. This remains true with parity shifts.
This is a statement about tower corners, not the equation between weights;
it remains valid when different formal contents have equal root weight.

Expand a fused upward word using its sector direct sums. A term with any
probe letter evaluates to zero: reservoir postcomposition does not change
probe content, and all probe letters induce positive content in the input
of V. The all-reservoir term remains. Dot and crossing blocks incident to a
zero evaluated summand are zero linear maps. The reservoir-reservoir blocks
are the factor blocks. In particular no probe excitation is discarded by
an unproved assertion that a numerical weight space vanishes.

This argument requires the content-supported vacuum functor and the stated
precomposition orientation. `RouquierHom.homPre`, `homPost`, and
`homSectorInterchange` supply the abstract functors/associator, but neither
`CoupledFactors` nor `FusedCoupledAction` constructs this vacuum functor or
the tower support equation. Those are explicit construction obligations.

## 4. The three laws after contraction

Let κ_t be the iterated tensor contraction after deleting the zero probe
summands. For the resulting evaluated word space W(t), define

    coord(s,t)(v) = (κ_t(v))(s).

Choose the vacuum vector as the iterated identity tensors beginning with
1_empty. The contraction sends it to the vector supported at s=t with
entry 1_t. Consequently

    coord(t,t)(vacuum(t)) = [1_t].

For a homogeneous reservoir generator g:t→t', the induction transformation
is postcomposition on the final bimodule factor. On a pure tensor its
contraction is `(b ≫ J_i(m)) ≫ g`; associativity gives the same result by
first contracting and then postcomposing. Tensor balancing and linearity
extend the equality to all vectors. Dots and crossings therefore give

    coord(s,t')(act(alpha(f)) v)
      = reservoirPostcomp(sourceCoefficientHom 1 f)(coord(s,t)(v))

for arbitrary affine f, by composition and linearity, **once the factor's
dot/crossing maps have been compared with these coefficient-category
morphisms**. In a signed-left implementation this is the generator
comparison left open in §2, not a consequence of projectivity alone.

Define the reservoir coefficient operator by its coefficient-category
endomorphism `sourceCoefficientHom a (1_t)` on the same final factor.
The identical contraction calculation gives

    coord(s,t)(reservoir(a) v)
      = reservoirPostcomp(sourceCoefficientHom a (1_t))(coord(s,t)(v)).

Composition of these coefficient operators is an algebra action: in
category order the product is reversed, exactly as in `Module.End`.
The affine and coefficient calculations keep the signed Hom composition.
For homogeneous b and g, the specific rule already proved by
`coefficientHom_comp` is

    (a ⊗ f) ≫ (b ⊗ g) = (-1)^(|a||g|) (ba ⊗ (f ≫ g)).

Thus the affine action on an odd coefficient times an odd diagram has a
minus sign (`odd_coefficient_comp_odd`). An unsigned contraction would fail
this law. It is not legitimate to repair it by silently replacing the ELV
ideal by its image under a sign involution.

## 5. Exact dependency boundary

The argument reduces the coordinate task to the following concrete maps;
it does not introduce another structure assuming the three conclusions.

1. Content-indexed probe/reservoir factor categories, projectivity where
   required by their actions, and the extension-by-zero vacuum functor V.
   The probe corner equation above must hold in that tower, not just in a
   model with a similar highest weight.
2. The connected reservoir coefficient quotient is the exact ELV quotient;
   append descends, its defining induction tensor is B_i, and its dots and
   crossings are the signed postcomposition maps. The required local
   commuting square is κ_(t') ◦ T_g = postcomp(g) ◦ κ_t, checked on balanced
   generators, where T_g is the already defined factor transformation.
3. Fusion's upward generators have the stated sector decomposition and
   unchanged reservoir-reservoir blocks; the full presentation action and
   its restriction to the original weights are supplied by the action work.

The local contraction in §2 proves the square for the representable
bimodule maps by associativity. The missing part is identifying those maps
with the concrete ELV factor transformations, not choosing an arbitrary
linear map satisfying the square. No current declaration inspected here
discharges that identification for the full connected deformation.

Once these constructions are formalized, `reservoirPostcomp_mk`,
`reservoirPostcomp_comp` and `reservoirPostcomp_generator` are the exact
quotient lemmas for the three laws, and `FusedVacuumWords.evaluation`
consumes them. `GSMod.rowModuleHomEquiv` provides canonical projective Hom
coordinates, not an independent faithfulness assumption.

The normalized bubble comparison is separate. Nothing above identifies
`W.bubbles` with the reservoir coefficient action: `CoupledSectorBubble`
still needs `fusedBlock`, `probe`, `reservoirValue` and `normalize`. In
particular the missing fusion inverse block is not used to define κ.
Balanced cutoff reachability and regular-window injectivity were already
proved in `ReservoirWeights` and `ReservoirCoverage`; neither is reopened
or substituted for this remaining module comparison.
