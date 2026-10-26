# Swapped Hom assembly and finite-colour passage

**Status: proposed written partial assembly, not a Lean theorem.** The
same-colour augmented inverse and the upward component calculations do not,
by themselves, finish the action. The remaining distinct-colour mate maps
are specified in §5. In particular this note does **not** assert that the
full swapped action has been constructed. It proves the contentwise
assembly, identifies the surviving vacuum blocks without a
`VacuumIdentification` assumption, and proves a finite-presentation passage
which avoids constructing an infinite-colour Hom action.

The presentation being tested is Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, Definition 1.5, (1.7)–(1.14), with the
parameters of (1.2)–(1.4). Its exact library version is
`OddMath/SKM/Presentation.lean`, `Rel` and `relation`. The source allows
infinite colour sets and a supercommutative ground ring. Here the factor
inputs require symmetrizability, homogeneous parameters, and a purely even
field k with 2 invertible. These are restrictions of this construction,
not extra conditions in the cited definition. Both even and odd colours,
and connected mixed data, are retained.

## 1. Fixed factors and literal weight categories

Fix a finite colour set J with the restricted Cartan matrix, parity,
symmetrizers and parameters. Do not replace the original weight group X by
a quotient or by its coroot coordinates. For the factor construction use
the pairing extension and the cutoff choice of `SwappedHomInversion.md`:
apply `ProbeReachability.md` to -μ, obtaining

    ΛP - ΛR = (μ,0).

Let T be the specialized unit-dot probe of `InvertibleDotProbe.md`, and W
the reservoir of `DeformedReservoirBound.md`. Fix its coefficient truncation
once for the entire tower, not separately at each content. The untruncated
factor input is `DeformedActionAssembly.md`, `DeformedMixedBraid.md` and
`DeformedGradedAction.md`. Its algebra parameters are `parameterTwist Sc`;
its action parameters are the original Sc. Denote the probe and reservoir
module categories at formal contents b,c by T_b,W_c, and their weights by
-ΛP+α(b), -ΛR+α(c).

Use the two-supercategory of k-linear supercategories, superfunctors and
supernatural transformations, with parity completion. One can choose a
larger universe for these Hom categories. Put

    H_(b,c) = SFun_k(T_b,W_c),
    wt(b,c) = ΛP-ΛR-α(b)+α(c),
    C_λ = product_(b,c nonnegative, wt(b,c)=λ) H_(b,c).       (A1)

Objects are arbitrary families, not finite-support families. A homogeneous
map of parity r is a family all of whose entries have parity r; arbitrary
maps are the sum of their two parity parts. This is the super-enriched
product, with finite biproducts taken componentwise. Empty fibres have the
zero category. Absent contents also mean zero categories and zero functors.
Formal content, not its image under α, controls every predecessor operation.
Thus (A1) is meaningful even if positive contents have root image zero.

The interpretation on X uses C_(λ,0). More generally all objects of the
pairing extension are included, and the original presentation maps into
this one by λ↦(λ,0), with α_i↦(α_i,0). Heights at these images remain the
original heights. There is no claim that every such category is nonzero.

At an input component (b,c), the raising summands are

    A_i = pre(E_i^T): H_(b,c) -> H_(b-i,c),
    B_i = S_(p_i P(b)) post(E_i^W): H_(b,c) -> H_(b,c+i),    (A2)

where P(b)=Σ_j p_j b_j in Z/2. These are precisely
`homContentPreE` and `homContentPostE`, with T on the precomposition side.
For example the pre edge in (A2) is T_(b-i)→T_b, not T_b→T_(b+i).
Both changes raise wt by α_i.

Their right adjoints, on the reverse edges, are

    R_A = S_σ pre(F_i^T),    σ=p_i(h_i(-ΛP+α(b-i))+1),
    R_B = post(F_i^W) S_(p_i P(b)).                         (A3)

The first uses the normalized *left* adjunction of T and the second the
right adjunction of W. Use `HomSectorTransport.md` (4), (6), not a common
unsigned tensor adjunction. In particular, writing z_t:S_t→Id,

    S_t(f);z_t = (-1)^(t|f|) z_t;f,
    ξ_t = (-1)^t z_t(S_t(-));z_t,
    β_(L,t) = z_t(L(-));L(z_t^-1).                          (A4)

A semicolon means chronological composition. In the pre component, if
u,v are the raw left unit and normalized left counit, the even unit and
counit are u;z_σ^-1 and (-1)^σ L(z_σ);v. The normalization is
c(k)=(-1)^(p_i(k+1))e(k), with e(k)=1 for k<0 and e(k)=(-1)^p_i
for k≥0, at the bottom weight of the appropriate edge. In the post
component they are u;N(ξ_κ^-1) and S_κ(v(S_κ(-)));ξ_κ.
All edge labels, rather than only the central weight, enter these formulas.

Define E_i on (A1) by summing the two incoming components at each output,
and F_i by the two reverse edges (A3). Each output receives at most two
summands. Consequently both functors exist on the product, without an
infinite coproduct in an individual H_(b,c). The unit has the diagonal
sector units and zero off-sector entries; the counit has the diagonal
sector counits and zero off-sector entries. On each E or F summand the
triangle reduces to its sector triangle. Orthogonal biproduct projections
kill the other terms. This proves the global even right adjunction.
It is not necessary to bound the size of a weight fibre.

## 2. Prescribed upward maps and local finiteness

Dots are the inherited pre dot and the shifted post dot, with the action
of S on homogeneous maps retained. Precomposition reverses the two factor
slots. Its equal-colour crossing is -(-1)^p times the inherited factor
crossing. Distinct-colour pre crossings are the inherited reversed-label
crossings, not their inverses. The post same-sector crossings are the
specified β/ξ word transports of the factor crossings. At unequal colours
r,s the even comparison is

    S_(p_s P(b))(β_(M_s,p_r P(b))^-1);c_(p_s P(b),p_r P(b)),

where c_(1,1)=ξ. Removing it by a bare double z changes its sign and is not
an alternative definition.

For the mixed sector, let J_ij:B_j A_i→A_i B_j be

    L_i(z_t(M_j(-)));j_ij;z_(t+p_i p_j)(M_j L_i(-))^-1,
    t=p_j P(b),                                           (A5)

where j is the inverse associator. Its degree is p_i p_j. For i≠j the
unit direction A_i B_j→B_j A_i is J_ij^-1; the reverse is Q_ij J_ij,
with Q evaluated in the target dot coordinates. For equal colour, in
row/column order AB,BA the crossing is exactly

    [ -q a             J           ]
    [ -J^-1 a²         q J^-1 a J   ],   q=(-1)^p,          (A6)
    a=(x-y)^-1                       (p=0),
    a=(x-y)(x²-y²)^-1                (p=1),

where x is the pre probe dot and y the post reservoir dot. In particular
neither swapping entry is changed when the nilpotent side is exchanged.

At each fixed reservoir content the relevant dot is nilpotent, uniformly
on all reservoir modules, because its multiplier belongs to a finite
integer-graded algebra and has positive degree. This uses the fixed tower
truncation. Thus the denominators in (A6) have finite geometric inverses
in powers of y, since x is a unit. The odd squares commute. The same proof
applies to Q(x,y): its y-free term is a unit times a permitted power of x,
and the rest is a nilpotent commuting perturbation. No Q of two reservoir
dots or crossing of two equal-colour factor strands is inverted.

These are identities of natural transformations, not merely pointwise
inverses depending on a test module. They therefore assemble over (A1).
The length of a terminating series may vary with c. Parity is fixed, so
this variation does not violate the homogeneous-product convention.
A finite word of length n has at most 2^n sector paths; every output has
only finitely many predecessors. Each rational entry and each same-colour
inverse has finite sector support. Composing two such matrices still has
finite sums in every entry. These observations prove the local-finiteness
needed for all the proposed generator maps, including the inverse of
`SwappedHomInversion.md`; they assert no uniform nilpotence over all contents.

## 3. Exact relation dictionary

The following is a dictionary to `Presentation.relation`, not merely to
`RouquierFamily`. In particular the latter does not contain the mixed
KLR or distinct-colour inverse relations.

| Source relation | Assigned map and proof or remaining obligation |
|---|---|
| (1.7), `quadEq` | Same-sector factor square; mixed square of (A6), the four cancellations of `CrossingNormalization.md` (4). |
| (1.7), `quadZero`, `quadNe` | Same-sector factor square after slot reversal/βξ transport; mixed products of J^-1 and QJ. Separate exponent support makes Q transport unsigned. For disconnected colours Q is the single constant t_ij. |
| (1.8), `slideLEq`, `slideREq` | Pre crossing coefficient -q gives the two constants +1; post transport preserves the factor slides; the four mixed entries are the slides of `CrossingNormalization.md` (2)–(3). |
| (1.8), `slideL`, `slideR` | Reversed factor slides, transported post slides, and the two signed dot intertwinings of (A5). |
| (1.9), `braid`, iii | `ThreeStrandSectorBraid.md` with `PairedHomInterchange.md`; same-sector factor braid. |
| (1.9), `braid`, iij/ijj/distinct ijk | All sector path sums of `MixedColourRemainingBraid.md` (9)–(16), including the symmetric-Q divided-difference cancellation. |
| (1.9), `braidEq` | `MixedColourSectorBraid.md` and `MixedColourBlockCompletion.md`, with `ExecutionBraidNormalization.md` (2); all-one-sector transport as below. |
| (1.10), `zigE`, `zigF` | The diagonal finite-sum adjunction in §1. |
| (1.11), `sigmaL` | The *defined* unit–crossing–counit word, not an independently selected splitting map; project it by (A8) below. |
| (1.12), `invNe₁`, `invNe₂` | **Still requires the distinct-colour partial-mate inverses in §5.** Upward Q invertibility is not this relation. |
| (1.13), `invP₁`–`invP₅` | Entire positive augmented map and inverse of `SwappedHomInversion.md` (13), (16), (17), extracting components as in §4. |
| (1.14), `invM₁`–`invM₅` | Entire negative augmented map and inverse there, (14), (16), (17). |
| `dcupZero`, `dcapZero` | Assign zero outside their indicated finite height windows. |

For completeness the all-pre transport does not require a new parameter
twist. Reversing two slots exchanges their dots; in a Q monomial each
exponent times its own colour parity is zero, so reordering the supported
powers has no sign. The distinct crossing squares remain Q. Reversing
three slots exchanges the two braid paths. In a corrected iji path there
is one equal-colour crossing, contributing -q_i. Reversing the ordered
correction contributes q_i, as the relabeling l↦r-1-l in
`ExecutionBraidNormalization.md` shows. Their product is -1, exactly the
path exchange. In zero-correction braids both paths have the same scalar.
For postcomposition the coherent even word comparisons simply transport
the factor relation. Their explicit two-strand representatives are the
β/ξ comparisons above; the paired-J calculations check the mixed paths.
These arguments keep the original Sc, including both leading coefficients.

For the corrected displayed relation, the coefficient of the ordered
term with l dots on the right i, s on j, r-1-l on the left i is
(-1)^(p_i(p_j+l)) Q_ij[r,s]. This is the chronological layer order of
`relation (.braidEq i j λ hij)`. The execution difference is its reversed
negative, not the displayed positive expression on renamed variables.
All distant commutations are super interchange in the target; each local
entry is supernatural of its declared parity. External prefixes change
b,c, and external suffixes apply the same superfunctors. No parity is
assigned to an object of H_(b,c).

## 4. Same-colour inverse generators, including height zero

Let H=h_i(λ), S=E_iF_i, T=F_iE_i, s:S→T the literal mate, v_n:S→1 the
literal dotted caps and u_n:1→T the literal dotted cups. Use the homogeneous
parity lifts of `SwappedHomInversion.md`, with all of its α_n, β_n, γ(k)
and identity windows. Its inverse is a proposed written input, not a
consequence of the kernel-checked principal word alone.

At H≥0 let [r,a] be the inverse of [s;v]:S→T⊕1^H. At H≤0 let [r;b]
be the inverse of [s,u]:S⊕1^(-H)→T. Undo the prescribed parity lifts and
set

    lcross(i,i)=-r,       dcup(i,n)=a_n (0≤n<H),
    dcap(i,n)=b_n (0≤n<-H).                               (A7)

For H≥0 the two inverse products read r s+Σ a_n v_n=1_S,
s r=1_T, v_m r=0, s a_n=0, v_m a_n=δ_mn in functional order.
Substitution of -r gives respectively `invP₁` through `invP₅`, with the
signs in the library. For H≤0 they read s r+Σ u_n b_n=1_T,
r s=1_S, r u_m=0, b_n s=0, b_n u_m=δ_nm. These give `invM₁` through
`invM₅`. These are products of the *whole* matrices, not principal-block
inverse assertions. At H=0 both define -s^-1 and agree by uniqueness.
The nonempty residual windows at equal nonzero factor heights must still
be inverted; `SwappedHomInversion.md` §5 treats these, retaining γ(0)=q.
The scalar zero-height rule does not discard those residuals.

## 5. First remaining map: distinct-colour partial mates

The outstanding relation is not another upward braid. Fix i≠j and take
L_a,L_b,L_c,L_d to be the appropriate A/B raising edges. For an upward
entry t:L_c L_d→L_a L_b in execution order, the projection of the literal
mate is

    M(t) = (R_a L_c ◁ η_d);
           (R_a ◁ t ▷ R_d);
           (ε_a ▷ L_b R_d)
         : R_a L_c -> L_b R_d.                            (A8)

Every unit and counit is the specific one in §1 at its own edge. Sector
projections are even and show that (A8) is the whole corresponding entry:
there are no additional summands hidden in the projection. Distinct-colour
upward crossings exchange sector labels, so the four entries are a block
permutation, not a central two-by-two Schur block. Their inputs are the
pre/pre crossing, the post/post crossing, J^-1, and QJ, respectively.

The post/post entry is the transported factor distinct-colour mate and
has its transported factor inverse. For the pre/pre entry one needs the
normalized-left analogue, with its explicit shift removals. In particular
one must evaluate (A8) with

    t=C^A_ij (the reversed-label inherited crossing),
    η=η_A, ε=ε_A, R=S_σ pre(F^T),                         (A9)

and give a two-sided inverse for this particular map. The all-height
same-colour result does not apply to (A9): there is no single-colour
principal-window formula for its two different colours. Neither the
ordinary right factor inverse nor the scalar γ(k) identifies (A9)
without a distinct-colour normalized-left mate calculation.

The other two entries require the same explicit check for M(J^-1) and
M(QJ). Their expected raw coordinates are an interchange of pre(F_i)
and post(E_j), with the latter multiplied by a polynomial in a unit probe
dot and a nilpotent transposed reservoir dot. This expectation is **not**
used as a proved identity here. In particular the transpose of an odd
power has factor (-1)^(p n(n-1)/2), and two bare z removals contribute the
minus in (A4). A finite inverse to the upward polynomial Q does not prove
that its partial mate equals that polynomial after these operations.
Taking an arbitrary partial mate does not preserve invertibility.

Thus (A9) is a precise first unproved map for this assembly; the two mixed
entries also need evaluation. The full factor actions provide derived
mixed relations that may discharge it, but a calculation matching their
left cups/caps, region-dependent normalizations and the prescribed maps
is still needed. No new action, parameter, or replacement crossing is
licensed by this observation. Until these entries have two-sided inverses,
there is no map out of the full presented SKM category here, regardless of
the completeness of the same-colour augmented inverse.

## 6. Surviving vacuum blocks are forced by the construction

The following conclusion needs only the specified upward maps, so does
not depend on closing §5. On T_0-supermodules let

    V(M)=Abar ⊗_k M,

as a functor to W_0, and put all other components of the object of C_(μ,0)
equal to zero. Here Abar is the fixed reservoir coefficient quotient and
T_0=k. The map on a homogeneous input u of parity r is
 a⊗m↦(-1)^(r|a|)a⊗u(m).

An A step decreases nonnegative probe content. Starting at b=0 it therefore
lands in the absent predecessor and is zero. A B step leaves b unchanged.
Consequently every upward sector path containing A is zero, including
ones preceded by arbitrarily many B steps. On the only surviving path
b=0 throughout, so κ_i=p_i P(0)=0, all z/β/ξ comparisons there are identity,
and every B functor, dot and crossing is literally reservoir postcomposition.
Mixed entries cannot connect this all-B path to another sector count.

For a displayed source word t, put ν=reverse(t). Multiplication of the
induction kernels gives

    V_t(M)=(B_(content(t)) e_ν) ⊗_k M,
    b⊗c ↦ b append_i(c),      z ↦ z⊗e_ν.                 (A10)

Balancing and the right idempotent give both inverse identities. No
flatness assertion is involved. The kernel dot is R_x(z)=(-1)^(|x||z|)zx;
the crossing is R_τ for distinct colours and -R_τ for equal colours.
These are exactly the surviving maps, because the all-B restriction
just proved contains no rational mixed term and no parity-removal factor.
For chronological multipliers b_1,...,b_l their value on z is

    (-1)^((Σ|b_j|)|z|+Σ_(j<k)|b_j||b_k|) z b_1...b_l.    (A11)

A signed left-module map φ:B e_ν(s)→B e_ν(t) of parity r is recovered from
b=φ(e_ν(s)) by φ(z)=(-1)^(r|z|)zb. Therefore its corner is
 e_ν(s) B e_ν(t), and evaluation of φ_b;φ_c is (-1)^(|b||c|)bc.
Evaluation of transformations V_s→V_t at k has the same inverse: extend
φ by φ⊗id; naturality against the maps k→M given by homogeneous vectors
forces that extension. This proves the corner identification, not merely
an equality of dimensions. Coefficients act by L_a=R_a, since a is
supercentral.

Equations (A10)–(A11) and this evaluation are precisely the word, signed
corner and generator formulas used in `SwappedVacuumCoordinates.md`
§§2–3 and (7). They are now consequences of the explicit upward assignment,
not a separate `VacuumIdentification` premise. Once §5 is proved, the
same formulas evaluate the corresponding morphisms of the full quotient.
The affine inverse-ideal and bounded extraction arguments of that note
can then be applied on their admissible windows. Normalized source bubble
values and the bounded-observation consumer remain separate; neither is
proved by this support calculation.

## 7. Finite-colour compatibility without a base-change Hom claim

Here is the cheaper passage to arbitrary I. It uses a finite action for
each required finite support, not one global Hom action. There are two
different compatibility statements to distinguish.

First fix finite J⊆K and compatible cutoff data on K. Let A_J,A_K be the
reservoir coefficient algebras, with identical powers used to truncate
shared generators. Their presentations give

    A_K = A_J tensor^s A_(K\J),
    B^K_β = A_K tensor_(A_J) B^J_β       (supp β⊆J).     (A12)

The same statement without truncation holds. Each extra-colour algebra
has augmentation sending its positive generators to zero. Thus inclusion
A_J→A_K has a left inverse and does not kill independent coefficients.
The ELV relations involve only their own colour, including δ_i χ_(i,m)=0
at positive even odd-colour cutoff. They introduce no cross-colour quotient.
For the probe the specialized coefficient algebra is k on both sides.

To prove (A12), present both sides by the coefficients, word idempotents,
dots and crossings at content β. Every word uses only J, so all affine
and first-position relations are the same. The two namesake generator
maps are inverse. For i∈J and supp(β+i)⊆J this identification commutes
with append_i. Consequently it identifies the induction kernels, the
restriction corners, and their balanced tensor products. On pure tensors
the comparison is the multiplication-of-coefficients map, with the super
balancing sign; its inverse inserts 1. Associativity of multiplication
makes it coherent for successive append operations. Units, counits, dots
and crossings are the same insertion/multiplication maps. The prescribed
inverse matrices commute with this identification by uniqueness of a
two-sided inverse. This is an exact cross-support comparison of the factor
functors on extended modules, not a dimension or flatness argument.

It does **not** identify A_K⊗Hom(M,N) with Hom(A_K⊗M,A_K⊗N) for arbitrary
modules or superfunctors. To compare a finite diagram within a K-action,
restrict to the content blocks with support in J but keep coefficients
A_K. Then the smaller coefficient-extended tower is literally the same
presented tower as those K blocks. Its Hom categories are taken between
these same categories; pre/post functors, parity shifts, and all rational
maps agree. Bounds may be chosen differently, but finite inverse formulas
agree by uniqueness. There is no base change of an arbitrary Hom space in
this comparison. Contents using K\J give other components of the K-action;
restriction to the J-supported components is preserved by J-labelled edges.

Second, the presentation itself has a directed finite-support property.
Keep the **whole X** and all its weights when restricting colour labels to
J. The restricted datum uses h_i:X→Z and α_i∈X unchanged, not a smaller
root-span weight group. Inclusion J⊆K sends every generator to its namesake.
The height windows of every inverse relation are unchanged. Thus it sends
each defining relation and each of its contexts to the same relation in K.
It defines a functor on presented categories. Faithfulness of this functor
is not assumed.

## 8. Finite derivations suffice for arbitrary-colour detection

**Finite-witness lemma (written).** If a finite linear combination d of
diagrams is zero in the I-colour presentation, there is a finite J⊆I
containing the colours of d and a derivation that d is zero using only
J-coloured diagrams, while retaining the original weights in X.

Proof. The linear contextual ideal is generated by finite sums of scalar
multiples of contextual instances of defining relations and super
interchange. Its generation is finitary: membership is a finite expression
using addition, scalar multiplication, composition and whiskering. Equally,
an inductive congruence proof uses a finite proof tree. Take the union of
the colours of every generator diagram and every left/right context in
that expression or tree. Each word, layer list and defining relation is
finite; inverse windows have finite integer length. Hence the union J is
finite. The same expression is valid in the J presentation, since α,h,
parameters and all weight labels have been retained. This includes colours
introduced and later removed by cups or caps, not only colours visible on
the boundary of d. No projection deleting those cups is used. ∎

For a proposed nonzero coefficient-affine combination f, also include the
finitely many colours appearing in its coefficient monomials. Coefficient
inclusion into any larger finite support is split by augmentation of the
new polynomial and exterior generators. The affine diagram part at fixed
content has the identical generator/relations presentation, since dots
and crossings never create colours. Thus f remains nonzero on enlarging
support; in coefficient coordinates this is the split coefficient map
tensored with the unchanged affine module, not an assumed injection of
full SKM Hom spaces.

Suppose, conditionally, that every finite restricted datum has the required
bounded detecting observations at every original λ, on the same action
and with normalized bubbles. If the image of f were zero in the I-colour
SKM category, apply the finite-witness lemma to that zero equality, then
enlarge its finite set to include f's coefficients. Apply the detecting
observation for this enlarged finite datum, with cutoff and homogeneous
coefficient truncation sufficiently large for f. It annihilates the finite
derivation but does not annihilate f, a contradiction. This proves the
arbitrary-colour implication from the finite-colour detection assertion.
It does not assume that an action for the original smaller support extends
to I, or that a chosen test object is compatible under all enlargements.

The auxiliary pairing extension can be made after choosing the finite
witness support. Its first coordinate is still the entire X. Mapping
λ to (λ,0) preserves every region and relation in that finite derivation.
Cofinal cutoffs are selected for all colours in this finite witness, not
just for the upward boundary word. This is why outside-colour cup/cap
contexts cause no exception.

All reservoir bounds used in this argument are those for one fixed finite
alphabet and one coefficient quotient chosen for its entire tower.
A global quotient that truncates only the initially active colours is not
being used. No claim of finite dimension for an infinite-colour coefficient
algebra, and no uniform joint nilpotence from such a claim, is needed.
One must not change the coefficient algebra with β and then assume append
compatibility: (A12) only proves it for a fixed common presentation.

## 9. Scope of the remaining work

The target of Definition 1.5 is a parity-superaction. The probe
specialization is not integer graded. `ReservoirVacuumEvaluation` and
`FusedFixedWeightFamily` in `ReservoirVacuumDetection.lean` demand linear
actions and bounded affine-coordinate laws, not a standard integer-graded
fused action. The independent reservoir grading suffices for the finite
series above and for the nilpotent closed-coefficient ideal used in
`SwappedHomInversion.md`. Requiring a full integer-graded fusion would be
a stronger package and is not inferred here.

The first missing action maps are (A9) and the two mixed instances of
(A8), with two-sided inverse identities and their prescribed shifts. Once
these are proved, the table in §3 and the local-finiteness argument give
the full finite-colour presentation action. They cannot be replaced by
an assumption called mixed inversion in a purported completed assembly.
The vacuum restriction of that action is already fixed by §6.

Separately required for detection are the normalized bubble formulas at
all height signs and a consumer using admissible bounded observations
(or a proved extension of the existing total window interface). The finite
witness argument removes the necessity of an infinite-colour graded tower;
it does not remove these finite-colour obligations. No nondegeneracy
conclusion, Lean implementation, raw coefficient-preserving global quotient
isomorphism, or total zero-window extension is asserted.
