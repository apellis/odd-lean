# Ground-ring descent with dependent roots and normalization units

**Status: proposed mathematical deduction, not a Lean theorem.** This note
supports Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1 and the Nondegeneracy Conjecture immediately following it.
It proves the commutative-algebra reduction on paper and supplies a universal
parameter construction, including the original weight group and supplied
normalizations. Its nondegeneracy input is the written field candidate
[SwappedNondegeneracy](SwappedNondegeneracy.md) at
`22c0d052a31eb1607f84f139e7490d34fbcdbedb`, not an established Lean theorem.
The candidate is unchanged. The presentation scalar-change interfaces below
are mathematical constructions still to be implemented for SKM.

## 1. Exact conclusion and source boundary

Fix the datum D, its arbitrary colour set I, original additive weight group X,
roots alpha_i, coroots h_i, parity p_i, and a positive integral symmetrizer.
Let R be an ordinary commutative ring with 2 invertible, regarded as purely
even. Choose all the admissible homogeneous parameters Sc of the frozen
candidate, including endpoint units, the single disconnected constant, and
separate even-exponent support at each odd colour. Supply cs : CScalars Sc,
with c_(lambda+alpha_j;i) = t_ij c_(lambda;i).

**Deduction from the field candidate.** Suppose the frozen field statement
holds for the fixed combinatorial datum D with every admissible homogeneous
parameter choice and supplied CScalars over every characteristic-zero field
(it suffices to use algebraically closed such fields). Then
`NondegeneracyConjecture cs` holds for the specified (R,Sc,cs). No d_i is
inverted in R. There is no domain, reducedness, flatness, Noetherian,
finite-colour, or independence-of-roots hypothesis on the target.
No new hypothesis is imposed on Sc or on cs. The zero ring is allowed.

This is a theorem implication proved below, not a proof that the field
candidate's unresolved action constructions exist. Completing those
constructions remains necessary for the nondegeneracy endpoint.

Source distinctions matter:

* BE2 Theorem 8.1 is spanning over the source's ground superring, not the
  independence conjecture. BE2 chooses independent simple roots in its
  introductory realization. The original possibly dependent X here is the
  explicit scope of the repository's frozen candidate, not a claim about
  BE2's printed realization. Symmetrizability and parameter homogeneity are
  also restrictions of this candidate, not hypotheses of BE2 Theorem 8.1.
* [Webster v4](https://arxiv.org/html/1603.06311v4), Theorem A and Theorem 3.13,
  explicitly invert the symmetrizers. Section 6.3 is the proof section, not
  another theorem numbered 6.3. Its universal ring starts over
  Z[1/(product d_i)] and its argument considers residue and fraction fields.
  We do not quote the printed theorem as an unlocalized result. We use only
  characteristic-zero fields in the new deduction, so no additional
  symmetrizer localization of the target follows from that comparison.
* The existing `Categorification/Diagrams/KL3/IntegralDescent.lean`,
  `IntegralBaseChange.lean` and `IntegralFamily.lean` implement the correct
  integral-basis-then-base-change strategy for the fixed KL presentation.
  In particular `integralNondegBasis` uses the actual presentation comparison.
  This is not an existing theorem for variable homogeneous Q or super data.

## 2. Why a universal domain is the wrong requirement

Here is a compatible example with X = Z and dependent roots, not torsion in X:

    alpha_0 = 2, alpha_1 = -1,
    h_0(lambda) = lambda, h_1(lambda) = -2 lambda,
    Cartan matrix = [[2,-1],[-4,2]], symmetrizers = (4,1).

Colour 0 can be even and colour 1 odd (or both can be even). The odd row has
only even Cartan entries. Set s = 0. Write t_01 = u, t_10 = 1 and t_ii = 1.
The normalization laws for colour 0 imply

    c_(lambda+2;0) = c_(lambda;0),
    c_(lambda-1;0) = u c_(lambda;0), hence u^2 = 1.

Conversely over B = Z[1/2][u,u^-1]/(u^2-1), the units
c_(lambda;0) = u^(-lambda), c_(lambda;1) = 1 satisfy every shift law.
The mixed polynomial is Q_01(x,y) = u x + y^4, with its reversed partner;
it is homogeneous of weighted degree 8 for dot degrees (8,2), and the
odd-colour exponent is even. There are no interior coefficient terms.

Both u-1 and u+1 are nonzero in B: specialize respectively at u=-1 and u=1.
Their product is zero. Any universal coefficient ring for these data maps
onto B and contains a unit u with u^2=1 and with both factors nonzero
(the same specializations show this). Thus that universal ring is not a
domain. In particular, a domain carrying the normalization laws cannot
specialize to R = Q x Q with u=(1,-1): in a domain u is either 1 or -1,
whereas that target unit is neither. Choosing one irreducible component
silently loses valid parameters. This example refutes the domain premise,
not nondegeneracy.

Using a free-root realization instead can remove these relations upstairs,
but moving back requires a presentation comparison, including the inverse
matrix generators and original normalized bubbles. A restriction functor
alone does not imply faithfulness. There is no need to introduce that
additional obligation: retain X throughout the construction below.

## 3. The universal ring including every supplied CScalar

Put Z2 = Z[1/2]. Let G be the abelian group with generators

    T_ij              for all i,j in I,
    C_(lambda;i)      for all lambda in X and i in I,

and additive relations

    T_ii = 0,
    T_ij = T_ji                         if d_ij = 0,
    C_(lambda+alpha_j;i) - C_(lambda;i) = T_ij.

No saturation of this relation subgroup is taken. Its torsion records
necessary root/normalization constraints and must not be discarded.
A homomorphism G -> R^units is exactly a compatible collection of the
units t and c. This assertion follows directly from the presentation of
an abelian group, without choosing representatives of X modulo the root
lattice. In particular all consequences of root dependencies are retained.

Next form the set V of allowed coefficient slots modulo
(i,j,p,q) ~ (j,i,q,p). A slot is forced zero when p p_i = 1 or q p_j = 1
in Z/2. In the used rectangle 0<p<d_ij, 0<q<d_ji, also force it zero unless

    p d_ji + q d_ij = d_ij d_ji.

The allowed/zero condition is invariant under the involution. These are
exactly symmetry and zero conditions, not equations between polynomials
in the remaining coefficients. For an exact lift of the repository's
`Scalars` structure, include allowed slots outside the used rectangles too:
`Scalars.s` is defined at all natural p,q, and `Scalars.Homogeneous` only
constrains the used rectangles. Unused values can instead be omitted only
after proving the presentation and expansion ignore them. We include them.

Define the ordinary, purely even commutative ring

    A = Z2[G][z_v : v in V].                                      (1)

In group-algebra notation [g], set t_ij = [T_ij], c_(lambda;i) = [C_(lambda;i)],
and s_ij^pq equal to z_[i,j,p,q] or zero as just specified. These define
Sc_A and cs_A on exactly D and X. Homogeneity and separate odd support
hold by construction. The connected endpoint coefficients are the group
units t_ij and t_ji; at disconnected colours use the single t_ij, not a
sum of two endpoints. The symmetry of the latter is a relation in G.

For every input (R,Sc,cs) in §1 there is a ring map A -> R sending these
parameters to the supplied ones. Map the group generators to the supplied
units, and the polynomial variables to the corresponding coefficients.
The defining equations are precisely the supplied axioms. This proves
universality, including arbitrary unused slots, arbitrary I and X, zero
divisors in R, and all normalization values simultaneously.

The exterior bubble generators do NOT enter G or A. They belong to the
coefficient algebra SYM over A (§5), not to the purely even parameter ring.
Putting them into A would introduce nilpotents and invalidate §4.

## 4. Enough characteristic-zero fields without a domain quotient

Here is the algebraic replacement for taking Frac(A).

**Lemma.** For any abelian group G and any set V, the ring (1) embeds in a
product of characteristic-zero fields, and also in a product of their
algebraic closures.

**Proof.** As a Z2-module, A is free on pairs consisting of a group element
and a polynomial monomial. Hence A -> A_Q = Q[G][z_v] is injective. We show
A_Q is reduced. Every element belongs to Q[H][z_w : w in W] for a finitely
generated subgroup H of G and a finite W. These subrings inject into A_Q
by their group/monomial bases. Write H = Z^r direct-sum T with T finite
abelian. Over an algebraic closure of Q the finite group algebra of T is
a product of fields: diagonalize its characters, equivalently factor the
polynomials x^n-1 into distinct linear factors in characteristic zero.
Thus Qbar[H][z_w] is a finite product of Laurent polynomial rings and is
reduced. Extension from Q to Qbar is injective coefficientwise, so
Q[H][z_w] is reduced. Any nilpotent in A_Q lies in one of these injective
subrings and is therefore zero.

Consequently the intersection of all prime ideals of A_Q is zero. For
each such prime P, let K_P = Frac(A_Q/P). Each K_P has characteristic zero,
and the maps

    A -> A_Q -> A_Q/P -> K_P

jointly separate elements of A. Composing with field extensions to
algebraic closures preserves separation. This proves the lemma. ∎

No component need itself be universal for all specializations. Indeed §2
shows why a single component cannot be. The kernel argument in §6 uses
all components coefficientwise, not tensoring with a product and not
commuting tensor products with infinite products. This also avoids finite
presentation or finite generation assumptions on the Hom modules.

Every field point preserves all parameter axioms and all CScalars: group
units stay units, while an interior coefficient may become zero, which is
permitted. The datum, roots, heights, symmetrizer and matching index sets
are unchanged. Hence the field candidate applies at every K_P (or its
algebraic closure). Only characteristic zero is used here.

## 5. Integral spanning with the full exterior coefficient algebra

Fix equal-weight words a,b, an external weight mu, and a complete matching
choice F, with all its representatives, distinguished points and serializers
fixed independently of the coefficient ring. Let L be its decorated labels.
Write

    E = ((I x N) ->_finite N) x Finset {i in I : p_i=1}.

There is an A-module basis e_eta of SYM_A indexed by E: ordinary elementary
polynomial monomials times exterior monomials in the fixed increasing
order on odd colours. For arbitrary I all supports are finite. Keep that
same order for every scalar extension. The repository already constructs
this basis over an arbitrary commutative ring in
[BubbleCoefficientBasis.lean](../../OddMath/SKM/BubbleCoefficientBasis.lean),
`SYM.coefficientBasis`, via `SYM.polynomialExteriorEquiv`. This is an
abstract coefficient basis, not a claim of bubble injectivity.

Let H_A be the actual SKM presented Hom for a,b,mu, and define

    F_A = direct-sum_(ell in L, eta in E) A,
    phi_A(ell,eta) = F.expansion(cs_A,mu)(single ell e_eta).       (2)

By BE2 Theorem 8.1's integral spanning argument, as implemented by
`MatchingBasisChoice.expansion_surjective` in
[Nondegeneracy.lean](../../OddMath/SKM/Nondegeneracy.lean), phi_A is surjective.
Its ambient assumptions are `[CommRing A]`, `Scalars D A` and supplied
`CScalars`, not `[Field A]`. Expand each of the finitely many SYM coefficients
in its basis to obtain (2). This supplies actual integral spanning rather
than making it another unproved premise of descent. No inverse bubble map
or dimension formula is used.

The exterior factor is essential: its labels are arbitrary finite subsets
of odd colours, not merely singleton odd generators. It is free as an
A-module even though it has square-zero generators and is not an ordinary
commutative algebra in general. Our argument is about ordinary A-modules
with a parity decomposition. It never takes a fraction field of SYM_A or
replaces SYM_A by its even quotient.

## 6. Descent proof

First use scalar change on the actual presentation (§7) to map (2) to
each field K_P. Its diagram and coefficient image formulas identify the
images with exactly the field family's elements. By the field candidate,
the expansion over K_P is injective. The full coefficient basis over K_P
therefore makes the family indexed by L x E linearly independent.

If v = sum a_(ell,eta)(ell,eta) lies in ker(phi_A), its image gives a
finite relation in every such field. Every a_(ell,eta) maps to zero in
every K_P. By §4 it is zero in A. Thus phi_A is injective and hence, by
§5, an A-linear isomorphism. Notice that neither H_A -> H_(K_P) nor
H_A -> product H_(K_P) was assumed injective. No torsion-freeness or
projectivity of H_A was assumed; freeness is the conclusion.

Now specialize through the map A -> R of §3. The actual presentation gives

    R tensor_A H_A  ~= H_R,
    R tensor_A F_A  ~= direct-sum_(L x E) R.                     (3)

The tensor of phi_A is an isomorphism for every R, including nonflat R,
because its inverse tensors too. By the basis-image formula it is phi_R.
Identifying the source with L ->_finite SYM_R makes phi_R exactly the
expansion map. This proves the assertion of §1 for every F, mu and a,b.
It also handles the zero ring, where both modules are zero.

This is not the false claim that independence survives arbitrary
specialization. The isomorphism over A, including spanning, is established
before specialization. Nor is it detection by the residue fields of R:
those would miss nilpotent coefficients. The characteristic-zero fields
separate A; specialization of an isomorphism handles R.

## 7. Exact presentation interfaces required for scalar change

The following are the needed outputs, with A and R arbitrary commutative
rings and f : A -> R carrying Sc_A to Sc_R and cs_A to cs_R. Names here
specify mathematics, not declarations claimed to exist.

1. A semilinear map H_A -> H_R, coefficient change on raw diagrams,
   preserving every named generator, composition and horizontal contexts.
   It must carry `relation D Sc_A r` to `relation D Sc_R r` and carry
   signed interchange relations as well.
2. An R-linear equivalence R tensor_A H_A ~= H_R whose pure-tensor formula
   is r tensor [d] |-> r [d]. Its inverse sends each raw diagram [d] to
   1 tensor [d]_A. This equivalence is independent of nondegeneracy.
3. Coefficient change SYM_A -> SYM_R, preserving elementary generators,
   each odd delta, their ordered products, and betaSYM at every mu.
   In particular it sends coefficientBasis_A(eta) to
   coefficientBasis_R(eta); it preserves the selected matching expansion.

Here is a presentation proof of item 2, not a flatness hypothesis. For
fixed boundaries let P_A be the free module on raw diagrams and J_A its
contextual relation submodule. The coefficient map identifies
R tensor_A P_A with P_R. Under this identification the image of
R tensor_A J_A is exactly J_R. Each direction follows from the same
relation labels and raw pre/post diagrams: map a contextual A-relation
forward; conversely each R-relation is the specialization of its A-relation,
and expand arbitrary R-linear contexts into finite sums of raw diagrams.
Whiskered relations use the same compatible coloured boundary words,
since D and X have not changed. The signed interchange coefficients are
integer signs and commute with f. Right exactness then gives the cokernel
isomorphism (3). No injection of R tensor_A J_A into P_R is claimed.
Equivalently the inverse in item 2 kills each target contextual relation
by the same expansion, and the two composites fix all raw diagrams.

An audit of [Presentation.lean](../../OddMath/SKM/Presentation.lean) shows:

* The signature and `Rel D` indices are independent of coefficients.
* Quadratic, slide and braid relations are finite sums with coefficients
  t_ij, s_ij^pq and integer signs. The disconnected quadratic relation has
  one coefficient. There is no division by a nonunit parameter.
* Adjoint zigzags and all inversion equations are finite polynomial
  relations in named generators, including both product identities for
  every inverse matrix. Base change is not being applied to the property
  "some matrix happens to be invertible"; its inverse entries are already
  generators in the presentation.
* Height tests, inverse matrix sizes and redundant-generator zero relations
  depend only on the integer coroot pairings. No relations are added by
  testing whether a parameter specializes to zero.
* CScalars do not enter `pres`. They enter the derived left cups/caps and
  the chosen bubbles/expansion. The formulas use the supplied units and
  their inverses, so mapping `Units` proves their naturality; finite fake
  bubble recurrences, bending and decoration then preserve the same map.

The fixed-KL implementation's `IntegralScalars.homBaseChange` and
`homMap_twoB` are precedents for items 2 and 3, not substitutes for them.
Only a forward scalar-change map is insufficient for the final step of
§6. Conversely no scalar-change theorem about arbitrary Hom functors,
module categories, or the entire swapped action is required here.

## 8. Field uses in the candidate and an integral bounded retraction

The deduction does not specialize the field detecting action. It uses only
its independence conclusion. Consequently its noncanonical field choices
need not vary with parameters or survive base change. The relevant field
uses in the frozen construction and its cited notes are as follows.

* `InvertibleDotProbe.md` §3 uses stabilized generalized-zero kernels and
  finite-dimensional injective-implies-surjective to prove dot invertibility.
  Its §4 separately descends units using finite modules and Nakayama. For
  §6 here, the probe is needed only over characteristic-zero fields.
* `DeformedReservoirBound.md` §§1,3–5 uses finite-dimensional coefficient
  and content algebras to obtain finite integer support and positive-closure
  nilpotence. These arguments take place over the field point. The unit and
  top-coefficient specializations of the probe do not specialize the Q
  endpoint parameters or remove the reservoir exterior generators.
* `SwappedNondegeneracy.md` §4 and `SwappedVacuumCoordinates.md` §7 extend
  an injective bounded-window map to a linear left inverse using a vector
  space basis. This is a genuine field-only argument as stated. Injective
  maps of modules do not generally split (e.g. multiplication by 3 on
  Z[1/2]). It must not be reused over A merely by replacing "field" with
  "ring".
* Right projectivity in `DeformedSquareResolution.md` comes from specified
  PBW summands, monic annihilators and its resolution, not vector-space
  complements. `DeformedActionAssembly.md` and the Hom/precomposition
  comparisons use supplied inverse maps and balanced tensors. No assertion
  that arbitrary Hom commutes with specialization is needed in §6 here.
* Finite-colour contextual witnesses, signed matching transitions, the
  polynomial/exterior basis and the final oriented-boundary reduction do
  not themselves demand a field. The field candidate, not this descent,
  remains responsible for its full finite-witness and action realization.

There is also a concrete integral replacement for the bounded splitting,
if a direct integral construction is desired. It is stronger than merely
knowing the bounded map is injective:

**Bounded projection lemma.** Let C have a specified R-basis (b_j) with
nonnegative weights w(j), and let K be a submodule contained in the span
of b_j with w(j) >= N. If d < N, projection onto the basis indices with
w(j) <= d annihilates K. It therefore descends to

    L_d : C/K -> F_d,          L_d(q(x)) = pr_(<=d)(x),

where F_d is the span of the indicated low-weight indices. The formula is
well-defined because pr_(<=d)(K)=0, and L_d q|_(F_d) = identity. This is
R-linear over any ring and uses no splitting of an arbitrary submodule.
An infinite basis or infinite low-weight window causes no problem because
each vector has finite support.

For the actual coefficient-extended affine PBW basis, the high-ideal bound
in `SwappedVacuumCoordinates.md` §6 has precisely this form, with threshold
N0 - 2 choose(length(s),2). Thus its proposed actual ideal identification
and bound, together with the integral PBW basis, give this L_d without a
field. The source-order sign involution and the triangular theta and
inverse are defined by integer signs and integral power-series coefficients;
the recovery composite then works on the same bounded window.

This eliminates that one field choice, not the outstanding full-ELV
factor-action, normalized pre-Hom inverse or vacuum-identification work.
Finite generation of a graded module over a degree-zero ring also suffices
for finite degree support: choose finite generators, decompose them into
finitely many homogeneous parts, and use those parts as generators. Thus
the finite-support step can in principle be integral too. Establishing all
of the actual integral action interfaces is not needed for the simpler
universal-ring deduction and is not asserted by this observation.

## 9. Adversarial checks and remaining obligation

The possible failure points have specific answers, not added hypotheses:

* **A might not be a domain.** True; §2 demonstrates it. Section 4 proves
  exactly the joint characteristic-zero injectivity actually used.
* **The universal normalization quotient might have nilpotents.** Its
  equations are group relations with coefficient +1, so (1) is an honest
  group algebra polynomial extension. It is torsion-free over Z2 and
  reduced after rationalization. No general assertion about arbitrary
  binomial quotients is used. Specializations may have nilpotents.
* **The parameter ring could miss root dependencies.** All X-labelled
  normalization generators and all shift laws are retained; taking a
  saturated relation subgroup or setting every c to 1 would be wrong.
* **Field points might lose admissibility.** All required nonzero endpoints
  are units. Allowed interior coefficients may vanish. Separate odd
  support and homogeneity are imposed before specialization.
* **Exterior coefficients might disappear in fields.** They are free
  module basis labels of SYM, not scalar parameters specialized to zero.
  Every exterior monomial remains among the labels in (2).
* **Integral spanning or presentation base change might be assumed.** The
  former is the existing arbitrary-ring expansion theorem; §7 proves the
  latter on the actual relation families in prose and states its precise
  missing Lean interfaces. The fixed-KL arbitrary-ring theorem does not
  discharge these SKM interfaces automatically.
* **A field splitting might have been specialized.** None is: only the
  universal basis is specialized. Section 8 supplies an independent integral
  bounded projection when the actual PBW ideal bound is available.
* **A new inversion of d_i might have entered.** A is over Z[1/2], not
  Z[1/(2 product d_i)]. Rationalizing to test its coefficients does not
  localize the final target R. Positive odd characteristics dividing some
  d_i remain in the conclusion.

There is no remaining commutative-algebra obstruction in this proposed
route. There is still a genuine proof boundary: the full field candidate
is not a Lean theorem. In addition to that independent mathematical input,
formal descent needs the universal group-algebra construction and separation
lemma, the actual scalar-change equivalence and expansion square, and the
short kernel argument of §6. A useful next bounded result is item 2 of §7
for arbitrary coefficient maps, with the inverse tested on nonflat scalar
extensions; then item 3 must include normalized bubbles and the full
polynomial/exterior coefficient basis. No additional action construction
or free-weight-realization comparison is required for those tasks.
