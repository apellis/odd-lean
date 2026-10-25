# Relative rewriting and odd spectral blocks

This note supports the Brundan–Ellis §8 research target. The algebraic arguments
below are written arguments and exact finite diagnostics, not new Lean theorems.
Neither a general confluent SKM presentation nor an odd unfurling equivalence is
constructed here.

## What the Dupont–Ebert–Lauda proof supplies

Benjamin Dupont, Mark Ebert and Aaron D. Lauda, *Super rewriting theory and
nondegeneracy of odd categorified sl(2)*, Quantum Topology 16 (2025), 569–653,
DOI 10.4171/QT/185, §§2.7–2.8 and Theorems 6.1–6.2, give a rank-one proof.
The primary source inspected is the publisher PDF:
https://ems.press/content/serial-article-files/48103.

They orient diagram relations as linear rewriting rules. A subsystem of signed
isotopy relations is handled modulo rewriting; this is not permission to use
unsigned pivotal isotopy. Bubble slides and crossing cyclicity create cycles,
so strict termination of the complete system is replaced by quasi-termination.
Decreasingness and the resolution of critical branchings establish confluence
modulo the isotopy subsystem. The branchings include parameter-indexed families,
not just a finite list of small diagrams.

The resulting quasi-normal forms are reduced oriented matchings, dots at
specified endpoints, a fixed crossing convention and ordered rightmost bubbles.
Uniqueness of their expansions gives a basis. Theorem 2.32 is the abstract
basis-from-confluence result; Theorem 6.1 verifies its rewriting hypotheses for
odd sl2, and Theorem 6.2 gives nondegeneracy. The source works over a field of
characteristic different from two. Its rank-one conclusion does not by itself
give the full arbitrary-ring, multicolour target of the present branch.

## A relative normal-form target

Let H be the *independently presented* upward quiver-Hecke supercategory, and
let K be the abstract all-colour SYM. For upward boundary words u,v, write
N(u,v) for the free K coefficient module on the usual upward PBW labels, with
the prescribed source coefficient order and super signs. Existing affine PBW
identifies this with the corresponding abstract skew-dot/crossing coefficient
module; it does not assert that N embeds in SKM.

A sufficient target for a rewriting proof is a k-linear map

    NF(u,v): free SKM diagram expressions u -> v -> N(u,v)

with two independently proved properties:

1. NF sends each abstract upward PBW diagram with a bubble coefficient to its
   corresponding basis vector and coefficient.
2. NF takes equal values on the two sides of every defining SKM relation in
   every typed context whose *external* boundaries are u,v.

Property 2 makes NF descend to SKM Hom(u,v). Property 1 makes this descended
map a left inverse to the upward expansion, proving its injectivity. This is
an elementary retraction argument; neither independence of betaSYM nor upward
SKM independence is among its hypotheses.

Existing spanning normalization provides choices of expansions, but not
property 2. The useful rewriting task is therefore relation-invariance of a
specified algorithm, not merely existence of another normalization sequence.
Internal contexts may contain cups and caps even when the external boundaries
are upward. Restricting the critical-pair analysis to upward-only words would
miss the essential additional relations.

This relative formulation is an alternative implementation target, not a claim
that its confluence proof is smaller than constructing a separating action.
In particular, it does not bypass the mixed oriented branchings.

## Critical families that distinguish the multicolour problem

The following is a prioritization of tests, **not an exhaustive critical-pair
classification**:

* A bubble of colour i transported across a j/k crossing: compare moving the
  bubble before or after crossing reduction, retaining the shifted local region,
  t-parameters and all polynomial correction terms.
* A mixed-colour braid adjacent to a cap or cup: compare the braid correction
  before taking the mate with the mated local reduction. Test repeated outer
  colours i,j,i as well as distinct colours; the correction polynomial matters.
* A same-colour inversion summand inside a different-colour context: compare
  sorting followed by bubble normalization with normalization followed by
  sorting. Identity summands cannot be discarded.
* Two independent odd bubble coefficients moved past a dot/crossing/cap:
  compare simultaneous transport with the two serial transports. The product
  delta_i delta_j must remain nonzero in the test coefficient algebra.
* Braid/quadratic reductions in contexts containing a closed component: a
  crossing ceiling alone does not control bubble or open-dot redistribution.

The first test beyond rank one should retain symbolic permitted parameters and
at least one connected colour pair. Testing only disconnected colours checks
super interchange but misses the mixed polynomial corrections. Finite successes
are evidence; an all-parameter indexed identity is the desired next result.

## Why ordinary scalar spectral splitting is not graded

Let V be a superspace in characteristic different from two, with parity operator
P. If x is an odd linear operator, Px=-xP. Hence P carries the generalized
a-eigenspace of x to the generalized (-a)-eigenspace. For a nonzero eigenvalue,
the individual eigenspace need not be a graded subspace.

Already on a 1|1 space take

    P = diag(1,-1),       x = [[0,1],[1,0]],       x^2=1.

The scalar spectral projectors e_+=(1+x)/2 and e_-=(1-x)/2 are exchanged by P.
They are not even idempotents. Thus an ordinary unfurling that makes +1 and -1
separate objects in a supercategory is not justified by scalar diagonalization.
It may be useful after forgetting grading, but then requires a recovery theorem.

For distinct odd dots x,y with xy=-yx, scalar shifts also fail:

    (x-a)(y-b)+(y-b)(x-a) = -2b x -2a y +2ab.

So replacing odd dots by scalar-shifted nilpotent dots does not retain the
defining skew relation. These observations reject this *naive graded scalar*
construction; they do not rule out odd unfurling.

## Squared-dot blocks and Clifford factors

The even operators z=x^2 preserve parity. If xy=-yx then x^2 commutes with y,
and hence with y^2. Thus simultaneous spectral blocks for squared odd dots are
compatible with the skew-dot algebra and grading. They need not be central in
the entire quiver-Hecke algebra: crossings transport the labels.

On a block with z=a+t, a an invertible even scalar and t nilpotent, work over a
characteristic-zero coefficient ring after adjoining an even square root of a.
The finite binomial series gives an even invertible square root s of a+t.
It commutes with x. Then c=x/s is odd and c^2=1. Thus the nonzero squared-dot
block contains a Clifford factor; it is not simply a nilpotent odd-dot block.
For several anticommuting dots the corresponding c's anticommute. The zero
squared-dot block instead has nilpotent x and belongs to the odd/nilpotent sector.

This local construction explicitly uses characteristic zero and a square-root
extension. It is a diagnostic model for a possible completion/Morita argument,
not a solution over the full base rings in the conjecture. Descent, off-diagonal
crossings, braid compatibility and cups/caps remain necessary.

The existing KKO intertwiner has norm

    g^2 = -(y^2-x^2)^2 (x^2+y^2).

Consequently distinct squared spectral values alone do not make this operator
invertible: sum-zero pairs remain resonant. Unit rescaling cannot remove that
zero norm. Whether a different exchange generator removes the obstruction, or
the resonant pair must remain joined in the unfurled datum, needs a separate
comparison; the displayed norm alone is not an impossibility theorem.

## Independent exterior parameters survive the graded block

The exact checker constructs Cl_1 super-tensored with the regular exterior
algebra on two generators. Write C for the odd Clifford matrix, P_C for its
parity matrix and L_i for left exterior multiplication. On the eight-dimensional
tensor product put

    x=C tensor 1,       d_i=P_C tensor L_i.

Then x is odd and invertible, the d_i are odd square-zero, xd_i=-d_ix,
d_1d_2=-d_2d_1 and d_1d_2 is nonzero. Thus an invertible odd dot is compatible
with retaining independent exterior coefficients; it does not force their loss.

Compression to the +1 scalar eigenspace loses multiplicativity in a particularly
instructive way:

    e_+ d_i e_+ = 0,
    e_+ d_1 d_2 e_+ != 0.

Hence such compression cannot replace a super representation that detects
products of odd coefficients. Keeping the whole squared-dot block avoids this
specific failure. The checker also rejects ordinary shifted odd-dot relations
and incorrectly commuting joint scalar projectors.

Run:

```sh
python3 scripts/Nondegeneracy/odd_spectral_blocks.py
```

This is exact rational matrix evidence with six negative controls. It constructs
neither a quiver-Hecke action nor an SKM action and proves no matching independence.

## Follow-up: adversarial score audit and a reducible overlap family

The executable `scripts/Nondegeneracy/cyclotomic_score_audit.py` independently
normalizes two-strand words, rather than checking only numerical scores.
It tests the odd nilHecke rules and a distinct-odd-colour Ore model with
`τx=−yτ`, `τy=−xτ`, and the deliberately inhomogeneous invariant polynomial
`τ²=1+x²+y²+3x²y²`. The latter is a local stress model, not a constructed
general SKM datum/action. Both models retain independent exterior generators
`d,e`, anticommuting with all three odd strand generators. All 25 minimal
length-three rewrite ambiguities in each model agree. The test checks 18,432
explicit two-sided multiples of pure and weighted deformed generators and
finds the asserted score support. An unweighted unit constant term fails the
bound, as it should. These finite tests do not replace the general proof or
the three-strand braid audit.

There is also a useful reduction in the proposed DEL overlap agenda. Consider
a bubble of colour `i` passing a crossing whose two strand colours are both
different from `i`. The connected normalized slide formula already proved in
`BubbleSlidesConnected.lean` expresses slide corrections through its
polynomial `P_ij`. Every exponent on an odd `j` strand in this polynomial is
even, by `Sc.parity_of_ne_zero` and `parity_mul_dn`. Consequently these factors
are even, and use squared dots on odd strands. Formal generating-series
parameters here are ordinary commuting bookkeeping variables.

For distinct crossing colours `j≠k`, the dot-crossing relations have no
identity correction. They therefore transport the factors individually:

`τ_jk P_ij(x) P_ik(y) = P_ij(y) P_ik(x) τ_jk`,

where variables on the right follow their strand to the new position. The
even powers remove every odd dot-crossing sign, and the transported factors
commute. This resolves the **polynomial transport part** of this overlap;
the actual diagrammatic statement still has to match boundary weights,
normalizations and the common bubble's super-interchange sign.

For an equal odd crossing colour `j=k≠i`, put `u=x²`, `v=y²`, `c=x−y`.
The odd nilHecke rules give

`τu=vτ+c`, `τv=uτ−c`,

and `c` commutes with `u,v`. Induction on polynomials consequently gives

`τ f(u,v) = f(v,u) τ + c ∂f(u,v)`,

where `∂f=(f(u,v)−f(v,u))/(u−v)` denotes the polynomial divided difference,
not localization or division in the coefficient ring. Hence every symmetric
polynomial in `u,v` commutes with `τ`. In particular the two identical slide
factors `P_ij(x)P_ij(y)` commute with this crossing. A single factor need not:
`τx²−y²τ=x−y` is a useful nonzero control. This reduces the same-colour
polynomial diamond to a familiar centrality identity rather than a new
critical-overlap computation.

`scripts/Nondegeneracy/bubble_crossing_overlap.py` verifies 50 transport and
symmetric-centrality cases, the nonzero single-factor residual, and an
independent exterior-pair control. The remaining difficult families include
the cases where the bubble colour equals a crossing colour, cups/caps and
inversion summands, and three-strand mixed braid interactions. No global
termination, confluence, or relative normal-form invariant is supplied here.

## Connected two-odd-colour reservoir pilot

For off-diagonal Cartan entries `−2`, take the permitted two-odd-colour
quadratic `Q(x,y)=x²+y²`; parity excludes an interior `xy` term. Two nilpotent
reservoirs make `Q` nilpotent. Thus the invertible crossing from a disconnected
tensor construction cannot simply be reused in both directions: its composite
would be invertible, whereas the required quadratic is nilpotent.

There is nevertheless no obstruction at the level of two-strand upward local
relations. The exact pilot `scripts/Nondegeneracy/connected_odd_reservoir.py`
uses two copies of the four-dimensional exterior reservoir from
`nonvacuum_exterior.py`. Their super tensor product has dimension 16. Give
the reversed-word summand the opposite parity grading. If `S` is the superflip
and `P` total parity, put `J=P S` and set

`τ_ij=J`, `τ_ji=Q J`.

Both maps are odd between the shifted word summands; they obey signed dot and
colour-specific exterior-coefficient transport, and their two composites
equal `Q`. Their ranks are 16 and 6, respectively. The product `δ_i δ_j` has
rank 4 and remains nonzero, while `Q` has nilpotence index 3. The computation
also rejects using `J` in both directions, as the disconnected case would.

This pilot exposes a concrete limitation rather than establishing separation:
`Q δ_i δ_j=0`, so the reverse crossing decorated by the two independent odd
coefficients is zero at this small cutoff. Retaining a nonzero bubble product
does not by itself give joint operator/coefficient detection. Growing
reservoirs and the weighted separation bound are necessary for this design.
There is no three-strand braid, adjunction, mixed `EF` inversion, or actual
two-colour bubble computation in this pilot. These remain construction tasks.

### Repeated-colour braid and distant odd crossings

The next pilot `connected_iji_reservoir.py` uses the actual two-strand
rank-one reservoir operators `(a,b,t)` on the `i` factor and the one-strand
reservoir on the `j` factor. It assigns 16-dimensional modules to `iij`,
`iji`, `jii`, in canonical colour-grouped coordinates, with parity shifted
by the number of colour inversions in the word. Mixed increasing crossings
are total parity `P`, decreasing crossings are `QP`, and the same-colour
crossing is `t⊗1`. All three-strand upward relations pass. In particular the
`iji` braid residual is `x_3−x_1`, of rank 8, exactly the nonzero correction
in `Presentation.lean`'s `braidEq` for this datum. Setting that correction
to zero fails the test. The mixed exterior product remains rank 4.

The parallel action stream supplied the missing sign for distant odd
crossings: multiply a mixed crossing at positions `r,r+1` by
`(−1)^inv(word[:r])`, counting colour inversions in its strict prefix.
`connected_iijj_reservoir.py` checks this recipe on all six words of content
`2i+2j`, with 16-dimensional modules obtained from two rank-two reservoirs.
All 12 braid identities and 6 distant-crossing identities pass, together
with dot, coefficient, parity and quadratic relations. Without the prefix
sign, the two disjoint increasing crossings on `ijij` commute instead of
anticommute. Thus the sign is detected by a genuine negative control.

These are fixed-content upward algebra representations, consistent with a
parabolic-induction interpretation. No general all-content construction or
coherent inclusions between these representations has been proved. In
particular, they do not furnish the adjunctions, normalized bubble maps or
weight-dependent inversion decompositions of a connected SKM action.

### Why fixed independent rank-one towers cannot supply connected inversion

There is an elementary dimensional obstruction to promoting an unchanged
external tensor product of fixed rank-one actions. On a nonzero finite
test object `M=M_i⊗M_j`, define

`c_i(M)=(dim(F_i E_i M)−dim(E_i F_i M))/dim(M)`.

If the `i` functors act only on the fixed `i` factor, applying `E_j` to the
other factor multiplies numerator and denominator by the same dimension
ratio. Hence `c_i(E_j M)=c_i(M)` whenever both objects are nonzero. A
same-colour SKM inversion decomposition, after forgetting parity shifts,
forces this number to equal `h_i(λ)` or its negative, according to the
fixed choice of `EF/FE` convention. In the connected datum under discussion,
`h_i(λ+α_j)=h_i(λ)−2`. The two demanded numbers differ by 2, a contradiction.
Parity shifts cannot fix the mismatch because they preserve ordinary
dimension. This argument assumes the finite-dimensional test objects and
functor values used in the reservoir experiments; it is not a claim about
arbitrary infinite or degenerate categories.

Thus adjusting only the mixed upward crossings is insufficient. A connected
categorical construction must change the rank-one tower with the other
colour's content, or use a genuinely multicolour induction algebra whose
adjunction and inversion already reflect the connected Cartan matrix. The
fixed-content upward pilots remain valid tests of the crossing formulas.

### A general upward construction: parabolic induction

The fixed-content tests suggest a construction that does not require guessing
crossing matrices. For finite content `β=Σ n_i α_i`, choose a total order on
its colours and the grouped word `g=i_1^n_1 ... i_r^n_r`. Inside the affine
QH algebra let `e_g` be its idempotent and let `B` be the super tensor product
of the same-colour affine algebras on these contiguous blocks. The existing
affine PBW theorem identifies this with the corresponding grouped-word
corner: permutations fixing `g` are precisely the within-block permutations.
For any left `B`-module `M`, ordinary algebraic induction gives an honest
upward representation

`H_β e_g ⊗_B M`.

PBW also makes `H_β e_g` a free right `B`-module on minimal colour shuffles.
Indeed every permutation factors uniquely as a minimal shuffle followed by
a within-block permutation, with lengths adding. Moving dots past the
minimal shuffle crosses only distinct colours, so introduces only the
prescribed unit signs and no nilHecke identity corrections. PBW proves
independence of the resulting right-module coordinates. Thus induction
has underlying module a direct sum of shifted copies of `M`, one per
shuffle. For a tensor product of finite rank-one reservoirs the dimension
is the multinomial number of shuffles times the product of their dimensions.
The construction extends coefficientwise to the explicit super tensor
extension with independent exterior parameters.

This is a written PBW-based construction, not a new Lean theorem or a claim
that the tested matrix formulas have been formally identified with it.
It supplies arbitrary-content upward modules and preserves any nonzero
coefficient acting on `M`. It does not make them jointly faithful for
decorated PBW operators at a fixed cutoff, and it does not make these
modules compatible with a connected categorical induction/restriction
tower. Those are the substantive next tasks; another isolated quadratic
or braid check cannot settle them.
