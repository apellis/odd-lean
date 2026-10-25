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
