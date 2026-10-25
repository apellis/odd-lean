# Spectral compensation: exact targets and an actual coefficient check

This separates a verified one-colour coupling calculation, an algebraic
weighted-cover calculation, and the outstanding categorical comparison.
The intended general scope is characteristic zero with symmetrizable,
weighted-homogeneous parameters and nonzero extremal coefficients. It does
not cover arbitrary BE2 parameters or claim an odd unfurling theorem.

## Complete probe components, not isolated vertices

The existing even implementation uses the full closure of spectral labels:
`Categorification/KLR/Unfurling/SpectralRouqFamily.lean` constructs the family
from `coverDatum`; `CoverFurling.lean` proves the relevant-label finiteness,
branched-cover pairing and base-weight identities. A weighted seed is not
an isolated A1 vertex. Its neighbouring labels can become active as strands
are added. The negative and positive components have no arrows *between*
them, but each component retains its internal Cartan interactions.

The same distinction is essential here. A nonzero odd squared spectrum a
has a same-original-colour partner -a: the odd intertwiner norm has a simple
factor a+b, so the opposite-squared-spectrum block is resonant. The basic
cutoff-two probe therefore corresponds to an even A2 pair with a
fundamental highest weight, giving three folded weights -2,0,2. Replacing
it by an isolated even A1 would give the wrong Cartan and coroot counts.

## The weighted Cartan identity to implement

Write r_i=1+p(i), so r_i=2 at an odd original colour and 1 at an even one.
Use squared-dot coordinates for an odd colour and ordinary coordinates
for an even colour. On a nonzero component, the candidate refined vertices
are even. At zero, retain the original super Cartan component.

For distinct original colours, write Q_ij=q_ij(z_i,z_j). Its degree in z_i
is -a_ij/r_i. At a nonzero value b of z_j, the extremal coefficients and
weighted homogeneity imply that q_ij(z_i,b) has this exact degree and has
nonzero constant term. Over an algebraic closure, all its roots are
nonzero and their multiplicities sum to -a_ij/r_i. Thus the nonzero fibre
Cartan row sum, multiplied by r_i, is a_ij.

For the same original colour, an even fibre contributes its single diagonal
2. An odd nonzero fibre has diagonal 2 and the opposite-spectrum neighbour
of multiplicity one, so its row sum is 2-1=1; multiplication by r_i=2
again gives the original diagonal 2. Homogeneity and the nonzero extremal
term also show that a zero label has no edge to a nonzero label. The zero
component therefore has coefficient one, not r_i.

Consequently the precise proposed folded coroot formula is

\[
 h_i^{\mathrm{original}}
 =h_{(i,0)}^{\mathrm{zero}}
   +r_i\sum_{a\neq0,\ a\text{ over }i}h_a^{\mathrm{nonzero}}.
\]

The root-multiplicity calculation justifies the Cartan compatibility target.
It does **not** by itself prove that the categorical inversion has this
multiplicity. That requires the completed Clifford comparison and its
adjunction maps. KKT, [arXiv:1107.1039v2](https://arxiv.org/abs/1107.1039),
Theorem 3.13 supplies a superalgebra isomorphism after adjoining the indicated
Clifford algebra and a *weak* Morita superequivalence; it is not an ordinary
Morita equivalence that automatically transports cups, caps or coroot
multiplicities. The definition of refined parity uses fixed points of the
label involution. A nonzero signed spectral pair has no fixed point, which
explains the even refined vertices after that comparison, while the
Clifford categorical data still have to be tracked.

Brundan–Savage's isomeric inversion matrices provide a related categorical
model: odd vertices have both plain and Clifford-token identity components,
with explicit gamma factors. Their reduced, specific-parameter theorem is
supporting architecture, not a theorem of the proposed general comparison.

If the comparison realizes the displayed formula, a connected zero-sector
lowest vacuum of weight -N and a nonzero-component highest vacuum supported
on seed vertices with total multiplicities L_i have initial folded weight

\[
 \lambda_i=-N_i+r_iL_i.
\]

Subsequent weight changes are supplied by each **whole** nonzero component.
For odd i this requires N_i congruent to lambda_i modulo two. The present
even-cutoff connected-reservoir audit therefore addresses even odd-coroot
components; odd-cutoff or translated-reservoir categorical actions remain
a separate parity-extension obligation.

## Actual fixed-weight compensation retaining an even/odd product

`vacuum_compensation.py` uses the cutoff-four reservoir from
`vacuum_even_exterior.py`, with

\[
 f_A(x)=x^4+x^3\delta+x^2\epsilon+x\delta\epsilon,
 \quad \delta^2=\epsilon^2=0,\quad \delta\epsilon\neq0,
\]

and a highest probe with polynomial (y²-a)², for nonzero a. The initial
weights are -4 and +4, so the coupled object has weight zero. This test uses
only the first levels of the towers: it is a coupling corner, not a claim
that the higher spectral comparison has already been constructed.

The actual EF/FE mate is an 80 by 80 matrix with two-sided inverse. Its
nonzero blocks have sizes 16 and 64. It is built from the same induction,
coinduction, unit, counit and rational mixed upward crossing as the earlier
nonvacuum calculation. Exact free bases 1,x,x²,x³ and 1,y,y²,y³ provide
balanced tensor and Hom coordinates. Functoriality fuses F(cap)F(cross)
with the coinduction unit, removing a redundant large Hom-space computation;
no inverse crossing or bubble matrix is supplied as an input.

With the native height-zero normalization, the result is

\[
 1+\sum_{r\geq0}B_rt^{r+1}
 =\frac{(1-\delta t)(1+\epsilon t^2)}{(1+a t^2)^2}.
\]

Eight exact moments and an operator recurrence on the cup image certify
this entire series, not merely its initial coefficients. In particular,

\[
 \mathrm{oddBubble}=-\delta,\qquad
 \beta(e_1)=\epsilon-2a,\qquad
 \mathrm{oddBubble}\,(\beta(e_1)+2a)=-\delta\epsilon\neq0.
\]

The four operators 1, oddBubble, beta(e1)+2a and their product are linearly
independent. The default exact test uses a=2; other nonzero integral a can
be supplied with `--probe`. This confirms simultaneous even/exterior
coefficient detection under an actual fixed-weight compensation map.
It does not establish the multicolour convolution formula universally.

There is also an exact external convolution in the previous nonvacuum
pilot: the separately computed factor series are
G_A=1-delta t-3x delta t² and G_B=(1+t²)/(1-t²); their product equals the
series computed from the full coupled inverse in `two_colour_exterior.py`.

## What a general coefficient law would buy

Suppose the completed categorical comparison proves, for each colour,
C_coupled,i(t)=C_reservoir,i(t) P_i(t²), where P_i(0)=1 and all coefficients
of P_i are even scalars in the independent probe base. Then the elementary
coefficients change by

\[
 e'_{i,r}=e_{i,r}+\sum_{a<r}e_{i,a}p_{i,r-a},
\]

and each odd generator is unchanged, up to its specified unit sign. This
has an explicit inverse triangular substitution. It preserves independence
of all ordered exterior products, since it never identifies distinct odd
generators. On a bounded coefficient window the substitution does not
increase reservoir coefficient weight; probe scalars belong to the base.

This is a bounded coefficient argument, not an asserted automorphism of
every finite ELV quotient: a general substitution need not preserve the
finite top-coefficient relation. The action interface should allow the
known triangular coefficient map and then use bounded coordinate
inversion. The remaining hard statement is the normalized categorical
convolution for the full zero/nonzero construction and its compatibility
with the weighted coroot identity and upward operator coordinates.

## Concrete interface changes relative to the native even construction

The dependency implementation is a useful blueprint, but cannot currently
be instantiated with the proposed odd spectral datum:

* `KLR/Unfurling/Cover.lean`, `UnfurlingDatum.arrows_of_eq`, requires every
  arrow between labels over the same original colour to vanish. The odd
  nonzero opposite-spectrum pair has an edge. This is a structural failed
  hypothesis, not a missing proof of the existing hypothesis.
* `CoverFurling.coverFurling_pair` and `GenericWeights.sum_level_difference`
  use unweighted fibre sums. The new pairing must distinguish zero-sector
  coefficient one from nonzero-sector coefficient r_i. At an odd colour,
  positive nonzero probes only adjust the original height by an even
  integer; odd heights still require an odd-cutoff reservoir.
* `TwoRep/FurlingMixedInversion.sameColour_mixedInversion` proves the actual
  mate is invertible for distinct cover labels over one original colour.
  Its input uses the preceding even datum. The odd replacement must
  include the opposite-spectrum interaction and Clifford factors in the
  crossing and the adjunction; an abstract equivalence of upward algebras
  alone does not provide this theorem.
* `CoverBubbleCompatibility.coverRouqFamily_localData_eq` compares the
  actual local generators of the signed-fibre and combined-fibre actions.
  This is the appropriate target before invoking a bubble formula. Its
  proof uses upward compatibility, nilpotence, same-colour mixed inversion
  and the pairing-or-zero alternative. The odd version needs all four
  inputs with the weighted pairing and transported Clifford adjunction.
* `BubbleMultiplicity` and `GenericWeights` use independent level-one
  labels to detect even coefficients, avoiding characteristic-dependent
  powers. Our proposed detector instead uses the reservoir coefficients
  and the bounded inverse triangular substitution. It therefore does not
  require algebraic independence of all probe bubble coefficients. It
  still requires the categorical comparison and invertibility of two.

A precise local algebraic precursor to the multiplicity-two step is the
Clifford extension Cl_l into Cl_(l+1). As a left Cl_l-module the extension
is free on 1 and the new odd generator c. As a bimodule, the second
summand has the parity-twisted right action, since c a=(-1)^|a| a c.
Thus restriction after induction has an ordinary and a parity-twisted
summand, rather than two ungraded identical summands. This explains the
expected plain/token pair in an inversion matrix. It does not yet prove
that the tower equivalences identify this extension with each refined
induction functor, or that their units and counits match the normalized
odd action. Those two tower-level compatibility statements are the
remaining categorical content of the factor-two claim.

For the native finite-observation interface, a sufficient target is more
modest than a quotient automorphism: evaluate on the compensated cyclic
object, identify the resulting finite upward PBW vector with the known
triangular transform of its coefficients, extract bounded PBW coordinates,
apply the inverse triangular substitution there, and reinsert them into
the ELV quotient. The extraction is well-defined beyond the weighted
cutoff bound. This keeps both the probe base extension and the source
placement of the bubbles explicit, and uses no presumed faithfulness of
the action.

## A simpler candidate: retain the original superdatum on both sectors

The weighted even-cover comparison may be avoidable. Take a zero-sector
lowest action of the deformed original superdatum and an original-superdatum
highest action with scalar cyclotomic polynomials

\[
 g_i(x)=(x^2-a_i)^{M_i}\quad(i\text{ odd}),\qquad
 g_i(x)=(x-a_i)^{M_i}\quad(i\text{ even}),\qquad a_i\ne0.
\]

The highest action must be obtained with the appropriate orientation and
parameter/sign duality; it is not simply induction in the same lowest
presentation. Its whole cyclotomic category retains all interactions of
the original Cartan datum. No assertion that a seed is an isolated vertex
is needed. The ordinary cyclotomic action theorem, at the stated source
scope, is the proposed input; the exterior deformation is only needed in
the lowest reservoir.

### Global exclusion of zero probe spectra

Here is an algebraic argument that avoids identifying any refined Cartan
components. Work over an algebraically closed field, in each finite
content of the scalar cyclotomic quotient. Assume its usual finite
dimensionality. Decompose into simultaneous generalized eigenspaces of
the commuting even coordinates z_r=x_r² at an odd colour and z_r=x_r
at an even colour.

Suppose a nonzero joint generalized eigenspace has a zero spectral label.
Choose its leftmost zero label. Every earlier label is nonzero. The zero
label can be transported successively left through each earlier label:

* At distinct colours, the crossing square is Q at these coordinates.
  Weighted homogeneity and the nonzero extremal coefficient give
  Q(0,b) a nonzero scalar times a power of b for b nonzero. Its value on
  the generalized eigenspace is a nonzero scalar plus a nilpotent
  operator, so the crossing is invertible between the two blocks.
* At equal even colours, the usual nilHecke intertwiner is invertible
  between distinct dot spectra.
* At equal odd colours, the polynomial intertwiner from `OddUnfurling.md`
  has norm -(z_2-z_1)²(z_1+z_2). On zero/nonzero blocks this is a unit.
  It exchanges squared-dot labels, although it negates the odd dots.

Each transport preserves nonzeroness. Eventually the zero label is first.
But g_i(x_1) has invertible constant coefficient and x_1 is nilpotent on
this block, so g_i(x_1) is invertible there. The cyclotomic relation says
it is zero, a contradiction. Thus **every probe dot coordinate has nonzero
spectrum at every content**, not merely at the initial vacuum. Nonzero
labels may interact and generate further nonzero labels; none of that
invalidates this argument.

For the reservoir, truncate the positive-degree coefficient algebra above
a sufficiently large weight when considering a bounded detection problem.
The usual finite cyclotomic module bound then gives a finite-dimensional
graded quotient, bounded below, in which all positive-degree dots are
nilpotent. The coefficient truncation must be included in the weighted
separation estimate, rather than presumed harmless. Equivalently one can
work in an augmentation completion and prove topological versions of the
following statements.

Consequently all intertwiners between reservoir and probe sectors are
units by the same argument. This supplies exactly the global separation
needed for a direct zero/nonzero shuffle comparison. It is stronger than
checking cross-sector invertibility only on the vacuum.

### What this bypasses, and what still has to be proved

This proposal bypasses the even refined datum, its forbidden same-fibre
edge, Clifford Morita transport, and the weighted refined-coroot formula.
Use the original action weights directly. The initial height is

\[
 \lambda_i=-N_i+\deg(g_i).
\]

At odd colours deg(g_i)=2M_i, so this does **not** remove the parity
obligation N_i congruent to lambda_i modulo two. At even colours there is
no analogous restriction. Arbitrarily large admissible N_i and probe
levels can be chosen independently while retaining the fixed height.

The remaining construction is genuinely categorical: identify the
completed upward algebra with the shuffle algebra of the two sector
algebras, define E_i as the sum of the sector functors with coherent parity
conventions, and use the transported adjunction to define all mixed mates.
Prove the full local relations and the same-colour inversion using these
actual maps. In particular, one cannot simply call the inversion matrix
block diagonal: the verified finite pilots have nonzero cross-sector
blocks and Schur-complement feedback. Unit intertwiners alone do not
identify that feedback or prove the desired inverse. A compatible
shuffle comparison plus a finite block elimination argument is needed.
Finally compute normalized bubbles from this inverse and prove the
triangular reservoir/probe coefficient law. The existing rank-one
80-dimensional experiment supplies an actual corner of precisely this
construction, including its nonzero feedback and coefficient recovery.

Thus global spectral separation now has a direct argument. The main
unproved step is a two-sector supercategorical coupling theorem, rather
than a full even/Clifford odd-unfurling theorem.

### An all-content algebraic criterion for the remaining inversion

There is a useful rigorous reduction, but it must not be confused with
having identified the coupled matrix. Let J be a nilpotent two-sided ideal
of the common coefficient algebra, J^K=0, and let M be a square block map
between finite projective modules. If its reduction M_0 modulo J has an
inverse which lifts to a map L, then LM=1+R and ML=1+R' with entries in J.
Both R^K and (R')^K vanish. The finite geometric sums give a two-sided
inverse of M. This statement applies to homogeneous supermaps after
inserting the appropriate parity shifts; it makes no commutativity
assumption about matrix entries. Thus exterior and positive-weight
reservoir coefficients introduce no further invertibility obstruction
once the undeformed coupled matrix and a lifted inverse are known.

More concretely, if a common summand of the coupled inversion has a
known invertible block A, elimination reduces the problem to
S=D-C A^{-1} B. It suffices to prove that S modulo J is invertible.
The correction C A^{-1} B must be included: its vanishing is not an
assumption. Once the residue inverse is known, the same finite geometric
argument recovers the complete exterior-deformed inverse.

The separated-spectrum linear equation also has an explicit all-content
solution. If X^q=0 and Y is invertible, the Sylvester operator on maps
from the Y-module to the X-module,

\[
 \mathcal L(T)=T Y-X T,
 \qquad
 \mathcal L^{-1}(U)=\sum_{r=0}^{q-1}X^r U Y^{-r-1},
\]

is invertible, by telescoping on both sides. Replacing Y by -Y gives the
sum version. Applying this to the even squared-dot coordinates proves
invertibility of all zero/nonzero difference and sum denominators that
occur in the odd intertwiner. The formula is valid for noncommutative
endomorphism rings, because left and right multiplication commute; it
therefore applies on arbitrary module objects, not only on vacuum scalar
blocks. It also provides finite resolvent expansions for an eventual
Cauchy-matrix calculation.

The existing `VacuumMixed` and `VacuumMixedDual` files do **not** supply
this final missing matrix identification: their bubble computations
already assume the relevant Rouquier inverse and derive partial-fraction
identities from its cap. Invoking those results to prove that same inverse
would be circular. `VacuumPartialFractions` supplies independent scalar
polynomial identities, but identifying the all-content odd Schur
complement with their resultant/Cauchy pairing still requires a proof.

The next exact target is therefore: in the undeformed zero reservoir,
express the Schur complement of the actual coupled same-colour mate in
factor-inversion coordinates, including its identity remainders, as an
explicit separated-spectrum pairing with inverse given by the preceding
resolvent formula (or its finite confluent matrix). Only after this
identity is established does the nilpotent coefficient argument upgrade
it to the full independent exterior reservoir. The present evidence does
not establish that identity at all contents.

The finite pilots provide a more explicit starting point for that target.
Their mixed upward crossing uses

\[
 a=(X-Y)(X^2-Y^2)^{-1},\qquad
 q=(X^2+Y^2)(X^2-Y^2)^{-2}.
\]

With the ordered dot and adjunction conventions of
`nonvacuum_exterior.py`, mating the diagonal term gives

\[
 C=\sum_{r\ge0}(-1)^r u_{A,r}v_{B,-r-1},\qquad
 D=\sum_{r\ge0}(-1)^r u_{B,-r-1}v_{A,r}.
\]

Here u denotes a dotted unit and v a dotted counit; negative dot powers
are defined on the invertible probe sector. The sums terminate by
nilpotence of the reservoir dot. The script checks these as identities
of actual mate matrices, independently of inverting the assembled mate.
For a general action the same formulas follow by finite resolvent
expansion and functoriality, with its parity shifts fixed in the same
ordered convention. Consequently the Schur correction is a finite
matrix of compositions of factor dotted cups, caps and factor inverses.
Factor Rouquier dual-basis identities should reduce this to a finite
Hankel/Cauchy pairing. This is a substantially more specific target than
asserting cross-sector invertibility; the reduction to an invertible
pairing at every content remains to be proved.

An exact scalar version of the desired remainder calculation is already
available. Let F be monic of degree p, let G=product_b(t-b)^{m_b} be monic
of degree q, assume p>=q, distinct b have unit differences, and G is a
unit in R[t]/F. Then the following p vectors form an R-basis of R[t]/F:

\[
 1,t,\ldots,t^{p-q-1},\qquad
 (t-b)^{-j}\quad(1\le j\le m_b).
\]

Indeed multiplication by G is an automorphism. The first vectors become
G,tG,...,t^{p-q-1}G, with distinct monic leading terms of degrees q through
p-1. The remaining vectors become G/(t-b)^j and form a basis of
polynomials of degree less than q by the confluent partial-fraction/CRT
identity. Together they form a triangular basis of polynomials of degree
less than p, hence of R[t]/F. The zero/nonzero spectral hypotheses imply
the required invertibility of G when F is a power of t, and nilpotent
coefficient deformation preserves it. The opposite inequality is handled
by the dual construction.

This proves the Cauchy/resultant step once a categorical remainder matrix
has been identified with it. A further caution is essential: compressing
a nilpotent dot to an arbitrary direct summand need not give a nilpotent
operator. Thus the identity remainder in a factor inversion cannot be
assigned zero spectrum merely because the full reservoir dot is
nilpotent. Its companion action or dual-basis pairing must be obtained
from the actual dot-slide and factor-inversion identities. This is the
specific missing passage from the scalar lemma to an all-content action.

### The stronger native blueprint: `RouqCoproduct`

The exact all-content even proof lives in `TwoRep/RouqCoproduct.lean`,
not in the vacuum bubble files. Its companion files are
`RouqCoproductBubbles`, `RouqCoproductTeleporter`, `CoproductGauss` and
`CoproductCRT`. It assembles the factor inverses, performs Gaussian
elimination, and reduces the remaining square matrix over End(Id) modulo
the nilradical to an explicit partial-fraction matrix. Relevant theorem
names are `schur_const_eq`, `isIso_lift_of_schur`,
`isIso_lift_teleporter`, and `isIso_rouqMap_of_nonneg` (with the negative
analogue in `RouqCoproductNeg`). This is an existence proof for the
inverse, so it avoids the circularity of applying `VacuumMixed` first.

`RouqCoproductBubbles` proves that non-boundary bubbles for a nilpotent-dot
factor are nilpotent: the infinite Grassmannian identity makes the two
finite bubble series mutually inverse polynomials. It then controls the
closed cup/inverse/cap entries occurring in Gaussian elimination. The odd
analogue must use parity-shifted identity summands and a supercommutative
closed-diagram algebra. A finite family of odd elements and nilpotent
even elements still generates a nilpotent ideal when two is invertible;
this is sufficient for matrix lifting, without treating the entire
superalgebra as an ordinary commutative ring.

The even theorem assumes scalar-shifted nilpotent dots for each local
factor. Our original-superdatum probe has invertible odd dots, so it is
not a direct instance. The promised simplification is to adapt this local
matrix proof to zero versus invertible squared spectra and their rational
bubble series; this is still a real adaptation. In particular no theorem
here asserts that a spectral summand of an odd probe is by itself an
ordinary even sl2 action.

The reservoir compression warning can also be addressed more narrowly:
after positive-weight truncation, homogeneous factor inversion and its
inverse preserve the explicitly shifted grading. A projected dot which
is proved homogeneous of positive degree is nilpotent on the finite
graded identity-remainder space. This uses the grading, not arbitrary
compression. There is no corresponding automatic assertion that a
compressed probe dot is invertible.

At the level of actual strand operators, the parity splitting is explicit.
Put Z=X² and W=Y². These are commuting even operators; Z is nilpotent and
W invertible. Then the diagonal rational crossing is exactly

\[
 (X-Y)(Z-W)^{-1}
 =\sum_{k\ge0}\bigl(Z^kY W^{-k-1}-XZ^kW^{-k-1}\bigr).
\]

The sum is finite. Even reservoir dot powers carry the squared-resolvent
coefficients Y W^{-k-1}, and odd reservoir dot powers carry -W^{-k-1}.
This explains the candidate pair of squared-spectrum Cauchy blocks.
However, Y is an invertible odd map on the probe strand functor, not an
invertible odd endomorphism of the identity. Transporting this parity
identification through caps and the factor-inversion projection is a
necessary part of proving the Schur-block formula. The displayed identity
alone does not identify the parity-shifted identity remainder blocks or
prove that either resulting matrix is a CRT matrix.

## Symbolic inversion at a highest-probe vacuum

There is a substantially simpler local calculation on the objects needed
for coefficient detection. Keep the probe at its highest vacuum, so
E_B vanishes there and E_B F_B is the degree-M Frobenius algebra
B=k[y]/g(y), with g monic and g(0) invertible. Let tr pick the coefficient
of y^{M-1}. This is a nondegenerate Frobenius trace and y is a unit.
For odd colour M is even and the trace has the corresponding odd parity;
the basis vectors carry their prescribed parity shifts.

Allow arbitrary reservoir content with local height -N<=0. Its factor
inversion identifies F_A E_A with E_A F_A plus N identity summands, whose
columns are the dotted cups u_{A,0},...,u_{A,N-1}. After finite positive
coefficient truncation, the reservoir algebra is finite dimensional and
graded. Projecting a higher dotted cup u_{A,r}, r>=N, to remainder
coordinate s<N gives a homogeneous closed coefficient of positive degree
r-s. The finitely many such coefficients in the resolvent expansion lie
in a nilpotent ideal. The first N cups project to the exact standard basis
by the factor inverse identity. This is stronger than an unsupported
claim about compressing a dot.

Modulo that nilpotent ideal, the mixed mate C on the probe vector y^j has
remainder coordinate r

\[
 (-1)^r\operatorname{tr}(y^{j-r-1}),\qquad 0\le r<N,
\]

in the ordered crossing convention above. Fixed orientation normalizations
may rescale rows or columns by unit signs, which must be matched to the
native presentation. The formula itself comes from the actual dotted
unit/counit expansion, not from a guessed inverse.

If M<=N, append the N-M ordinary cups required for total height M-N.
They eliminate the first N-M remainder coordinates. The remaining square
matrix has rows r=N-M,...,N-1 and columns j=0,...,M-1. Apart from unit row
signs it is the pairing

\[
 (s,j)\longmapsto
 \operatorname{tr}(y^{-s}y^j y^{-(N-M+1)}),\qquad 0\le s,j<M.
\]

The vectors 1,y^{-1},...,y^{-(M-1)} form a basis of B: invert the monic
relation using g(0) a unit. Multiplication by y^{-(N-M+1)} is an
automorphism. Thus nondegeneracy of the Frobenius pairing proves this
matrix invertible, including repeated nonzero roots of g.

If M>N, the total inversion instead has M-N cap rows. After eliminating
the common E_A F_A summand, the mixed rows supply trace exponents
-1,...,-N, while the cap rows supply exponents 0,...,M-N-1. Together these
are the contiguous Laurent basis y^{-N},...,y^{M-N-1}. Its Gram matrix
against 1,y,...,y^{M-1} is again invertible, because it is the ordinary
Frobenius Gram matrix twisted by the unit y^{-N}. To turn this latter matrix into the actual reduced mate, one must also
check that eliminating the common E_A F_A summand changes the cap rows
only by positive-degree closed coefficients. This is the corresponding
cup–inverse–cap identity, analogous to `RouqCoproductBubbles`; the
Laurent Gram calculation does not by itself verify that identity. Once
checked, the corrections lift by the finite geometric inverse argument.
At N=0 the scalar target consists only of the probe Gram matrix.

This gives a concrete symbolic local route at every reservoir
content with nonpositive local height, conditional on the already stated
shuffle construction and its ordered mate formula. It does not yet give
the full all-content coupled action: objects with an excited probe, and
all associated relations, remain to be handled. For any fixed finite
upward detector, however, the reservoir cutoffs can be chosen so that all
of its finitely many reservoir contents have nonpositive local heights.
Since E_B kills the highest probe vacuum, the entire upward word stays in
the reservoir. Thus this calculation addresses the actual local inversion
and coordinate window used for that detector, without a Clifford
comparison or an assumption about compressed probe-dot spectra.
