# Separated-sector fusion

## Status and scope

This is a **proposed, incomplete proof** of node A2 of
[GeneralRoute](GeneralRoute.md). No counterexample to zero/nonzero fusion is
found below. In particular, the adjacent odd affine A1 example survives a
six-shuffle braid test with both reservoir exterior parameters present.
Neither that test nor the existing rank-one mate calculation establishes the
all-content super 2-representation. The missing categorical comparison is
identified in §6; A2 must remain open.

The proposed input consists of genuine highest- and lowest-weight actions of
the **original** superdatum, as in [LowestWeightAction](LowestWeightAction.md),
not merely representations of their upward algebras. At a finite reservoir
truncation its dots are nilpotent. On the probe the even spectral coordinate
of each dot is a unit: it is the dot for an even colour and its square for an
odd colour. All probe odd cyclotomic coefficients vanish. Independent odd
coefficients are retained together in the connected reservoir. Inverting a
reservoir dot is forbidden.

Use characteristic different from two for the exterior-coordinate discussion.
The local algebra calculations in §2 do not require division by two. A
universal deformation with unrestricted even coefficients is not itself a
nilpotent reservoir; finite coefficient truncations, or an explicitly specified
completion, are necessary before invoking local nilpotence.

## 1. What the even blueprint supplies, and what it does not

The relevant declarations in the categorification library separate three
operations:

* `KLR.Unfurling.coverProduct` constructs the Hom product for disjoint label
  sets, using `RouqFamily.homProduct`. Its upward relations are for `prodQ`,
  not automatically for the original colour polynomial.
* `TwoRep.Furling` constructs the block sums of functors, their adjunctions
  and dots. Its definition explicitly leaves crossings and Rouquier relations
  to separate results. Thus a product followed by a direct sum is not, by
  itself, a proof of A2.
* `TwoRep.RouqCoproduct.schur_const_eq` identifies the constant Schur matrix;
  `isIso_lift_of_schur` lifts its inverse, and `isIso_rouqMap_of_nonneg`
  applies that argument. `RouqCoproductNeg.schur_const_neg_eq` and
  `isIso_rouqMap_of_nonpos` treat negative total height. These arguments
  use ordinary commutative identity-endomorphism rings and scalar shifts
  of nilpotent dots.

The separated super construction does not shift an odd dot by a scalar and
does not split the connected reservoir into independent colours. It must
replace the last scalar-shift argument by an ordered two-sector argument.
[SeparatedFactorInversion](SeparatedFactorInversion.md) already supplies the
conditional block algebra for that replacement. What is needed is to connect
its inputs to the actual multicolour Hom construction.

## 2. Cross-sector denominators: a complete local argument

Write `z_i=x_i` for even i and `z_i=x_i²` for odd i. The allowed homogeneous
crossing polynomial is a polynomial in these commuting even coordinates.
For distinct colours i,j, the nonzero extremal coefficient gives

    Q_ij(0,y)=t_ji y^(-a_ji),

with a unit scalar t_ji. The exponent is even when j is odd, so this expression
is a unit on the probe under the stated hypothesis. Write

    Q_ij(x,y)=Q_ij(0,y)(1+N).

All terms of N contain a positive power of the reservoir dot. The coefficients
commute with that dot and with one another in this cross-sector polynomial
subalgebra. If x^L=0, then N^L=0. Consequently

    Q_ij(x,y)^(-1)=(sum_(r=0)^(L-1) (-N)^r) Q_ij(0,y)^(-1).

This is a finite identity, preserves every reservoir coefficient, and applies
to even–even, even–odd and odd–odd pairs. It proves a denominator statement,
not a statement about categorical mates. In particular, the mate of an
arbitrary invertible two-morphism need not be invertible.

For equal odd colours put X=x on the reservoir and Y=y on the probe. They
anticommute. Their squares commute, and both X²-Y² and X²+Y² are units:
a commuting nilpotent perturbation of a unit is a unit. Let

    R=(X²-Y²)^(-1),  a=(X-Y)R,  b=(X²+Y²)R².

Then R commutes with X and Y, and direct expansion gives

    aX+Ya=1,    aY+Xa=1,    a²=b.                 (1)

The first two are the inhomogeneous odd slides on the position-preserving
shuffle block. The off-diagonal entries must cancel b in the crossing square.
They cannot both be unnormalised shuffle identities. In the concrete parity
model below, one direction is P and the other is -bP, where P anticommutes
with X,Y and commutes with R. Then aP+Pa=0 and the two-by-two crossing squares
to zero. This uses odd dots with potentially nonzero squares; replacing them
by exterior generators would destroy the test.

`OddMath.Diagrams.OddNilHecke.SeparatedCrossing` formalizes the inverse
commutation and identities (1), with a unit whose value is X²-Y². Unit
existence under spectral separation is already in `SeparatedSquareNorm`.
These local statements do not assert a global shuffle construction.

## 3. Exact falsification tests

Run:

```sh
uv run --no-project --script scripts/Nondegeneracy/separated_fusion_relations.py
uv run --no-project --script scripts/Nondegeneracy/nonvacuum_exterior.py --full
python3 scripts/Nondegeneracy/separated_block_inversion.py
python3 scripts/Nondegeneracy/mixed_mate_recurrence.py
```

### Cross-polynomial units

The first test uses

    Q[z,w]/(z³,(w-2)²) tensor Lambda(delta_i,delta_j).

It is 24-dimensional. Both exterior generators belong to the reservoir
coefficient algebra; neither is a probe ELV coefficient. The probe coordinate
has a nontrivial Jordan part, so this is not only a scalar-eigenvalue test.
The polynomials checked are u+v in even type A2; u+v² and u²+v for the two
mixed orientations of B2; u²+v² for the all-odd Cartan matrix
`[[2,-2],[-2,2]]`; and 3u²+5uv+7v² in even affine A1. Here z,w represent the
even coordinates, including squares at odd colours. Every matrix has a
verified two-sided inverse. The exterior-product rank remains six after
multiplication by Q. The first four determinants are 16777216; the final
polynomial also has nonzero determinant.

### Adjacent odd braid with both sectors occupied

Let a,b,c denote respectively reservoir i, probe i, reservoir j. The reservoir
local odd dot x and coefficient delta satisfy

    x²+x delta=0,  x³=0,  delta²=0,  x delta+delta x=0.

Use the graded tensor product of two such four-dimensional modules and the
two-dimensional probe with odd y²=1. Thus each labelled word is
32-dimensional. No probe exterior coefficient is introduced. Dots X_a,X_b,X_c
are fixed graded tensor operators; the grading of a word is changed by the
parity of its permutation. Let P be the underlying tensor grading operator.

For a distinct-colour adjacent pair use P in the i-to-j direction and QP in
the reverse direction. For the equal-colour pair a,b use the diagonal a from
(1), with off-diagonal P and -bP as above. The test enumerates all six labelled
words and every resulting path, including the position-preserving component
of the equal-colour crossing. It verifies:

* both adjacent slides and the distant-dot slide;
* crossing parity and supercommutation with both exterior coefficients;
* each crossing square;
* both three-crossing paths and every output block of their difference.

For the two words of colour pattern iji the difference is the nonzero
operator `X_3-X_1`, exactly the Q=u²+v² odd repeated-colour correction. All
other braid differences vanish. The exterior-product rank is eight. This
checks the dangerous repeated colour **across** the two sectors, rather than
only a repeated colour inside the nilpotent factor.

This is a fixed three-strand affine representation, not a cyclotomic tower.
It does not test a four-strand distant-crossing relation or produce cups,
caps, or connected multicolour categorical mates.

### Actual smallest nonvacuum odd mate

The second command reconstructs the existing degree-two rank-one example
from balanced induction, constrained-Hom coinduction and actual adjunction
maps. At content (1,1), with a nonzero reservoir exterior coefficient:

* the full EF-to-FE mate is 72 by 72, of rank 72 and determinant one;
* its central two-sector block is 32 by 32, of rank 32 and determinant one;
* both factor mates have rank 16; both coupling blocks have rank 10;
* the feedback F has rank four and F²=0; the Schur pivot I-F has determinant
  one and inverse I+F;
* the reconstructed undotted bubble is minus the reservoir exterior action,
  of rank four; right-linearity, odd parity, homogeneous supernaturality,
  both adjunction triangles and the ordered mixed-mate expansions pass.

These are actual mates, not selected invertible matrices. They are still
rank-one: the affine test above does not upgrade them to connected
multicolour categorical mates.

The conditional companion-matrix test passes 162 combinations of slide sign
and factor heights from -4 through 4. The ordered recurrence/parity test
passes 32 parity-line cases and 76 telescoping cases; 38 incorrect even-sign
mutations are rejected. These tests are not a substitute for the comparison
in §6.

## 4. The conditional all-content inversion argument

Fix a colour i and any content in both factors. Put q=(-1)^p(i). Write X_A,Y_A
for its reservoir EF,FE terms and X_B,Y_B for the probe terms, after the parity
line identifications. Let sigma be each factor mate and let u_r,v_r be its
dotted cups and caps. The factor dot-slide is

    sigma x = u_0 v_0 + q y sigma.

The same-colour total inversion splits into the off-sector EF/FE blocks and
the central block

    [sigma_A  C]
    [D  sigma_B]

with extra **total** dotted cap rows or cup columns according to the sign of
h=h_A+h_B. The target ordered formulas are

    C= sum_(r>=0) q^r u_A,r v_B,-r-1,
    D=-sum_(r>=0) q^(r+1) u_B,-r-1 v_A,r.       (2)

The sums are finite because the reservoir dots are nilpotent. The total cups
and caps have BOTH their A and B components. Dropping the B component can
make an invertible matrix singular, as the mutation test records.

Assume (2) has been derived from the actual crossing under the specified
parity comparisons. The reservoir closed-loop ideal J in
[BlockNilpotence](BlockNilpotence.md) then removes the correction terms in its
factor companion coordinates. Eliminating the common reservoir summands
reduces the map modulo J to the negative cap/cup windows and the dot-conjugated
probe inversion maps calculated in [SeparatedFactorInversion](SeparatedFactorInversion.md).
All four signs of (h_A,h_B), and both signs of h, are covered there. The
argument uses invertibility of probe dots, not a claim that arbitrary
unchanged-mate windows remain invertible.

To lift from modulo J, only finitely many closed coefficients occur in a
fixed block calculation. Their ideal is nilpotent under the hypotheses of
BlockNilpotence. A matrix inverse modulo a nilpotent ideal lifts by the finite
geometric series. This is valid for an associative ring and does not require
a commutative determinant of a supermatrix. Parity shifts must first make the
block entries even morphisms between their specified shifted objects; ordinary
commutative determinants on unshifted odd entries are not valid.

This proves inversion **conditional on the actual block identifications**.
It is independent of content bounds beyond local nilpotence. Merely stating
that a Schur complement exists, or verifying the vacuum, does not establish
those identifications at occupied contents.

## 5. What is genuinely new in the super comparison

1. A shuffle of two odd labels changes the parity line. A sector comparison
   which is an even underlying identity can have odd declared parity. The
   content-dependent shifts in the Hom functors and their action on odd
   natural transformations must be specified together.
2. The equal odd-colour cross-sector crossing has the nonzero diagonal (1)
   and a nontrivial off-diagonal norm. Its quadratic and repeated-colour
   braid relations cannot be imported from the even scalar-difference formula.
3. The mate of that same crossing must give (2), with the displayed signs.
   A separate choice of an invertible EF/FE map is not enough. The ordered
   recurrence is proved in `scripts/NonVacuity/MixedMateRecurrence.lean`, but
   it requires the categorical recurrence as input.
4. Odd reservoir coefficients supercommute; they are not central commuting
   scalar variables. The nilpotent-ideal lift is an associative-ring argument
   in parity-shifted blocks, not ordinary determinant calculus with odd
   coefficients.
5. The lowest-weight action has the transport signs and shifted adjunctions
   in LowestWeightAction. They must agree with the chosen Hom construction;
   conjugating an upward dot alone does not verify that comparison.

## 6. Precise remaining gap and Lean plan

The present results do **not** construct natural, coherent multicolour
sector-comparison maps on Hom(T,W) and prove that their mates have the block
coordinates used in §4. An invertible cross-sector Q and a successful affine
braid test do not imply this. This is the current obstruction to closing A2,
not a counterexample to the proposed mathematical statement.

The implementation should proceed with the following interfaces, keeping
these obligations separate rather than assuming the desired inversion:

1. **Local rational crossing.** `SeparatedCrossing.lean`: (1) and its inverse
   commutation, then the two-shuffle square and slides. The first local
   identities are implemented here. Extend to an actual parity-envelope
   two-block map, rather than an ungraded matrix abbreviation.
2. **Hom sector functors.** Define pre/postcomposition E and F summands,
   explicit content parity shifts, and their right adjunctions. Prove the
   component formulas for total units and counits. Use original-datum weights,
   with h=h_A+h_B; do not silently replace the datum by a disconnected one.
3. **Multicolour affine coherence.** Define the cross-sector distinct-colour
   normalization and the equal-colour rational block. Prove the braid with
   repeated colour in different sectors before packaging all upward
   relations; prove distant supercommutation as a separate obligation.
4. **Actual mates.** In the same convention prove the projected dot-slide
   recurrence, then apply the existing ordered-recurrence lemma to obtain
   BOTH formulas (2). Prove the off-sector mixed-colour mate is invertible by
   its explicit dot expression and adjunction triangles, not by the false
   principle that taking a mate preserves every isomorphism.
5. **All-content Schur comparison.** Port the negative-window lemmas,
   the four height cases, and the nilpotent-ideal lift to the parity envelope.
   State the actual equality of the block matrix with the mate plus total
   cups/caps before asserting invertibility.
6. **Assembly.** Package the original-datum super 2-representation after
   steps 2–5, then expose its evaluation to detection. No theorem named A2
   should have its defining categorical inversion as an assumed field.

The next decisive deliverable is step 4 for the explicit multicolour Hom
functors of step 2, including a connected occupied-content example. Another
vacuum or denominator-only test cannot discharge it.

## 7. Lean interfaces and the comparison still missing

The following modules now separate the proved infrastructure from A2:

- `OddMath/SKM/RouquierData.lean`: homogeneous factor generator data,
  same-colour nilHecke relations, even right adjunctions, the actual ordered
  mate `rouquierMate`, and parity-indexed row/column inverses. The common
  summand has shift `|i|`, and dotted identity summand `r` has shift `r|i|`.
- `OddMath/SKM/RouquierHom.lean` and `RouquierHomAdjunction.lean`: linear
  pre/postcomposition on full super Hom categories, signed transformations,
  the associator comparison, and both adjunctions with even components.
  These are not yet the content-shifted, weight-indexed coupled functors.
- `OddMath/SKM/RouquierBoundary.lean`: finite homogeneous dotted-unit
  coefficients, extraction from negative local inversion at a vacuum, the
  top-coefficient cap and a joint detection lemma for its dotted units.
- `OddMath/SKM/RouquierMate.lean`: `homMateEquiv_eq` identifies the actual
  cup–crossing–cap composite with the Hom equivalence, retaining odd crossings.
  `rouquierMate_slide` proves the unprojected identity
  `σ ≫ (x₂ ▷ F₂) - q • ((F₁ ◁ x₁) ≫ σ) = ε₁ ≫ η₂` from the upward slide,
  without assuming any inverse. Its sector projections still require the
  explicit content-shifted comparison maps of step 2.
- `OddMath/SKM/RouquierSchur.lean`: block LDU factorization and
  `isUnit_of_nilpotent_feedback` over an associative ring. This requires
  nilpotence of the whole feedback operator, never just of its entries.

The first fusion-specific equation still absent is the super analogue of
`Categorification/TwoRep/RouqCoproduct.lean`'s `rouqSig_eq`. In the convention
of §4, the projections of **one actual mate** must be identified with
`C = Σ_r q^r u_{A,r} v_{B,-r-1}` and
`D = -Σ_r q^(r+1) u_{B,-r-1} v_{A,r}`. The two factor unit/counit components
must both occur. The even proof's scalar-difference crossing is not the
homogeneous odd crossing (1), so its mate identity cannot simply be reused.

After this equation, the remaining comparison is not automatic: identify the
Schur reduction with the correct negative windows and dot-conjugated probe
inverses in every height-sign case, and prove the feedback belongs to a
nilpotent two-sided ideal. Only then can the associative lifting theorem
supply inversion and the cover-family assembly be replaced by an action of
the original superdatum. There is no A2 theorem in these modules, and no
counterexample to separated fusion is asserted.

### Exact mate controls and an occupied adjacent-colour slice

`scripts/Nondegeneracy/rouq_sig_super_check.py` computes the cup–crossing–cap
composite before extracting either coupling block. Its even control uses
ordinary cutoff-two nilHecke towers; its odd control uses the corresponding
odd towers. Induction is a balanced-tensor quotient and coinduction is a
constrained Hom space. The tests check both adjunction triangles, both upward
dot slides, crossing square, both finite expansions, the complete total
cup/cap matrix and its two-sided inverse. The feedback tested is the whole
operator `D r_A C r_B`, with `r_A,r_B` extracted from the factor inversion
matrices, including their dotted identity summands.

There is a necessary convention distinction, already specified in
[SeparatedFactorInversion](SeparatedFactorInversion.md): (2) describes
`sigma = -q sigma_src`. Thus for the literal `rouquierMate` the formulas are

    C_src = -sum_(r>=0) q^(r+1) u_A,r v_B,-r-1,
    D_src =  sum_(r>=0) q^r u_B,-r-1 v_A,r.

For odd colour these are exactly (2); for even colour both blocks change
sign. In the even control, if `a=(X-Y)^(-1)` is the raw source
position-preserving crossing, the crossing in the convention of
`RouqCoproduct.rouqSig_eq` is `delta=-a`: it satisfies
`delta (Y-X)=1`, exactly its inverse-difference hypothesis. Its mate is
therefore `-sigma_src`. The even control passes with this normalization.
No extra odd-bubble term is required in the tested cases.

An occupied connected slice uses the all-odd datum `[[2,-2],[-4,2]]` with
`Q_ij(x,y)=x²-y⁴`, reservoir cyclotomic polynomials `f_i=1`,
`f_j=y²+y delta_j`, and probe `f_i=t²-1` at zero j-content. Put
`R=Q<y,delta_j>/(delta_j²,y delta_j+delta_j y,y²+y delta_j)`.
Here `delta_j` and `y²` are nonzero, while `y³=0`. At reservoir content
`(a,1)`, every word except `j i^a` starts with i and is killed by `f_i=1`.
Consequently mixed crossings vanish, and their quadratic relation imposes
`x_1²=y⁴=0`. The surviving `jii` braid has unequal outer colours, hence zero
correction. Relations on killed words vanish with their idempotents. Sending
those idempotents and mixed crossings to zero gives the reverse presentation
map, identifying this slice with `R tensor_hat ONH_a/(x_1²)` for `a=0,1,2`.
The ideal `(x_1²)` here is two-sided. These identifications respect appending
an i-strand, so the induction, coinduction and their adjunctions transport.

The calculation transports the generators and recomputes their mate, rather
than tensoring a presumed mate formula. The additional occupied odd j strand
is retained through the component equivalence `G_(a,b)=Pi^b`; a homogeneous
map of parity p transports as `(-1)^(bp) P_R^p tensor f`. In particular the
B-sector functor has the extra parity line; it is not silently discarded.

Run `python3 scripts/Nondegeneracy/rouq_sig_super_check.py --all-contents
--connected` for all `a,b in {0,1,2}`. All nine even controls, nine odd
controls and nine occupied-j slice cases pass. The factor heights are
`h_A=2a-2`, `h_B=2-2b`, covering both signs of each factor and of their sum.
By default the script uses the graded projective generators `e_00 A_2` and
`e_00 B_2` in the matrix-algebra factors, retaining the entire local algebra
at the other levels. The connected total matrix sizes are 24, 32, 48, 64,
80 and 144. Retaining full regular modules with `--regular` also passed,
with total matrices up to size 192. Their whole
feedback operators vanish. The rank-one even middle-content feedback has
rank two and square zero; the odd coefficient-free feedback vanishes.
Separately, `--exterior` checks the rank-one middle content with nonzero
`delta_i`: the total matrix has size 72 and invertible total map, and the
feedback has rank four and square zero.

**Boundary of this evidence.** These are exact finite instances, not an
all-content multicolour comparison theorem. The connected slice has
`delta_i=0` and its mixed polynomial specializes to `x²`; it does not test
simultaneously independent `delta_i,delta_j`, other j-contents, or a mixed
crossing with nonzero polynomial contribution inside the reservoir. Such
contents may also have small matrices and have not been enumerated here.
A2 and the general comparison in this section therefore remain open.

**Further j-contents and exterior coefficients.** The script now builds each
coefficient superalgebra from a presentation and checks associativity on the
claimed basis. Besides the reservoir slice it treats the probe word `j i^b`
with probe `f_i=1`, `f_j=y'²-1`: there `Q_ij(x_1,y')=0` gives `x_1²=y'⁴=1`,
so the corner is `Q<y'>/(y'²-1) tensor_hat B_b` and the probe j strand gives no
parity twist. In the default run (under a minute) all nine contents of the even
and odd controls, of the reservoir slice and of the probe slice pass. With
`--heavy`, an odd j strand in both factors (coefficient dimension 8, total
matrices up to 288) passes at all nine contents, as do the `delta_i` exterior
reservoir at all nine contents and `delta_i` together with a nonzero odd
coefficient `delta_j`, with or without an occupied probe j strand. Throughout,
`C` and `D` equal (2) and the total map has a two-sided inverse; the whole
feedback is nilpotent, and is nonzero only at the middle exterior content.

Two limitations are structural. First, an exterior coefficient cannot deform an
invertible odd cyclotomic polynomial: in `Q<y,delta>/(delta²,y²+y delta-1)`,
`y·y²-y²·y=-2delta`, so `delta=0`. Hence `delta_i` and `delta_j` enter
nontrivially only through nilpotent reservoir polynomials, and an occupied
reservoir j strand needs `f_i=1`, which excludes `delta_i` there. Second, every
slice above is a base change of a single-colour model along a coefficient
superalgebra. Replacing the parity line `Pi^(jA b)` by `Pi^0` or `Pi^b` also
passes at contents `(0,1)`, `(1,0)` and `(1,1)`, so that line acts as a gauge
there. The computations therefore
confirm the corner presentations, not new crossing data. Contents with two j
strands in one factor, or a j strand beside nontrivial `f_i`, involve several
idempotents linked by mixed crossings. They need a genuine multicolour
cyclotomic quotient and remain untested.
