# Exterior coefficients: a same-factor obstruction and surviving route

## Verified obstruction

The separating-action construction must distinguish an abstract coefficient
specialization from a cyclotomic action realizing it. Ebert–Lauda–Vera,
*Derived superequivalences for spin symmetric groups and odd sl2-categorifications*,
[arXiv:2203.14153v2](https://arxiv.org/abs/2203.14153), §3.5 (3.24), use the following coefficient algebra after specializing their
base field to Q:

\[
 A_n=\mathbb Q[\chi_1,\ldots,\chi_{\lfloor n/2\rfloor}]\otimes\Lambda(d)
 /(d\chi_{n/2}\text{ if }n\text{ is even}),
 \qquad |d|=1,\quad |\chi_r|=2r.
\]

Here the displayed degrees are integer degrees, and d is odd while the chi's
are even. Write c_(2r)=chi_r and c_(2r+1)=d chi_r. Their monic-up-to-sign
cyclotomic polynomial is a^n(t)=sum_(l=0)^n (-1)^l t^l c_(n-l).
For n=2m its constant coefficient is chi_m. Localizing this coefficient
forces d=0. It is the constant coefficient, not the monic leading coefficient,
that matters. For odd n the constant coefficient is odd and square-zero,
so it cannot be inverted in a nonzero ring.

This is also an elementary consequence of the defining polynomial, rather
than an accidental feature of the coefficient presentation. In any ring,
assume delta^2=0, delta x=-x delta, and q commutes with x and delta. If

\[
 x^2q+x\delta q=b,\qquad xb=bx,
\]

then commuting this equation with x gives 2x^2 delta q=0; multiplying
it by delta gives b delta=x^2 delta q. Hence 2b delta=0. A left inverse
of 2b forces delta=0. The Lean module
`OddMath/Diagrams/OddNilHecke/CyclotomicExteriorObstruction.lean` checks this
statement for arbitrary rings, its degree-two specialization q=1, and the
left-inverse cancellation corollary. For the even ELV polynomial take
q=sum_(r=0)^(m-1) x^(2r) chi_(m-r-1), delta=-d and b=-chi_m.

## Consequence for the research program

A single ELV cyclotomic factor cannot simultaneously provide invertible
constant coefficient and a nonzero odd exterior coefficient over Q. Thus
an abstract unit-cutoff coefficient map does not itself construct the
required faithful categorical action. This does not refute that abstract
map, nor does it prohibit invertible odd elements in general superalgebras.

A two-factor construction remains viable: retain the odd parameter in a
nilpotent-dot factor and use a distinct factor for the invertible-dot
probe. At even cutoff n the additional coefficient relation has degree
n+1. It therefore disappears from every fixed bounded-degree window as
n grows, provided the action has the required PBW freeness and compatible
bubble evaluation. See `UpwardSeparation.md` for the bounded-separation
criterion and `OddUnfurling.md` for the spectral hybrid proposal.

The existing `ExteriorDeformation.lean` already checks a nonzero degree-two
nilpotent reservoir. The rational-matrix extension `scripts/Nondegeneracy/nonvacuum_exterior.py`
checks that reservoir at all three A levels, of dimensions 2, 4, 8, alongside
the separate B tower of dimensions 1, 2, 4. Its default local checks pass.
The slower `--action` checks also passed: both adjunction triangles on the
eight-dimensional regular input, and all four tested upward-relation
blocks (dimensions 32, 32, 64, 16). The labels 0 and 1 here distinguish
the two factors of one colour, not two distinct root colours. The `--full` calculation now completes using sparse Kronecker products. The
actual mate matrix has size 72 by 72, rank 72 and determinant 1; both inverse
identities pass. Its central block has size 32 by 32 and determinant 1.
The off-diagonal blocks have rank 10 each, and the Schur feedback is genuinely
nonzero of rank 4 but square-zero. Thus H=1-feedback has inverse 1+feedback.
All mate blocks pass odd-parity and right-linearity checks, homogeneous
supernaturality passes, and the two actual diagonal mates equal the ordered
finite dotted expansions. The pure-right mate has size 8 and determinant 1.

There is also an actual categorical coefficient check. At total weight zero,
form U by summing the adjunction units into the diagonal FE branches, and V
by summing the counits from the diagonal EF branches. With the normalization
in `MoreGenerators.etaP`, `eq_2_12_a` and `Bubbles.oddBubble`, the odd bubble is

\[
 V\sigma^{-1}U=-L_\delta.
\]

This matrix identity is checked exactly: its rank is 4 and its square is zero.
It agrees with the source parameter d=-delta and establishes that this odd
parameter is realized by an actual coupled bubble, not merely added as a
spectator coefficient. The feedback also has image inside the reservoir
exterior image and annihilates that image; both assertions are checked.
They explain its square-zero property structurally: any endomorphism F with
im(F) contained in im(D) and F D=0 satisfies F^2=0. This is the elementary
lifting mechanism available when reduction modulo a square-zero coefficient
recovers the zero-feedback model.

The concrete consumer `scripts/NonVacuity/CyclotomicExteriorObstruction.lean`
applies the obstruction theorem to the existing nonzero dual-number exterior
model at b=0. It and the new module pass Lean with warnings as errors. All
three new theorem declarations depend only on `propext`, as checked by
`#print axioms`.

These finite one-colour checks do not supply colour-specific exterior generators,
mixed-colour braid coherence, or a faithful full-SYM bubble map. Those are
still genuine missing construction tasks; tensoring spectators onto an
action does not establish that categorical bubbles realize them.

## Two actual bubble composites and higher moments

`two_colour_exterior.py` reconstructs the rank-one mate inverse, then takes
its supertensor lifts for two independent slots. Both normalized bubbles
are computed as lifted V, inverse sigma and U composites. On the 64-dimensional
product object the bubbles have rank 32 each, their product has rank 16,
and their squares and anticommutator vanish. This is a genuine pair of
bubble composites rather than two adjoined spectator scalars. It does not
by itself attach the mixed-colour KLR crossings to these adjunctions.

For the original eight-dimensional object, let B_r=V X^r sigma^-1 U and
z=x delta. Exact coefficient calculations give

- B_0=-delta;
- B_1=2-3z;
- B_(2r)=-2delta for r>=1;
- B_(2r+1)=2-6z for r>=1.

These are equalities of left-multiplication matrices, not just their values
on one vector. The matrix identity X^5 sigma^-1 U=X^3 sigma^-1 U certifies
the tail for all r, so the normalized moment series is

\[
1+\sum_{r\geq0}B_rt^{r+1}
=(1-\delta t)(1-3x\delta t^2)\frac{1+t^2}{1-t^2}.
\]

Quotienting the nilpotent reservoir by x=0 preserves delta and removes the
x delta correction. The resulting series is
(1-delta t)(1+t²)/(1-t²): the nonvacuum probe contributes a rational factor.
The odd coefficients equal the odd bubble times the preceding even
coefficient, and the even coefficients commute. This is a finite
specialization of the bubble coefficients, not full-SYM injectivity.

## Higher cutoffs retain joint coefficient/operator information

`higher_exterior_reservoir.py` constructs a two-strand odd polynomial module
with nonzero exterior coefficient at even cutoffs N=2,4,6. In the skew
polynomial ring on odd x,y,delta, it quotients by the **left** ideal generated
by f_N=x^N+x^(N-1)delta and its odd divided difference g_N. It explicitly
checks that multiplication and divided difference preserve the relation
spaces; this is not a guessed quotient action. The final two homogeneous
pieces vanish, so the degree truncation introduces no artificial boundary.

The module dimensions are 4,24,60; the exterior operator has rank 2,12,30.
All odd nilHecke, supercentral-exterior and cyclotomic relations pass.
The rectangular operator families

\[
 X^aY^b\tau^w\delta^e,
 \quad 0\leq a<N,\quad 0\leq b<N-1,\quad w,e\in\{0,1\},
\]

have full ranks 8,48,120 respectively. In particular they simultaneously
detect dots, crossings and the exterior coefficient through total
coefficient-plus-dot degree N-2 in each tested model. Conversely g_N tau=0
is an actual relation of degree N-1. At N=2 this is
(X-Y+delta)tau=0, explaining why the smallest reservoir loses some
operator/coefficient combinations despite its nonzero bubble.

`CyclotomicCutoffKernel.lean` proves the cutoff relation for every N in an
arbitrary ring from the dot-slide, crossing-square-zero, exterior
anticommutation and cyclotomic relations. Its proof uses the recurrence
G_0=0, G_(n+1)=x^n-yG_n and the identity
 tau x^n=G_n+(-y)^n tau. This generic negative-boundary statement is separate
from the finite computational independence evidence. A native all-N rectangular
basis proof and the coupled higher-cutoff inversion remain open. The
all-cutoff algebraic basis is available as a published input below.

### Published all-cutoff basis input

ELV Theorem 5.9 and Remark 5.10 give an A_N-supermodule basis of the deformed
cyclotomic odd nilHecke algebra. Set k=ell=m in their notation (m is strand
count, N is cutoff). The corner idempotents become identities, Y_(m,m)=X_m,
and the basis is x^a tau_w with a_i<=N-i and w in S_m. Base change
chi_r=0, d=-delta retains this basis over the exterior algebra. Thus the
all-cutoff algebraic independence underlying the finite experiments is
already published; no new all-N Groebner theorem is needed. Retaining the
full coefficient ring A_N instead gives simultaneous even and odd source
parameters, subject to the high-degree relation d chi_(N/2)=0 at even N.
This statement does not identify the whole left-ideal polynomial model
with the published categorical action without further comparison.

### An actual even/odd vacuum coefficient detector

`vacuum_even_exterior.py` retains an independent even square-zero parameter
at cutoff four. Set B=Q[epsilon]/epsilon² tensor Lambda(delta), with
chi1=epsilon, chi2=0, d=-delta, and

\[
 f_4=x^4+x^3\delta+x^2\epsilon+x\delta\epsilon.
\]

The resulting sixteen-dimensional algebra A1 is associative and free of
rank four over B. The dotted cups 1,x,x²,x³ give an actual boundary inversion
map from four parity-shifted copies of B to A1. Its final inverse row is the
odd trace selecting the x³ coefficient. The Frobenius comparison
 a |-> (b |-> trace(ab)) identifies A1 with Hom_B(A1,B): both injectivity and
the entire Hom dimension are checked, together with right module actions.

At weight -4 the native bubble conventions give

- oddBubble = trace(x⁴) = -delta;
- beta(e1) = -trace(x⁵) = epsilon;
- beta(delta e1) = -trace(x⁶) = -delta epsilon.

The mixed operator has rank one, and 1, oddBubble, beta(e1), and their product
are linearly independent as operators on B. This detects an even parameter
and its product with the actual odd bubble, rather than only a nonzero
exterior scalar. It is a finite boundary/Frobenius realization; the script
does not assert a complete higher-cutoff or multicolour categorical action.
