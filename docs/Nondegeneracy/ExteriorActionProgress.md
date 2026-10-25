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
