# Review of the deformed multicolour action

Status: **proposed mathematical review**, not a Lean construction of an action.
“Verified” below means that the indicated calculation or source comparison has
been checked on paper; it does not promote it to the Lean status in HANDOFF.

## Conclusion

The normality, balanced-ideal, norm and cap-row mechanisms survive this review.
The corrected odd intertwiner norm does **not** invalidate the cyclotomic
projectivity proof: the product occurring in that proof is not its square.
There remains a presentation-comparison gap before the consolidated manuscript
can be called a proof of an action of the specified SKM presentation. In
particular, signed right multiplication on induction bimodules is a
super-opposite representation, not an unsigned representation of the upward
algebra. The existence of the quotient algebras, or of abstract decompositions
of functors, does not discharge this comparison.

The conclusions below concern homogeneous KKO parameters, finite colour set,
symmetrizable compatible datum, and an even base with 2 invertible. They do not
extend the action to arbitrary parameters of the abstract BE2 presentation.

## Sources and conventions

The editions compared are KKO I, arXiv:1206.5933v2, §§7–9; KKO II,
arXiv:1303.1916v2, subsection “Cyclotomic quotients”; ELV,
arXiv:2203.14153v2, §4.6, Theorem 4.5 and (4.15)–(4.16); BE2,
arXiv:1701.04133v2, its generating presentation and Proposition 3.5.
For the polynomial-projectivity step, Kang–Kashiwara,
arXiv:1102.4677v4, Lemmas 4.18–4.19 were also compared.

KKO I uses restriction for E and induction for F. The manuscript uses induction
for E, restriction for F, and weight −Λ+β. ELV uses the latter convention in
rank one. KKO II explicitly puts the induction endomorphism representation in
`End(... )^sop`, whereas the restriction representation has ordinary target.
These are substantive conventions, not merely changes to the letters E and F.

## Step 1: affine algebra and first-dot normality — verified

Super tensor extension of the affine PBW decomposition is legitimate: its
basis gives an explicit free module decomposition before extension. No
flatness of a subsequent cyclotomic quotient is inferred from this fact.
At an odd colour and even cutoff, write

`f=C(x²)−xd q(x²)`, `C(z)=χ_m+zq(z)`.

Using `xd=−dx`, `d²=0`, and `dχ_m=0`, one obtains

`xf=f(x−2d)`, `af=fa` for coefficient elements a.

Thus the automorphism ν fixes coefficients and sends x to x−2d; it preserves
x² and f. The whole polynomial is even, so distant supercommutations have
uniform signs, including across independent odd parameters of other colours.

**Repair retained:** the domain of right multiplication by f is twisted by
ν inverse, hence its right dot is x+2d. It is not x−2d. Already
`f=x²−xd`, with χ_m specialized to zero, has `xf−fx=−2x²d`.
KKO's original first-dot commutation cannot be imported. The shifted identity
in ELV (4.16) agrees with this repair once the source action is distinguished
from the formula for P on the unchanged underlying module.

## Step 2: P, balance, and the cyclotomic ideal — verified with qualifications

The final section of MulticolourCyclotomicAction supplies the relevant
extension of KKO I (8.3)–(8.5). Let `T=τ₁…τ_n`, and work in the quotient by
`J=H a(x₁) R(β)e(β,i)`. For even N_i, `f_i T` has parity p(i)p(β).
The balance identity is checked idempotentwise, not by declaring the sum of
all differently coloured cyclotomic polynomials central.

* An old dot slides across T. A nonzero correction deletes precisely its
  matching-i crossing. The remaining prefix takes that old i to the first
  position, so the polynomial there is an old cyclotomic relation.
* An old crossing slides through T by one braid move. Its correction requires
  the two outside colours to agree. In this configuration that says that the
  relevant old colour is i. Separate the two distant crossing blocks. Move
  the correction polynomial's dot monomials to the adjacent outside factors;
  the shortened prefix again exposes an old cyclotomic relation. No crossing
  through that polynomial is being treated as an error-free dot slide.
* A coefficient c contributes exactly `(-1)^(|c| p(i)p(β))`. The parity
  involution must act on the coefficient algebra as well as on affine
  generators. Applying it only to the affine factor is wrong.

Normality handles first-dot multipliers; distant supercommutation handles the
remaining generators. This gives the extension of Lemma 8.2's ideal sum and
identifies im(P) with the kernel of the final quotient. At this point the
sequence is only right exact. Neither injectivity nor projectivity follows
from the ideal calculation alone. The argument for the distinct-colour
corner in §9.1 likewise survives: the additional double-crossing term has
equal endpoint colours and contributes nothing to a mixed corner.

## Step 3: Q and QP — verified; distinguish three different products

KKO I defines φ and `g=(y²−x²)φ` at a repeated odd colour. With
`Δ=y²−x²` and `S=x²+y²`, the relevant distinctions are:

* `g²=−Δ² S`, the odd intertwiner-variant square;
* the coefficient of the longest crossing in g is `−Δ²`;
* the repeated-colour factor in the quotient identity for QP is S.

Accordingly, the product `G_i(t²)` in `QP=f_i(t)G_i(t²)` contains
`x_a²+t²`, not `−(t²−x_a²)²(x_a²+t²)` for every repeated i. The additional
squared differences belong to the leading-crossing extraction used later
for Proposition 9.3. Replacing either product by the other changes its degree
and destroys that proposition's height count. Generic invertibility of g
would require both Δ and S invertible; injectivity of the monic QP operator
requires no such localization.

Q is balanced by the affine intertwiner transport, with its codomain parity
shift. For the repeated-colour induction, transport sends an odd dot and an
odd coefficient through the same sign, so the even product xd is preserved.
Thus the transported relation is the full f_i, not its reduction d_i=0.
The cancellations in the proof of KKO I Theorem 8.5 are in the first-dot
polynomial projective modules. Their leading coefficients are units;
exterior zero divisors do not obstruct these cancellations. This is not
cancellation in the final cyclotomic algebra, where dots can be zero divisors.

## Step 4: projectivity — repaired argument is valid

Use `s=t²` at an odd colour. The conjugate product

`(C(x²)+xd q(x²)) f(x)=C(x²)²`

supplies an even monic square-annihilator, before any use of PQ. The
propagation argument of KKO I Lemma 7.3 uses the affine relations and even
square polynomials and therefore survives super coefficient extension.
For finitely many colours their first-position annihilators can be multiplied
to give a common monic polynomial with central even coefficients.

P commutes with s, despite failing to commute with t. Restriction from the
skew polynomial extension to B[s] preserves projectivity: that extension is
free on 1,t. Consequently the exact sequence supplied by Steps 2–3 is a
projective resolution of length one over B[s]. Kang–Kashiwara Lemma 4.18 now
applies to the central monic s-annihilator. Its central-coefficient hypothesis
must be stated; a merely monic annihilator with noncentral coefficients is
not the lemma that was read.

Opposite-side projectivity uses ordinary algebra reversal and the opposite
coefficient algebra. Reversal sends xd to d^op x^op, so the displayed
polynomial has parameter −d^op. This differs from the super-opposite used
for natural transformations in Step 7. An anti-involution fixing d without
this sign does not establish the claim.

## Step 5: companion norm — verified

The translation fixes t² and td_i, hence the norm A_i=f_i(t)G_i(t²).
The commuting square follows from semilinearity, not centrality. Therefore
`PQ−A₀` vanishes on im(P) and factors through coker(P). It is B[s]-linear.
A central monic s-polynomial annihilates the cokernel and acts injectively
on K₀, so the factor is zero. This is the mechanism of
Kang–Kashiwara Lemma 4.19. It neither presupposes projectivity of the
cyclotomic quotient nor requires the deformed f_i to commute with t.

## Step 6: monicity and cap conversion — verified conditional on the diagram

The relevant dependency is the exact Mackey diagram, not a dimension count.
The filtered defect has degree less than the degree of the multiplying
polynomial. Iterating its one-step version is valid by

`D(y,gh)=D(yg,h)+D(y,g)σ(h)`.

The norm identity and the monic, translation-fixed squared-difference product
then give degree `a+k` with unit leading coefficient, or zero for `a+k<0`.
One must retain the order of the factors; centrality of f_i is unnecessary.

The negative-height calculation in CoupledBubbleEvaluation has the correct
sign. In KKO's tensor conventions,

`X(a⊗πb)=−ax⊗πφ(b)`, `D(a⊗πb)=a⊗π(bd_i)`,
`E(a⊗πb)=aφ(b)`.

Consequently `XD=−DX`, `D²=0`, and `ED=−R_d E`. For `Y=X−2D`,

`EY^(2r)=EX^(2r)`,
`EY^(2r+1)=EX^(2r+1)+2R_d EX^(2r)`.

The plus sign in the second formula is essential. The row operation is
`1+N`, with N supported from even rows to the following odd rows, so N²=0
and inverse `1−N`. The coefficient is odd and the adjacent summands differ
in parity; this is a homogeneous row automorphism after the shifts. The
existing `SKM.OddDotTranslation.kko_cap_rows` and related lemmas concern
these operator identities, not the existence of the cyclotomic diagram.

**Remaining qualification:** the diagram and its arrows must be constructed
as the balanced modules of Steps 2–5. ELV proves this in rank one; it does
not supply the multicolour diagram by citation. The proposed extension is
compatible with its recurrence, but no corresponding Lean diagram exists.

## Step 7: the specified SKM action — gap in the presentation comparison

Adjunction on all modules is verified by tensor insertion and multiplication;
Step 4 permits restriction to projectives. It is also legitimate to obtain
inverse generators from a proved invertible matrix rather than choosing new
cups and caps. However, the phrase “standard affine dot and crossing maps”
does not yet specify a comparison with the given upward presentation.

For a homogeneous right multiplier u, the left-superlinear operator is
`R̃_u(h)=(-1)^(|u||h|)hu`. Its composites satisfy

`R̃_u ∘ R̃_v = (-1)^(|u||v|) R̃_(vu)`.

KKO II explicitly records this super-opposite target. ELV §4.6 uses
`h↦φ(h)x` for the dot and **`h↦−φ(h)τ`** for the crossing in rank one.
Thus an unsigned assignment of both generators by the same right-multiplier
rule is not justified. A complete multicolour comparison must specify the
word reversal, crossing factors for each colour pair, and the induced
polynomial parameters, then check the mate matrix including its sign at
height zero. Rank-one sign checking alone does not check mixed crossing
squares or braid corrections for the chosen homogeneous parameters.

This is a precise missing comparison, not a counterexample to the existence
of a deformed action. BE2 Proposition 3.5 provides a signed super-opposite
symmetry that may be used, but applying it requires keeping its crossing
factor `−(-1)^(p(i)p(j))` and its adjunction conventions. Ordinary diagram
reversal from Step 4 is not a substitute.

## Boundary of the conclusion

Neither this review nor KKO II's Grothendieck-group supercategorification
asserts detection of abstract exterior bubble generators. ELV Theorem 4.5
provides rank-one existence; its later universal-equivalence argument must
not be reused to infer the multicolour nondegeneracy being sought. The next
action deliverable is the explicit presentation comparison and its smallest
mixed-colour consumers, followed by the balanced all-content diagram in Lean.
