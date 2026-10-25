# Coupled bubble evaluation: source normalization and a finite calculation

Research progress, 2026-10-25. This separates a native diagrammatic identity,
a checked finite action calculation, and the remaining general coupling law.

## A native formula for the coefficient being tested

For an odd colour at height zero, write `σ:EF→FE` for the source rightward
mate, `u:Id→FE` for the right cup and `v:EF→Id` for the right cap. BE2 (2.12)
gives `lcross=−σ⁻¹`; (2.10) gives `η′=−c lcross u`. Consequently the normalized
odd bubble is exactly

\[
\beta(\delta)=v\sigma^{-1}u.
\]

Both minus signs cancel. There is no residual choice of `c` and no extra
content-parity sign. `OddMath/SKM/CoupledBubbleEvaluation.lean`, theorem
`oddBubble_zero_inverse_mate`, proves this in the repository's presented SKM
category, given the one inverse equation it uses. Its concrete source
consumer is `scripts/NonVacuity/CoupledBubbleEvaluation.lean`.

The native theorem `normalized_bubL_zero_inverse_mate` proves the same
identity for every nonnegative dot number. Unfolding `betaDGen` therefore
identifies the higher normalized elementary bubbles at height zero as
`v x^(2r−1) σ⁻¹ u` for the one-based even generator `e_r`, `r≥1`.
Here the dot is on the E leg of EF, immediately before the cap. This proves
which source coefficient to compute, not its value in any proposed action.

## A surviving odd coefficient in the actual coupled model

The action stream's `nonvacuum_exterior.py` computes the separated two-factor
model at content `(1,1)`, with total height zero. The source mate is a 72 by
72 invertible matrix. Using its actual inverse and actual adjunction cup/cap,
the above coefficient is **minus left multiplication by the reservoir's
nonzero exterior element**. The resulting endomorphism has rank four on the
eight-dimensional regular test object. Thus this finite coupling does not
kill the odd bubble. In the source deformation convention `d=−δ_res`, it
realizes exactly `d`.

The associated feedback has rank four and square zero, and is nonzero; this
is a test of the nilpotent correction, not merely the undeformed matrix.
These results are exact rational-matrix checks, not Lean proofs of a general
action, and the two factors have one root colour. They do not address the
mixed-colour reservoir problem or full bubble independence.

### An all-order series on that same coupled object

Write `x` for the reservoir dot and `δ` for its exterior coefficient, so
`x²=−xδ`, `δ²=0`, and `xδ=−δx`. The action stream has now computed the dotted
moments `B_r=V X^r σ⁻¹ U` as actual matrices, not chosen scalar values. Their
first values, interpreted as left-multiplication endomorphisms, are

\[
B_0=-\delta,\quad B_1=2-3x\delta,\quad B_2=-2\delta,
\quad B_3=2-6x\delta,\quad B_4=-2\delta.
\]

The exact matrix identity `X⁵ σ⁻¹U=X³ σ⁻¹U` proves the recurrence for every
higher moment. Together with these initial values it establishes

\[
1+\sum_{r\geq0} B_r T^{r+1}
 =(1-\delta T)(1-3x\delta T^2)\frac{1+T^2}{1-T^2}.
\]

Thus the full moment family is genuinely an ordered coefficient series for
this finite coupled action. The nilpotent term `−3xδ` is visible before
coefficient extraction; dropping it prematurely would give an incorrect
categorical bubble value.

There is an actual algebra quotient sending `x↦0` and retaining the independent
reservoir `δ` and probe Clifford generator `y`, `y²=1`. It respects the displayed
reservoir relations and the super tensor signs. On the bubble values the
quotient gives

\[
C(T)=(1-\delta T)P(T^2),\qquad P(Z)=\frac{1+Z}{1-Z}.
\]

This is a **computed rational even-probe law** in the current small model,
with a fixed probe series and nonzero odd coefficient. The reservoir has no
independent positive even coefficient after this extraction, so this example
does not prove a general triangular change of the full polynomial bubble
algebra. The script also tests the product of the two actual odd-bubble
composites on a super tensor product; this retains two independent exterior
coefficients, but still does not construct a connected two-root action.

### A higher reservoir detects an even coefficient and its odd product

The separate `vacuum_even_exterior.py` calculation uses cyclotomic degree
four over `B=Q[ε]/(ε²) ⊗ Λ(δ)`, with

\[
f(x)=x^4+x^3\delta+x^2\varepsilon+x\delta\varepsilon.
\]

It constructs the 16-dimensional algebra and its actual vacuum dotted-cup
inversion. The odd Frobenius trace selects the coefficient of `x³`, and the
associated map to `Hom_B(A,B)` is checked to be an isomorphism. At source
height `−4`, native `oddBubble`, `betaD_h` and `betaD_dh` give the normalized
images as `tr(x⁴)`, `−tr(x⁵)`, `−tr(x⁶)`, respectively. The computation gives

\[
\delta_{\mathrm{source}}\mapsto-\delta,\qquad
e_1\mapsto\varepsilon,\qquad
\delta_{\mathrm{source}}e_1\mapsto-\delta\varepsilon.
\]

The four images of `1, δ_source, e_1, δ_source e_1` are linearly independent.
This is a stronger finite **reservoir** detector than the degree-two model:
an even parameter and its odd product both survive normalized categorical
evaluation. It does not yet couple this larger reservoir to an invertible
probe, establish every tower level, or prove arbitrary-cutoff separation.

## An ordered generating-series identity already inside BK

In Brundan–Kleshchev, [arXiv:2203.14149](https://arxiv.org/pdf/2203.14149),
use (13.28) with `n` replaced by `n−1`, and normalize by (13.12). For
`k=n−n′≥0`, the sign of summand `s` becomes

\[
(-1)^{(k+1)r+(n'+1)r+ns+\binom{s}{2}}
 =(-1)^{n(r-s)+\binom{s}{2}}.
\]

Writing

\[
A_j=(-1)^{nj}(\psi_n^\ell)^{-1}(\bar\varepsilon_j^{(n')}),
\qquad P_s=(-1)^{\binom{s}{2}}\bar\eta_s^{(n)},
\]

the normalized coefficient is `C_r=Σ_(s=0)^r A_(r−s)P_s`. Thus
`C(T)=A(T)P(T)` with this product order and central formal variable `T`.
No odd factors were interchanged in the sign simplification. This is a
factorization **inside BK's Grassmannian bimodule model**, not a proof that
an external nilpotent/invertible tensor coupling obeys that formula. Also
`ψ_n` need not act as a scalar extension of one independent external factor.

## What an even probe would imply algebraically

Suppose an actual coupled action, with its normalized cups and caps, supplies
an ordered law with a fixed purely even probe series `P(Z)`, `P(0)=1`, and
reservoir elementary series `E(Z)`. In rank one write the reservoir full
coefficient series as

\[
A(T)=(1+\delta T)E(T^2),\qquad
C(T)=A(T)P(T^2).
\]

Then `C_1=δ`, and its even coefficients obey

\[
C_{2r}=e_r+\sum_{s=1}^r e_{r-s}p_s,\qquad e_0=p_0=1.
\]

This transformation is unipotent triangular over the fixed probe algebra.
Its inverse is the finite recursive formula
`e_r=C_(2r)−Σ_(s=1)^r e_(r−s)p_s`. The same computation with a fixed sign
unit `δ↦−δ` remains invertible. For several colours, independently retained
exterior variables then give the product of the corresponding sign units on
every exterior monomial; no product `δ_iδ_j` is lost by this algebraic map.

The theorem `bubble_convolution_right_cancel_upto` checks finite-window
injectivity of right multiplication by a fixed series with constant term one
in **any ring**, without a domain or commutativity assumption. It is the
consumer of a categorical formula, not a replacement for constructing it.
If `P` depends on the unknown reservoir variables, this cancellation theorem
does not compare two substitutions with different `P`; the fixed-probe
hypothesis is essential.

## What still has to be proved

The finite series calculation establishes a coupling law for this specific
object, but does not yet establish the general convolution law. The next
calculation needs a reservoir with a nonzero independent even parameter.
The current small reservoir alone cannot demonstrate independence of all even variables.
The general law must then be proved from the actual block inverse, including
its nilpotent feedback, rather than inferred from BK's internal factorization.

Changing an adjunction by a compatible gauge does not add coefficients:
if `u'=B u`, `v'=v A⁻¹`, and `σ'=BσA⁻¹`, then
`v'(σ')⁻¹u'=vσ⁻¹u`. Hence a proposed Frobenius-trace deformation by a unit such
as `1+δx` must do more than coherently rescale adjunction data. The source
inversion fixes the other adjunction, so its normalization cannot simply be
assigned independently to manufacture a desired bubble value.

Finally, keeping every odd colour's reservoir at zero leaves their
mixed-colour interactions intact whenever `Q_ij(0,0)=0`. Generic nonzero
Clifford probes do not eliminate that construction task. A full proof still
needs a multi-colour reservoir action and verification of its coupling to
the probes.
