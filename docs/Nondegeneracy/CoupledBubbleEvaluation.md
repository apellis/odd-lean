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

The finite odd-bubble result makes a zero coefficient less likely to be the
first obstruction, but does not yet establish the full convolution law.
The next calculation is the sequence `v x^(2r−1) σ⁻¹u` on the same object,
followed by a reservoir with a nonzero independent even parameter. The current
small reservoir alone cannot demonstrate independence of all even variables.
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
