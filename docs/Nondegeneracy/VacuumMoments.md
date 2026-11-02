# One-strand moments of the constructed coefficient functional

This attaches the coefficient-extraction normalization in
[SwappedVacuumNonpositiveBubbles, §2](SwappedVacuumNonpositiveBubbles.md)
to the old full-coefficient vacuum. It uses the inverse rows constructed in
[UnitCoefficientRows](UnitCoefficientRows.md), the canonical upper-Hom
equivalence, and the actual old one-strand relation. The producer and paired
consumer pass scoped Lean checks with warnings as errors and both pinned
compatibility settings. All 15 owned declarations pass the standard axiom
allowlist audit; full CI remains the integration gate.

Write A for the full ELV coefficient quotient, N=cutoff(i)>0, p=p_i, and
lambda for the constructed top inverse row. Transport lambda through the
canonical balanced-induction/representable equivalence to obtain
`upperFunctional` on Old([i],[i]). Its target is literally Old([],[]).
Let e(a) denote the coefficient class at the empty identity.

For every old coefficient b, `upperFunctional_column` extracts the top
ordinary signed-dot column. The existing actual signed-power calculation
then gives `upperFunctional_output_window`: on the raw output-polynomial
column of exponent n<N, its value is

    (-1)^(binom(n,2)*p) [n=N-1] b.

Raw output-polynomial coefficients and coefficient-left one-strand
monomials differ. The signed box-product composition, applied before
quotienting, proves `output_monomial`: for homogeneous a of parity |a|,

    outputColumn_n(e(a))=(-1)^(|a|*n*p) [a t^n].

Consequently `coefficientMoment_window` proves the exact literal raw
coefficient window

    lambdaRaw([a t^n])
      =(-1)^(|a|*n*p+binom(n,2)*p) [n=N-1] e(a),  n<N.

For odd i, this is precisely equation (4) of the cited normalization.
Both the coefficient-order sign and the triangular dot-power sign remain
visible. The concrete consumer checks the odd coefficient at cutoff two
for both moving parities, its vanishing undotted value, and the nontrivial
triangular sign at odd cutoff three.

## Higher moments from the actual relation

Set mu(a,n)=lambdaRaw([a t^n]), implemented by `coefficientMoment`.
The actual old relation has ascending coefficients C_j=`singleCoefficient`:

    sum_(j=0)^N [a C_j t^(j+m)]=0,  C_N=1.

Applying the constructed linear functional proves
`coefficientMoment_recurrence`, with the original coefficient order.
Solving its monic last term proves `coefficientMoment_leading`:

    mu(a,N+m)=-sum_(j<N) mu(a C_j,j+m).

Every exponent on the right is smaller than N+m. Thus the actual relation
and the low coefficient window determine every higher raw moment; no
independent monic-basis or annihilating-polynomial assumption is added.
The concrete consumer also expands a higher moment at cutoff two, keeping
the actual coefficient products instead of specializing them away.

## Boundary

These results concern the literal old full-coefficient vacuum. They do
not identify a final swapped factor, impose the paper's even-generator
power ideal, or compute its bubble series. Converting the recurrence to
the normalized right-moment sequence used by the cap calculation still
requires the signed higher-dot comparison and coefficient-superlinearity
in those exact coordinates. These two attachments for the old vacuum are
provided by [VacuumSignedMoments](VacuumSignedMoments.md). Ordinary right
precomposition cannot be silently identified with the signed supernatural
dot.
