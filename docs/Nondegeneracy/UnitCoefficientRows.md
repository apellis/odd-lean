# Coefficient functionals from the prescribed unit inverse

This is the proposed attachment of the normalized coefficient-extraction
window in [SwappedVacuumNonpositiveBubbles, §2](SwappedVacuumNonpositiveBubbles.md)
to the existing arbitrary-module unit matrices. It supports research issue
#345 and the cap calculations in [InverseCapMoments](InverseCapMoments.md)
and [NegativeCapMoments](NegativeCapMoments.md). The declarations described
here still require scoped verification before their integration.

The producer and paired concrete consumer are unverified source. Separate
scoped checks of generic inversion, homogeneous components, source-shift
naturality and coordinate projection do not verify these old-module
declarations. No result in this note is promoted to an established
coefficient-functional attachment until those scoped checks pass.

Fix an old supermodule M, an old output word t, and a moving colour i at
nonnegative content height. Put m=contentUnitCount(i,t). The verified
`moduleUnitMatrixIso` has the literal ordinary-unit/dotted-unit entries
as its forward columns, in their prescribed shifted source coordinates.
For a coordinate a in Option(Fin m), take its inverse followed by the a-th
coordinate projection. These are `moduleUnitCoefficientRow`.

The two inverse products immediately give the full coordinate window:
the selected row is 1 on its own literal column and 0 on every other
column, including the mate coordinate at none. The inverse and coordinate
projection are even, so each row is even in the shifted coordinates.
Removing the r-th canonical source shift gives `moduleUnitCoefficient`.
Its parity is r*p_i. The existing `moduleUnitColumn_total` identity
then identifies its window with the chosen signed induction dot D and
ordinary adjunction unit u:

    lambda_r D^a u = [a=r],   0<=a<m.

This supplies a coefficient functional and its window; no functional,
basis, tensor-flatness or arbitrary-kernel evenness hypothesis is added.

## The coefficient sign

For a homogeneous old endomorphism f of t, whole-matrix output naturality
conjugates through the existing inverse. Coordinate projection commutes
with the finite-family action. The final canonical source-shift comparison
is supernatural of degree r*p_i. Consequently

    lambda_r target(f)=(-1)^(r*p_i*|f|) M(f)lambda_r.

`moduleUnitCoefficient_end_naturality` states this equality with its
literal source, target and coefficient order. At the empty word this is
the full exterior-coefficient superlinearity required by coefficient
extraction. It must not be replaced by unsigned A-linearity.

## Empty-word specialization

Let M be the old empty-word representable. Its append restriction is zero:
an appended word cannot have the content of the empty word. Inducing this
zero module is zero as well, by balanced-tensor generation. Thus the
mate-source part of the unit matrix vanishes on M; the other source
coordinates remain literal dotted units. At empty output, m=cutoff(i)=N.
For N>0 select r=N-1. The namespace `VacuumCoefficient` constructs this
`functional`, its parity (N-1)*p_i, and its exact extraction window

    lambda D^a u=[a=N-1],   0<=a<N.

For odd i, the signed-power identity and its odd coefficient rule give

    lambda(a t^(N-1))=(-1)^((N-1)|a|+binom(N-1,2)) a.

This is the normalization used in the written nonpositive-height bubble
calculation, with no additional cap rescaling. The ordinary old action on
the covariant empty representable is the left coefficient action in these
coordinates; its endomorphism composition conventions are retained.

## Boundary

The paired consumer uses connected mixed data and the actual empty-word
representable, checks both moving parities, zero finite count, selected
and off-diagonal column values, the literal signed dot window and an odd
coefficient-basis endomorphism. It also audits every owned declaration.

This attachment is to the old full-coefficient module matrices. It does
not yet construct the final swapped vacuum, match its normalized
adjunction, or compute the high-dot moments and entire bubble series.
The generic row construction applies to every old supermodule, so the
later truncated coefficient vacuum can use its actual pulled-back module;
no assertion of coefficient flatness is needed. Whole factor/action
comparisons remain separate.
