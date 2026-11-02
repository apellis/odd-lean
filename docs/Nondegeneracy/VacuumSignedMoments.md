# Signed higher moments of the old vacuum

This supplies the higher signed-dot comparison used in
[SwappedVacuumNonpositiveBubbles, §2](SwappedVacuumNonpositiveBubbles.md).
It follows [VacuumMoments](VacuumMoments.md), retaining the actual ordinary
adjunction unit, actual induction dot and prescribed inverse row. The
producer and paired concrete consumer pass scoped Lean checks with warnings
as errors and both pinned compatibility settings. All 10 owned declarations
pass the standard axiom allowlist audit. Full CI remains the integration
gate.

Let N=cutoff(i)>0, p=p_i and r=N-1. Write e(a) for the coefficient class
at the empty word, and mu(a,n) for the coefficient-left raw moment of the
preceding note. Define the literal signed moment

    s(a,n)=lambda D^n u(e(a)).

For homogeneous a, `signedMoment_coefficientMoment` proves at every n

    s(a,n)=(-1)^(binom(n,2)*p+n*p*|a|) mu(a,n).

`coefficientMoment_signedMoment` proves its inverse. The proof transports
through the canonical upper-Hom equivalence and uses the existing actual
signed-power calculation, together with the raw output-monomial comparison.
It does not identify ordinary right precomposition with the signed dot.

## Full coefficient rule

`functional_end_naturality` specializes the previously constructed inverse
row's naturality. The canonical upper-Hom inverse is even and natural;
`upperFunctional_end_naturality` transports that exact rule. Applying it
to the actual coefficient endomorphism and a raw dot monomial proves
`coefficientMoment_coefficient`:

    mu(a,n)=(-1)^(r*p*|a|) (mu(1,n) composed with e(a)).

The composition is the literal empty-word category composition, which
retains the full coefficient order. This is the signed A-linearity of
the coefficient functional required in the written moment calculation,
at all exponents rather than only in its initial window.

## Actual signed recurrence

The actual monic relation has ascending coefficients C_j, j=0,...,N,
whose proved parity is (N-j)*p. The raw recurrence and the inverse signed
comparison give `signedMoment_recurrence`:

    sum_(j=0)^N
      (-1)^((N-j)*(j+m)*p+binom(j+m,2)*p) s(C_j,j+m)=0.

All terms use the constructed signed-dot maps. There is no separate
annihilating-polynomial assumption, no arbitrary coefficient extractor,
and no replacement of the odd coefficient action by unsigned A-linearity.
The concrete consumer checks cutoff-two odd coefficients at n=2 and n=3
(where the two odd signs cancel), the even moving colour, the high-moment
coefficient rule, and the actual relation at a nonzero exponent shift.

## Boundary

This completes these signed-power and coefficient-rule attachments for
the old full-coefficient vacuum. The final swapped factor, the specific
even-generator power quotient and normalized mixed caps remain separate.
The cap-polynomial arguments still need their actual probe relation and
mixed slide instantiated on that action before the whole bubble series
can be claimed.
