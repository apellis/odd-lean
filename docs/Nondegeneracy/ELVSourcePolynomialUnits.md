# Contentwise source polynomial units

The distinct-colour step of BE2 (1.11), recorded in
SwappedDistinctMixedMates (13)–(15), requires invertibility of each source
polynomial `c • A^n + N`. Here `c` is a scalar unit and `N` is any
admissible linear combination of monomials with positive reservoir-dot
power. It does not require one nilpotence exponent on the complete
original-weight category.

`ELVMixedSourcePolynomialUnits` assembles these polynomial units over the
actual product of ELV content module categories. Total evaluation of
supernatural endomorphisms is an algebra map, so every ordered monomial
and every linear combination is preserved. The pre-dot remains a unit
at each component. The positive post-dot remainder is nilpotent there,
and its commutation with the pre-dot gives the polynomial unit. The
evenness of the entire polynomial allows these component inverses to
assemble into an inverse of the whole input Hom functor.

The reservoir input is the literal right transpose of a positive power
of the chosen ELV induction dot. The signed transpose-power identity and
the existing source-content transpose bound prove its componentwise
nilpotence. The exponent can vary with the source content. The
surrounding Hom functor and its specified parity shift remain in place.

`ELVProbeSourcePolynomialUnits` specializes the pre-dot to the even power
of the prescribed invertible OLD probe dot. Odd colours use exponent two;
even colours use exponent one. The resulting
`elvProbeMixedPostSourceUnits` supplies the existing source-polynomial
criterion for every pair of colours, every original weight, every Hom
functor, and every admissible remainder. The distinct-colour sideways
crossing wrapper applies the generic source-unit inversion theorem.
No global reservoir nilpotence assumption is added.

The scoped strict producer and paired consumer checks pass with warnings
as errors and the pinned compatibility options. The consumer specializes
both mixed-parity and all-odd parameter data, retains nonzero probe
append vectors at both colours, applies the criterion to arbitrary units
and leading degrees with a positive post-dot monomial, and applies the
literal distinct-colour crossing wrapper. All 25 declarations owned by
the two generic source-unit modules and two ELV producer modules use only `propext`, `Classical.choice` and
`Quot.sound`.
