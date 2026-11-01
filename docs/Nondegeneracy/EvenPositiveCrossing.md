# Even positive-height augmented crossing

The nonnegative-height matrix in DeformedRouquierMatrix, section 4, is
the prescribed balanced crossing augmented by the literal low polynomial
columns. ELVEvenPositiveCrossing proves its inverse for even moving colour
and arbitrary old endpoints.

evenPositiveCrossingAssembly sends (z,r) to toCyclotomic(z) plus the
canonical cyclotomic image of appendOutputEmbedding(r).
evenPositiveCrossingAssembly_injective uses the actual even boundary
leading maps, shared module row separation, and the proved crossing
injection. Its surjection uses the actual degree-shift division and
short-cross decoder; the surjection is valid in both height ranges.
evenPositiveCrossingEquiv packages the inverse in the nonnegative range.
evenBoundaryRowWindow_eq_height identifies the complement literally with
coefficients supported below the height.

No duplicate coefficient elimination or auxiliary assumed row inverse is
used. Complete Old(v,t) coefficients and the existing commutative scalar
ring are retained. The first entry and complement are the original maps,
not independently postulated categorical transformations.

The producer and mixed-parity concrete consumer pass scoped builds with
warnings as errors. The consumer uses distinct old endpoint orders,
positive cutoffs, the support window below four, literal column values and
both inverse identities. It audits all thirteen owned declarations.
Full CI and the global audit remain integration gates. Identification with
the prescribed module-valued positive categorical columns is separate.
