# Even crossing height and kernel

The prescribed balanced crossing in DeformedRouquierMatrix, section 4,
inherits injection and surjection in the respective height ranges from the
proved even polynomial boundary.

ELVEvenCrossingHeight gives evenToCyclotomic_injective_of_nonnegative_height,
evenToCyclotomic_surjective_of_nonpositive_height and
evenToCyclotomicEquiv_zero_height at arbitrary old Hom endpoints.
The surjection uses a preimage under the actual polynomial boundary and
the existing short-cross decoder, rather than a supplied crossing inverse.

The construction and exactness proofs in ELVOffDiagonalBoundarySnake
are parity-independent. Its moving binder is now an arbitrary colour.
Existing odd callers retain the same names and coerce their odd-colour
subtype argument; their source and consumers still check.

ELVEvenBoundaryKernel identifies ordinary polynomial coefficients
supported at d+endpointQPDegree<outputSDegree with the actual boundary
kernel (evenBoundaryKernelEquiv). Composing with the generic snake gives
evenCrossingKernelEquiv onto the kernel of toCyclotomic.
evenBoundaryKernelWindow_eq_height identifies this support literally with
degrees below m when outputSDegree=endpointQPDegree+m.
evenCrossingKernelEquiv_lift evaluates these classes using the original
long section, exactly q(decode(P(longSection f))), as needed by the cap
recurrence. No source-lift equality or faithful-action premise is supplied.

All changed producers and concrete consumers pass scoped builds with
warnings as errors. The even consumer uses both height ranges with positive
cutoffs, the zero-height inverse identities, mixed distinct old endpoints,
the support window of three coefficients, and the original-long-section value
formula. It audits all owned declarations. The existing odd input matrix,
its categorical operator comparison and ordinary dotted-counit inverse
also pass scoped checks after the generic snake extension.
Full CI and the global audit remain integration gates.

The finite even cap matrix and its coefficient(0) ordinary-counit
comparison remain subsequent obligations.
