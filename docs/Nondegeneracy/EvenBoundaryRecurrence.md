# Even polynomial-boundary recurrence

This is the parity-zero specialization of
[DeformedBoundaryDivision](DeformedBoundaryDivision.md), equation (8).

Let A be the actual arbitrary-Hom polynomial boundary and σ ordinary finite
coefficient shift. The even moving-dot/section identity and the
generic polynomial-constant input-dot defect give

    A(σ f) = σ(A f) + single(0, defect(P(section(f)))).

This is an identity on arbitrary Old(v,t), retaining all polynomial and
exterior coefficients. The parity hypothesis concerns the moving colour
only. It imposes no support restriction on the other colours.

At coefficient n+m, every n-fold shift therefore telescopes exactly:

    A(σ^n f)(n+m) = A(f)(m).

Together with the independent-S reverse-numerator identity in
[EvenPolynomialBoundary](EvenPolynomialBoundary.md), this supplies the
parity-specific recurrence input for monic-S division and leading coefficients.
The implementation is
[ELVEvenBoundaryRecurrence](../../OddMath/QuiverHecke/CyclotomicAction/ELVEvenBoundaryRecurrence.lean).

Verification status and remaining dependencies are maintained in
[STATUS.md](STATUS.md) and [HANDOFF.md](HANDOFF.md).
