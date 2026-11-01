# Actual cofinal probe polynomial parity

`probePolynomial_parity` supplies the exact `CyclotomicPolynomialParity`
premise for the existing cyclotomic supermodule construction. The proof
writes each binomial probe as a polynomial expansion. Nonzero odd-colour
coefficients have even exponent; the expanded natural degree is also even.
It requires a commutative ring, with no domain/nontriviality hypothesis and
no finiteness hypothesis on the colour type. Exponent zero powers are included.

The producer passed the full source build and axiom audit at `33e3042c`;
its complete concrete-consumer gate remains under verification. This supplies polynomial parity, not invertibility of the
dot or a factor action. The signed induction-dot inverse is a separate result.
