# Even cap pivots on the prescribed source

This is the parity-zero input pivot calculation of
[DeformedRouquierMatrix](DeformedRouquierMatrix.md), section 4.

Let beta(f) be the decoded P image of the specified long section.
The ordinary even input dot shifts beta's coefficient row by one.
The raw input contraction reads the constant coefficient of the next
polynomial-boundary value. Iterating therefore gives

    E_raw X^r q(beta(single(d,b))) = A(single(r+d+1,b))(0).

The actual arbitrary-Hom above/top theorem implies vanishing when

    r+d+1+endpointQPDegree < degree(S),

and the scalar-unit balance-twist pivot when equality holds.
Both affine short coordinates and the original q quotient are covered.
The old coefficient b remains arbitrary, with no exterior support bound.

These are the pivots needed for the finite even cap matrix after the
generic crossing-kernel equivalence. The actual coefficient(0) module
comparison separately identifies E_raw with minus the canonical counit.

The proposed producer `ELVEvenInputPivots` has concrete connected mixed-data
negative-height pivot/below/iterate consumers, with every numerical
condition proved. Source and consumers await checking.
