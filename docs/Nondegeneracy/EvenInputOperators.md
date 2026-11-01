# Even input operators on the original cyclotomic source

This is the parity-zero input-operator construction in
[DeformedMatrixComparison](DeformedMatrixComparison.md), section 3.

The ordinary even moving dot preserves the kernel of long extraction.
Since that kernel is the actual range of alpha, the input polynomial
defect vanishes on P(alpha). The decoded moving dot preserves the
prescribed Pprime relation. Both operators therefore descend through the
original q map to Source, before any row division or inverse is used.

The descended raw contraction and decoded dot retain all old coefficients.
On representatives their formulas are

    E_raw(q(r tensor g)) = -[r composed with g],
    X_aff(r tensor g) = (dot composed with g) tensor r.

The minus sign is essential. Identification with actual induction of the
coefficient(0) module and the canonical counit requires the explicit
E_raw = -counit normalization; the odd coefficient(1)/grading(1) attachment
cannot be reused without this change.

The proposed producer `ELVEvenInputOperators` and concrete mixed connected
data quotient/representative consumers await checking. Cap pivots and the
actual coefficient(0) attachment remain separate obligations.
