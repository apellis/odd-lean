# Off-content coefficient kernels vanish

ELVOffContentZero descends the existing full-coefficient no-permutation zero theorem through the actual old quotient. Old-Hom(v,t) vanishes when the two colour multisets differ. Appending the same moving colour preserves that mismatch by multiset cancellation, so the upper Hom vanishes too.

`indResKernel_eq_zero_of_content_ne` proves the actual IndRes coefficient coend vanishes off content for ANY ordinary functor J:C→OldCategory. Each pure tensor has arrows v→J(s)→t; either v and J(s) differ in content, killing the coefficient, or J(s) and t differ, killing the first factor. This is a proof in the literal quotient, not a whole-category/content equivalence or a density assertion.

Zero and Subsingleton APIs are exported. No finite-colour, symmetrizer, homogeneous-scalar, flatness, degree or moving-parity hypothesis occurs. Producer and concrete wrong-content Hom/upper-Hom/append-J/identity-J/Subsingleton consumers passed strict local checks; all 9 owned declarations, including private/generated, were audited. Full CI is pending.

This closes the off-content zero branch for fixed-target finite matrix counts on the full old coefficient category. Matching-content bijectivity still uses the checked fixed-content height/count and actual matrix inverse results; arbitrary-module/family identification remains a separate assembly step.
