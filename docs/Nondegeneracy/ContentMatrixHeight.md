# Fixed-content matrix height and finite counts

DeformedMatrixComparison section 4 uses one finite matrix count on a
fixed-content block. ELVContentMatrixHeight proves that the actual row
degree difference Q-S is constant there.

contentCrossingHeight is cutoff(i) minus the sum of the actual Cartan
pairings over the content multiset. crossingHeight_eq_content identifies
it with the integer difference of endpointQPDegree and outputSDegree.
Permutation invariance follows. contentUnitCount and contentCapCount
are the explicit nonnegative parts of this height and its negative.

oldContent_unitCount_height and oldContent_capCount_height prove the
precise natural-number degree equalities Q=S+m and S=Q+m for every
actual OldContentCategory object, from its wordPerm field. The
ContentCategory counterparts use the actual content field, for any
coefficient truncation bound. Neither a category equivalence nor a
module equivalence is assumed between these categories.

This supplies a single finite count for a coefficient-kernel matrix
restricted to a fixed content. It does not itself construct the
natural transformation or transfer representable inversion to
arbitrary modules. Those remain the kernel/coend obligations.

The producer and closed mixed consumer pass strict scoped checks,
with all eighteen owned declarations audited. Both moving parities,
positive and negative heights, zero count, and genuinely reordered
content objects are tested on the actual old and truncated categories.
The truncated tests retain an arbitrary coefficient bound. Full CI
and the global audit remain integration gates.
