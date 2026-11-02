# Distinct-colour ideal equality

This addresses [DeformedActionAssembly](DeformedActionAssembly.md) §2, the
full-coefficient extension of KKO I (9.3) needed by the distinct E/F mate.
It retains the two literal outer old cyclotomic ideals. The coefficient
algebra is the full ELV superalgebra over the original commutative ground
ring.

The existing one-sided decomposition is
`ELVIdealSum.ideal_eq_appendRelations_sup_range`. Its additional summand is
the image of `appendW`, the prescribed last-to-first crossing followed by
the first-position relation. In a corner from `v ++ [i]` to `t ++ [j]`, with
`i ≠ j`, this image is contained in the old-output relation span.

Expand the continuation from `i :: v` to `t ++ [j]` with the existing
output-parabolic basis, taking its final block to be `[j]`. The long
output-last shuffle moves the first letter `i` to the last position, so it
cannot occur. Every other shuffle acts entirely after the first strand.
Thus the first-position relation moves past it with its total parity,
without commuting a relation through the first crossing. The final
parabolic normal form has an old factor and a power of the last dot. The
existing last-dot/twisted-old-arrow identity moves this dot power before
the old relation, keeping the involution on the whole old Hom. This gives
an old-output ideal generator. Precomposing by the prescribed
last-to-first map finishes the containment.

`ELVOutputLastShuffle` supplies checked combinatorial inputs:
`canWord_appendRun_forward`, `outputLast_long_target`,
`outputLast_nonlong_of_distinct`, `outputLast_tail_word` and
`outputLast_tail_factor`. The output-last shuffle uses a descending
canonical word; the input-side append basis uses its inverse ascending
word. The mixed support exclusion is proved before quadratic or braid
reduction. The producer and its concrete repeated-colour, nonidentity
shuffle consumer pass strict scoped Lean checks; the consumer audits all
14 owned declarations. Full CI remains separate.

`ELVDistinctIdealSpan` formalizes the remaining span argument.
`outputOldRelations` is the literal old-output ideal span.
`ideal_eq_appendRelations_sup_outputOldRelations` proves the word-corner
form of (9.3), with only the distinct-colour premise and including empty
words and zero cutoffs. Its producer and mixed-colour consumer pass strict
scoped Lean checks. The consumer tests both moving parities, repeated
nonempty corners, the empty zero-cutoff corner, and actual crossing arrows
carrying the odd exterior coefficient at cutoffs five and six. It audits
all ten owned declarations, as well as all fourteen shuffle declarations.
Full CI remains the integration gate.

This ideal equality does not by itself construct the distinct-colour E/F
isomorphism. Its remaining inputs are the explicit mixed affine crossing
PBW inverse, identification of its two outer quotient spans with the
balanced source quotients, and comparison with the chosen categorical mate.
