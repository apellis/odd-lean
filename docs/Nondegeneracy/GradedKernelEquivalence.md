# Graded arbitrary-module kernel transfer

DeformedMatrixComparison §4 needs an even, componentwise bijective
ordinary-right kernel matrix to induce an even isomorphism for every input
supermodule. The balanced quotient and its sum grading are the existing
objects, without a flatness premise.

`gradedIsoOfBijective` equips the existing `equivOfBijective` with the literal
source and target SVec objects. Its forward map is exactly the established
kernel-tensor map. `gradedIsoOfBijective_hom_even` uses the proved
`map_even` theorem. `gradedIsoOfBijective_inv_even` then uses inverse
homogeneity of an isomorphism: inverse grading is a consequence, not a new
input. `gradedIsoOfBijective_hom_tensor` retains the generator formula.

The producer and paired concrete consumer pass strict source checks, with
all 7 owned declarations passing the axiom audit. The consumer applies a
nonidentity negative-identity natural kernel map to actual old representable
modules, checks both directions' evenness and the inverse product, and uses
a nonzero mixed exterior-coefficient crossing that survives cofinal cutoffs.

The concrete matrix's bijectivity and evenness and its action-module
realizations remain separate inputs. Full exact-head CI is required before
research integration.
