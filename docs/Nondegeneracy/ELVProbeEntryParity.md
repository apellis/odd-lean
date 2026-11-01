# Scalar probe entries preserve parity and word support

`ELVProbeEntryParity.lean` proves that the actual scalar specialization of
untruncated old ELV rectangular Homs preserves super parity in the existing
`heightAlgebra`, including height zero. The canonical probe polynomial parity
proof closes this input without an extra hypothesis.

Each entry is supported by its actual target word idempotent on the left and
source word idempotent on the right. Together with the previously checked
identity, composition and append formulas, these are the algebraic inputs for
restricting an ordinary probe supermodule to the old category.

Strict local producer and concrete consumer checks pass; all 11 owned
declarations pass the axiom audit. Full CI remains the integration gate.
The consumer checks the vacuum, an odd last dot, and the actual specialized
old identity and its two word supports.

The full old-category module functor and its induction/action comparison are
still separate. No specialization of a coefficient-truncated category is
asserted.
