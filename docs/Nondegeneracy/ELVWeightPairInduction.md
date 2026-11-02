# Actual pair induction on the weight product

Current scope and verification are maintained in [STATUS](STATUS.md). Any original
topic-head pending checks below are historical; they do not override the consolidated
status or establish completion of the full conjecture.

The supported coordinate of the actual product induction is the composite of
its two actual block inductions, preceded by evaluation at the unique source
block. Their true intermediate block content is retained. The natural even
comparison to direct two-letter induction uses contentInductionCompTo with
that explicit intermediate content.

Outside the image of the double successor, either the outer predecessor is
absent or its inner predecessor is absent. In the latter case the inner
coordinate is zero and the actual additive outer block induction preserves
that zero object. Both cases concern the actual product functors.

The index arguments reuse blockSucc₂ and its existing uniqueness/order-support
properties. No finite-colour, finite weight-fibre or root-map-injectivity
hypothesis is added. The cutoff is not identified with the weight height here.

This supplies the support and comparison prerequisites for the actual global
crossing. Definition of that crossing, comparison of its whiskerings to the
independent content families, and transfer of their relations remain separate.

The producer and its asymmetric mixed-colour vacuum consumer pass scoped Lean
checks with warnings as errors and the pinned compatibility settings. The
consumer tests both missing-inner and missing-outer predecessor cases and
audits all nine owned declarations. Full CI remains the integration gate.
