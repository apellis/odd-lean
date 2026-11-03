# Distinct slides through the selected pair charts

Brundan–Ellis (1.8) requires the independently chosen dots and positive
rectangular crossing. `ELVInductionGridDistinctSlides` keeps four
categories and all four append functors. Both rectangular slides use the
two prescribed induction-composition charts defining the crossing.

`rectangularCrossComponent_slide_inner_outer` relates the inner dot on
the target pair to the outer dot on the source pair. Its companion
`rectangularCrossComponent_slide_outer_inner` interchanges these roles.
Each follows from its literal source relation by signed balanced
induction and the existing inner/outer dot comparisons. The two
superopposite signs cancel, retaining the source scalar.

The generic intermediate theorems explicitly require their source slide.
The concrete consumer supplies it from `ELVOldDistinctSlides`, using four
successive OLD content categories and their prescribed common upper
representative. It tests both moving parities, a mixed-content restricted
representable and a shifted empty-content representable. Both producer
and consumer pass strict checks with warnings as errors and both
compatibility settings, including all three owned-declaration audits.
Full integration remains separate. Evaluated restriction and comparison
with the independently selected global dot coordinates are the remaining
distinct-slide attachments for the probe family.
