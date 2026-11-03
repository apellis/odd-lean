# Restriction and parity charts for finite matrices

For Brundan–Ellis (1.13)–(1.14), `ELVRestrictionMatrixCharts` retains the
chosen pointwise module comparisons under finite products and the actual
canonical parity shifts. `restrictionFamilyIso` is the coordinatewise
product of the supplied module isomorphisms, with the restricted action
on every coordinate. Its total formula applies to arbitrary vectors.

`shiftedRestrictionChart` uses the existing `parityRestrictionIso` in the
source-to-target direction. An even unshifted chart gives an even shifted
chart, and `shiftedRestrictionChart_source_coordinate` identifies the
specified source parity coordinate with the restricted target coordinate.
No rescaling or replacement of the parity action occurs.

The producer and its paired concrete consumer pass strict scoped checks.
The consumer uses the selected fully faithful content-extension unit,
parity-shifted representable modules, both colour parities, arbitrary
truncation bounds, arbitrary finite Option/Fin families, and the empty
window at zero bound. It audits every declaration owned by the producer.
The given content finite matrix forward squares and inverse attachment
remain separate obligations.
