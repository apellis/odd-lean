# Inverse rows of the old missing-colour unit matrix

For Brundan–Ellis (1.13), `unitColumnModuleInverseRow` projects the inverse of
the specified finite module unit matrix and removes its original source
shift. Its degree, finite Kronecker window and reconstruction identity
follow from the existing finite-module inverse-coordinate identities.

`contentMissingUnitRow` supplies the constructed prescribed old
missing-colour module isomorphism. Its window and finite decomposition
hold on every old input module, including zero cutoff. No scalar
coefficient evaluation, inverse-naturality or compatibility condition is
imposed. The consumer extracts a nonzero vector of a full old
representable in each finite row, for both moving parities.

These inverse-defined rows provide the empty local Rouquier boundary.
They have not been identified here as a whole family with every
preselected normalized coefficient cap; the regular probe and its
scalar-evaluating closure objects have the separate checked uniqueness
criterion needed for that comparison.
