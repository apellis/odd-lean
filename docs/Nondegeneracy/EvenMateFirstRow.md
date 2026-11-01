# Actual even first-row identification

`ELVEvenMateFirstRow.evenModuleMate_firstRow` proves, for every even moving colour i, arbitrary old endpoints v,t and arbitrary ordinary induction-restriction source vector z, that co-Yoneda evaluation of the fixed actual `oldModuleMate.app 0` equals minus `toCyclotomic (evenSourceEquiv z)`.

The canonical even source comparison is the existing coefficient(0) module isomorphism of ELVEvenCoefficientModule. Its checked tensor formula has no parity twist. The actual signed mate and co-Yoneda formulas are reused from the common all-colour calculation; no mate/matrix equality or inverse premise is introduced.

Verification: producer and closed mixed-endpoint consumer passed strict local checks, with all 2 owned declarations audited. This producer and consumer were integrated with the full-CI verified representable closure [#889](https://github.com/apellis/odd-lean/pull/889), including the global audit and non-vacuity checks.

Together with the odd first-row theorem, this supplies both component identifications needed by the already constructed representable finite-family inverse. Their packed representable shifted-family attachment is proved in [ActualMatrixFamilies](ActualMatrixFamilies.md). Arbitrary-module inversion and content/weighted coefficient transports remain separate steps, tracked in [STATUS](STATUS.md). This note does not assert the completed action.
