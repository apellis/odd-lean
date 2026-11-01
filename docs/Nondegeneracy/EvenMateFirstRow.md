# Actual even first-row identification

`ELVEvenMateFirstRow.evenModuleMate_firstRow` proves, for every even moving colour i, arbitrary old endpoints v,t and arbitrary ordinary induction-restriction source vector z, that co-Yoneda evaluation of the fixed actual `oldModuleMate.app 0` equals minus `toCyclotomic (evenSourceEquiv z)`.

The canonical even source comparison is the existing coefficient(0) module isomorphism of ELVEvenCoefficientModule. Its checked tensor formula has no parity twist. The actual signed mate and co-Yoneda formulas are reused from the common all-colour calculation; no mate/matrix equality or inverse premise is introduced.

Verification: producer and closed mixed-endpoint consumer passed strict local checks, with all 2 owned declarations audited. All imports use existing checked artifacts; no dependency rebuild, resource budget increase or linter change. Full branch CI is pending.

Together with the odd first-row theorem, this supplies both component identifications needed by the already constructed representable finite-family inverse. Attaching those equalities to the packed shifted-family entries and transporting through content/weighted coefficient quotients remain separate steps. This note does not assert the completed action.
