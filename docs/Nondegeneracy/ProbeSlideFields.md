# Exact distinct slide fields for the bundled OLD probe generators

Brundan–Ellis (1.8) is proved in the literal `RouquierMulticolour.slideLeft`
and `slideRight` formats by `ELVProbeSlideFields`.
`probeOldRouquierData_slideLeft` and `probeOldRouquierData_slideRight`
retain the actual `.cross`, `.E` and `.dot` fields of
`probeOldRouquierData D (parameterTwist D Sc) m Λ`.
`probeOldActionCross_distinct` selects the already constructed positive
branch. The left equation uses the checked whole-weight inner slide and
the involutivity of the parity sign; the right equation uses the checked
outer slide. Both signs are exactly `SKM.zsign k (D.parity i * D.parity j)`.

The two independent dot choices and the stored-target coordinates are
unchanged. The underlying whole-weight equations already include absent
predecessor blocks through their actual zero source objects. No slide
relation, multicolour record or partial action record is supplied as an
extra hypothesis.

The exact producer and paired consumer pass strict checks with warnings as
errors and both compatibility settings. All eight owned declarations pass
the axiom allowlist. The consumer covers connected mixed colours with a
nonzero interior parameter, both colour orders, occupied vacuum and
nonempty actual regular weight inputs, and asymmetric two-odd data with
an explicitly negative slide sign. Disconnected odd colours with original
unit parameter 2 are tested in both orders as well. The regular probe
vacuum vectors are independently nonzero.

These two exact fields can be used with the separately proved quadratic,
braid and inverse fields in the eventual complete presentation. The
present module constructs no record with missing fields.
