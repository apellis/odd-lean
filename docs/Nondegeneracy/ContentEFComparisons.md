# Chosen content E/F comparisons

SwappedVacuumCoordinates §6 and DeformedActionAssembly §5 require comparisons
for the selected content E/F composites, as functors on all input modules.
The output-content restriction of an old matrix is a different statement.

For a content ν and colour i, write Eν and Fν for induction and restriction
along the literal old-content append functor. Let Lν and Rν be extension
and restriction along the full content inclusion, and E and F the whole-old
append functors. The existing chosen comparisons are

```
e : Eν ⋙ L(i::ν) ≅ Lν ⋙ E,
ξ_N : Lν(Fν N) ≅ F(L(i::ν) N).
```

`oldContentAppendRestrictionNaturalIso` bundles the selected restriction of
e, including the fully faithful inclusion unit. Its forward component is
exactly `oldContentAppendRestrictionIso`, as stated by `_hom_app`.

`oldContentRestrictionSquareNaturalIso` is the literal restriction square

```
R(i::ν) ⋙ Fν ≅ F ⋙ Rν.
```

The forward map of ξ is the inverse mate of this square under the two
inclusion adjunctions. Its formula is induction of the restricted inclusion
unit followed by the inclusion counit, exactly the previously selected ξ.
This identifies its naturality on every supernatural module map, including
odd maps, without normalizing concrete balanced quotient modules.
`oldContentRestrictionExtensionNaturalIso` bundles the resulting family.

The two composite charts have different content endpoints:

* `oldContentEFExtensionNaturalIso` compares extension of the preceding
  Eν Fν composite at i::ν with old E F on the canonical extension. Its
  `_hom_app` formula is e at Fν N followed by E applied to ξ_N.
* `oldContentEFRestrictionNaturalIso` compares that same preceding content
  composite with old E F after canonical extension and restriction. The
  first map is the selected fully faithful inclusion unit.
* `oldContentFERestrictionNaturalIso` compares the following Fν Eν
  composite at ν with old F E after canonical extension and restriction.
  Its `_hom_app` formula keeps Fν applied to the selected restricted e.

At a same-colour matrix on content i::ν, use the first composite chart on
the preceding edge and the following-composite chart on the next edge.
The concrete consumer exercises both moving parities, mixed representable
modules, the specified odd content dot as an input map, and the vacuum
following composite.

The ordinary unit/counit identities are supplied separately by
`ELVContentAppendAdjunction`. Still required are compatibility of the
chosen two-letter extension comparison with the signed equal crossing,
the resulting prescribed mate square, and the parity/product charts for
the whole finite unit/cap matrices. Contents with no predecessor of
colour i require their zero preceding composite; a predecessor assumption
must not be hidden in a final matrix theorem.
