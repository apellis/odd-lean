# Proposed comparisons for the chosen content E/F composites

This is a proposed continuation toward SwappedVacuumCoordinates §6 and
DeformedActionAssembly §5. The source module `ELVContentEFComparison` is
not yet a checked library result and is not exported by the umbrella.
Its proposed declarations must pass both source and concrete-consumer
verification before integration.

For a content ν and colour i, write Eν and Fν for induction and restriction
along the literal old-content append functor. Let Lν and Rν be extension
and restriction along the full content inclusion. The existing chosen
comparisons are

```
e : Eν ⋙ L(i::ν) ≅ Lν ⋙ E,
ξ_N : Lν(Fν N) ≅ F(L(i::ν) N).
```

The proposed `oldContentAppendRestrictionNaturalIso` bundles the selected
restriction of e, including the fully faithful inclusion unit. Its forward
component must equal the existing `oldContentAppendRestrictionIso`.

To bundle ξ without normalizing nested concrete module records, identify
its forward component with the inverse mate of the literal restriction
square

```
R(i::ν) ⋙ Fν ≅ F ⋙ Rν.
```

The mate uses the existing two inclusion adjunctions; its component is
induction of the restricted inclusion unit, followed by the inclusion
counit. This is exactly the previously selected ξ. Naturality of that
mate applies to every supernatural module map, including odd maps.

These families should produce two different charts. At the upper content
i::ν, the first compares the chosen Eν Fν composite to E F after canonical
extension and restriction. At the lower content ν, the second compares
Fν Eν to F E after canonical extension and restriction. For a same-colour
matrix at i::ν, use the first chart on the preceding edge and the second
chart on the following edge.

The ordinary unit/counit identities are supplied separately by
`ELVContentAppendAdjunction`. Still required are compatibility of the
chosen two-letter extension comparison with the signed equal crossing,
the resulting prescribed mate square, and the parity/product charts for
the whole finite unit/cap matrices. Contents with no predecessor of
colour i require their zero preceding composite; a predecessor assumption
must not be hidden in a final matrix theorem.
