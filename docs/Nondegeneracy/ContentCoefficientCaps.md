# Native content coefficient caps

For fixed output content ν, a nonnegative crossing height and an index r
in its prescribed unit count, the cap used in
`SwappedVacuumNonpositiveBubbles.md`, §2, is defined by

    selected native FE chart
      ≫ inverse coefficient row on the canonical extension
      ≫ inverse fully faithful inclusion unit.

`contentCoefficientCap` is therefore a module morphism from native FE(N)
back to the original content module N. It retains the original comparisons
and source unshift; no additional scalar is introduced.
`contentCoefficientCap_mem` proves its degree r*p using the checked
evenness of the selected charts and inclusion inverse.

`contentCoefficientCap_total` gives the exact linear-map identity needed
for the scalar inverse-row comparison: its component is the chosen value
chart inverse, composed with `contentUnitCoefficientMap.total`, composed
with the chosen native FE chart. These are the same selected isomorphisms
used by the scalar comparison APIs. `contentCoefficientCap_total_surjective`
proves surjectivity on every module value.

The paired consumer uses the asymmetric two-odd-colour rational regular
vacuum probes at levels one and two and applies both component
surjectivity and the homogeneous module-map theorem.

Naturality as the input module N varies, identification with a separately
prescribed action left counit, and the final swapped mixed slide remain
separate statements. Existing ground-ring descent is not an outstanding
hypothesis of these maps.
