# The missing-colour inverse on old content modules

Brundan–Ellis (1.13) at a missing-colour output has no preceding E/F
summand. The existing `missingColourUnitMatrixIso` drops that proved-zero
coordinate from the prescribed global old matrix inverse.

`contentMissingUnitMatrixIso` transports this given inverse through the
chosen following F/E chart and the canonical shifted value-family chart.
It applies to every old content module, with no scalar-evaluation
assumption. Its `_hom` is exactly `unitColumnMatrix`, with the ordinary
given unit/dot columns; `_hom_mem` and `_inv_mem` retain their canonical
source grading. Empty content and cutoff zero are included.

The scoped consumer uses a full old representable restricted to empty
content in both moving parities. A nonzero finite source vector has
nonzero image under the constructed prescribed matrix, and the zero-cutoff
inverse is also instantiated. These components support the empty local
Rouquier boundary; no complete family or left-adjunction triangle is
assumed here. The optional comparison with every preselected normalized
cap family is unnecessary for constructing this boundary inverse: inverse
uniqueness identifies the rows at the regular probe and its scalar-evaluating
closure objects when they are consumed.
