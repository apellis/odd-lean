# Actual reservoir layer cells and affine quotient classes

[ELVReservoirLayerCells](../../OddMath/QuiverHecke/CyclotomicAction/ELVReservoirLayerCells.lean)
attaches the chosen OLD reservoir dot and crossing to actual tensor-vacuum
Hom entries, with an arbitrary reservoir path on each side. The right path
ends at reservoir content zero; the left path may end at nonzero content.
Both labelled paths are reversed when read as iterated OLD E words.
The original middle E weight certificates are retained. No supplied equality
of the resulting functors or their generators is a hypothesis.

`dot_square` and `cross_square` identify the actual whiskered chosen maps
with the corresponding contextual tensor-Hom generators, using only the
proved path endpoint equalities and canonical word charts.
`dot_class_square` and `cross_class_square` then act on an arbitrary Hom
entry `f`, at the actual regular probe, on every vector in its specified
source-content block. Given a representative of that input's quotient
class, the output is the action of the original affine layer with coefficient
one. The half-turn sign and both outer contexts are those of
`TensorLayerClasses`; equal-colour and distinct-colour crossings are included.
The representative hypothesis describes the input class, rather than a
generator comparison.

The [paired consumer](../../scripts/NonVacuity/ELVReservoirLayerCells.lean)
uses actual OLD data over the rationals, both two-odd and mixed parities,
a two-letter right context and a nonempty left context. Count-compatible
middle vertices are constructed from `cR + single i 1` and
`(cR + single j 1) + single i 1`. It tests the whole-map and all-vector
quotient squares for every Boolean colour pair. Exterior basis inputs,
normalized vectors, and their quotient classes are proved nonzero; the
needed representatives are obtained from quotient surjectivity.

The producer and consumer pass the repository's strict isolated checks.
The owned-declaration audit covers 58 declarations and uses only the
standard allowed axioms. These statements concern the concrete selected
Hom object and specified content block. They do not assert boundary
support for arbitrary objects in a whole weight product, faithfulness of
regular-probe evaluation on all Hom transformations, existence of a
completed OLD ProbeReservoir, or the final observation assembly.
