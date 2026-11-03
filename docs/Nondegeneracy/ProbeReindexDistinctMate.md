# The distinct inverse at prescribed OLD probe contents

Brundan–Ellis (1.12) requires the chosen positive sideways crossing to
be invertible when the colours differ. `ELVProbeReindexDistinctMate`
supplies that inverse at four arbitrary stored contents, using the
already proved untruncated OLD PBW inverse. No component invertibility or
generator comparison is assumed.

For a standard input module `N` at the lower `j` content, the target
input is its forward reindexing. The lower-`i` append comparison and the
upper-`i` append comparison identify the two mixed induction/restriction
coends. Their tensor formulas retain the whole coefficient arrow and
the coefficient vector. The positive rectangular mate acts by
`[g ⊗ v] ↦ [cross ≫ twist(M.map g) ⊗ v]`. Applying either order of
mate and comparison therefore gives the same tensor.

`oldReindexDistinctLinear_mate` proves this all-vector square. Both
comparison maps are bijective because they are totals of the specified
append-adjunction isomorphisms. The standard OLD mate is bijective by
`oldContentDistinctMateLinear_bijective`. The square proves bijectivity
for reindexed inputs. The strict inverse reindexing equivalence covers
all inputs: its module equality is transported before forming the coend
property, avoiding an additional hypothesis on the input module.

`oldAppendToDistinctMateLinear_bijective`,
`oldAppendToDistinctMateModuleIso`, and
`oldAppendToDistinctMateFunctorIso` give the resulting linear, module and
input-natural inverse constructions. Their forward is the prescribed
positive cup-crossing-cap, and their inverse has crossing parity
`p(i)p(j)`.

The full evaluated-category restriction retains the same forward and
constructed inverse. `probeAppendToDistinctMateIso` is its whole
supernatural isomorphism. `probeAppendToCrossMate_eq` identifies the
presentation's sideways crossing, bent by the given lower and upper
right adjunctions, with this mate.
`probeAppendToCrossMate_isIso` supplies its inverse from colour
distinctness alone. The global weight-product attachment is a subsequent
obligation.

The producer and paired consumer pass strict scoped checks with warnings
as errors and both compatibility settings. The consumer instantiates the
all-input bijection, raw and evaluated inverse constructions, the exact
sideways-crossing equality and its invertibility on canonical contents.
It includes mixed data and the symmetrizable all-odd asymmetric datum,
checks that the latter inverse has degree one, both inverse identities,
and naturality on an odd input map. All 132 owned declarations pass the
axiom audit. Full integration verification remains separate.
