# Central path charts

For the central blocks of Brundan–Ellis (1.13)–(1.14),
`SPath.centralUpDnEquiv` identifies the source paths with the subtype
of valid first sides of `EᵢFᵢ`; `SPath.centralDnUpEquiv` does the same
for the target paths of `FᵢEᵢ`. Both sides of each path are equal.
The reservoir source requires positive reservoir content, whereas the
probe target requires positive probe content. The other pure paths
always exist. `centralNilEquiv` gives the unique identity-path index.
These statements include empty and mixed sectors.

`matrixEmbeddingIso` inserts zero objects at absent indices of a finite
family matrix, using specified isomorphisms at every present index. Its
forward and reverse entries are the Kronecker family followed or preceded
by the supplied component chart. The two inverse identities follow from
finite sums; invertibility of a matrix being charted is not a premise.
`matrixEmbeddingMap_square` records the resulting coordinate square.

The paired consumer applies the path classifications to both colours,
occupied sectors, the empty sector, and a mixed sector with complementary
absent corners. Its matrix example pads a nonzero rational module by a
zero module, checks both inverse equations and a nonzero retained entry,
and applies the coordinate square to an arbitrary module matrix.

`sectorFamilyIso` packages this padding with a classification into valid
pure sides and window indices. Its pure objects and all their component
charts are supplied explicitly; window objects have their specified
charts too. `matrixEmbeddingMap_apply` identifies every retained matrix
entry as source chart, original entry, inverse target chart. The paired
`SwappedSectorFamilyChart` consumer covers each absent-corner pattern,
both two-slot and empty windows, and arbitrary maps between these
rational-module families.
