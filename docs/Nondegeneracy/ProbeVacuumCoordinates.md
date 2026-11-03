# Ground coordinate of the regular probe vacuum

`SwappedActionAssembly.md`, F2, uses the regular height-zero probe. The
empty-word PBW basis in BE2 (11.1) has one index: both words are empty,
there are no dot positions, and the permutation of zero strands is unique.
`heightZeroScalarEquiv` identifies its literal algebra `Hn D Sc 0` with the
ground ring as an algebra. Its value at one is the original empty
idempotent; neither a quotient nor an evaluation hypothesis is introduced.

`probeVacuumScalarEquiv` then gives the scalar coordinate on the fixed
empty-idempotent submodule of the prescribed regular old probe. It sends
one to `probeOldVacuumVector`, and `probeVacuum_even` proves that every
vector of this component is even. This supplies the ground-valued target
needed to specialize the last inverse unit-matrix row to the probe.

The paired consumer uses the asymmetric two-odd-colour datum over the
rationals, with probe levels one and two. It checks algebra multiplication,
the unchanged empty vector, a nonzero scalar vector, and evenness of every
empty vector. The last-row specialization and its identification with a
normalized left probe cap remain separate obligations; no mixed slide or
final swapped vacuum datum is asserted here.
