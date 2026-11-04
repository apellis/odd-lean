# The padded Dx expansion as negative-cap/post-unit words

This is the padded-chart step of SwappedHomInversion §3 (4)–(5).
The checked `centralPaddedDx_word_series` rewrites the existing
`CentralPaddedDxSeparatedAt` equation using the two given padded corner
isomorphisms. Each term is the prescribed `homPreNegativeCap` followed
by `homContentPostCup`, under the same output functor.

The input is the existing finite Dx equation. No endpoint comparison,
moment formula, or identification with a vacuum bend is assumed. The
proof removes the padded probe automorphism chart using its integral
power formula and uses `homPreNegativeCap_aut` to retain the given raw
probe inverse. The leading minus and Koszul power remain unchanged.

This charted word sum is the source for the regular-probe and empty
reservoir-block comparisons in `ProbeVacuumBendMonomials` and
`ProbeVacuumBendSeries`. Combining these with a sufficiently long
constructed Dx window is the final comparison with the evaluated
vacuum bend. The paired consumer constructs the existing ELV finite
window at each probe module and output block, then applies the word
comparison. It treats both parity colours and retains a nonzero
canonical probe append vector.
