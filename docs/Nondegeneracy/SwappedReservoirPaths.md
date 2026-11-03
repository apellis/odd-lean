# The canonical occupied reservoir path

SwappedActionAssembly §6 and SwappedVacuumCoordinates §2 require an actual
reservoir path for every upward word. `SPath.reservoirPath` in
`SwappedAssembly/ReservoirPaths.lean` constructs it at probe content zero,
from reservoir content `wordContent w + c` to an arbitrary given terminal
content `c`. Every step is the reservoir summand, with the literal
content subtraction. No existence premise or factor action is supplied.

The construction retains the full labelled word, all colours and repeated
colours. At terminal content zero it is the occupied path to which
`sum_of_upward_probe_zero` applies. The paired consumer uses two colours,
a repetition, three independent integer labels and a positive terminal
content, and checks a nonzero coefficient sum in the vacuum case.

The next attachment identifies the corresponding iterated postcomposition
functor with the chosen reservoir word value and computes its literal
swapped layer entries. This constructor alone does not prove that
identification or supply a nondegeneracy observation. The producer and
paired consumer pass strict scoped checks with the pinned toolchain,
warnings as errors and both compatibility settings; all 27 owned
declarations pass the consumer's axiom audit. The full build, global axiom audit and all non-vacuity checks passed in
[#1010](https://github.com/apellis/odd-lean/pull/1010), at source head
`066fc97a28cb36b2034dc37e9913f6d958b08f62`
([CI run](https://github.com/apellis/odd-lean/actions/runs/41680334616)).
