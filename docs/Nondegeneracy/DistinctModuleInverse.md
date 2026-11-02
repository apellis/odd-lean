# Distinct mate on arbitrary old modules

This extends the representable-corner inverse from
[DistinctMateComparison](DistinctMateComparison.md) to the arbitrary-module
step of Brundan–Ellis (1.12), following
[DeformedActionAssembly](DeformedActionAssembly.md) §4.

For the two append functors `A = append i` and `B = append j`, the source
coefficient kernel at `t` is

    K(v,t) = ∫ˢ Hom(A s,t) ⊗ Hom(v,B s).

Its right action is literal ordinary precomposition on the second factor.
`ELVMixedIndResKernel` generalizes the existing one-functor kernel realization:
`K(-,t) ⊗ N` is canonically the balanced induction of the restriction of `N`
along `B`, using induction along `A`. Evaluation and identity insertion are
explicit inverse quotient maps. This producer is scoped-checked.

The kernel map has the prescribed positive cup-crossing-cap formula:

    [g ⊗ b] ↦ A(b) ≫ cross(s) ≫ twist_e(B(g)),
    e = p(i)p(j).

Crossing supernaturality proves its lower balance. Associativity and functor
composition give ordinary-right covariance, without a sign on `b`. The direct coefficient natural isomorphism
`kernelSourceCoefficientIso` acts through the checked ordinary coend
`coefficientEquiv`, before forming any induced module map. This changes
`Hom(v,B s)` to the existing coefficient-zero functor. Canonical J followed
by the checked full quotient PBW decoder supplies `kernelCrossingEquiv`.
`kernelMateComponent_bijective` identifies this with the prescribed forward
component. The inverse is therefore identified without expanding the
actual representable module records. `BalancedKernelTensor.coefficientIso` and its explicit
quotient tensor equivalence then produce the inverse after tensoring with
every old module, without flatness or projectivity.

The forward-map comparison with the categorical mate is to be checked on
kernel generators. Evaluate `b` on a module element; the categorical mate
then produces the tensor with arrow `cross(s) ≫ twist_e(B(g))`. The outer
induction balance moves `A(b)` to the arrow factor and gives the displayed
kernel formula. This identifies the tensor inverse with the prescribed
categorical map, rather than an independently selected decomposition.

`ELVMixedIndResKernel`, `ELVMixedMateKernelMap`,
`ELVInductionCoefficientIso`, `ELVMixedMateLinear` and
`ELVDistinctMateKernel` pass strict scoped checks. The paired kernel
consumer passes and audits all 108 owned declarations; see
[DistinctMateKernel](DistinctMateKernel.md).

`ELVDistinctModuleInverse` and its paired consumer remain proposed. The
file constructs the arbitrary-module coend equivalence and its kernel
generator formula, the ordered categorical map and its rectangular mate
identity, and the evaluation square. Its final whole-map equality has not
passed: the proposed proof compares the coend maps through an abstract
kernel-generator criterion, with explicit composite-map value equalities.
This is an endpoint-normalization obligation, rather than a mathematical
obstruction. Neither this producer nor its consumer is a checked completed
batch, and no all-module categorical inverse is claimed from the proposed
source. Exact-content and original-weight transport remain subsequent
obligations.
