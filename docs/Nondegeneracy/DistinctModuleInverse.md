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

The forward-map comparison with the categorical mate is proved on
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

`ELVDistinctModuleInverse` constructs `moduleMateUnderlyingEquiv` on every
old input module and proves the whole-map identity
`moduleMateUnderlyingEquiv_toLinearMap`. The separate identity
`moduleMateLinear_eq_rectangular` identifies this forward map with the
chosen rectangular categorical mate, so `moduleMate_total_bijective`
gives bijectivity of every total component of that mate. No restriction to
representables, finite-dimensional modules or even module elements is used.

The producer and its paired consumer pass strict scoped checks. The consumer
uses parity-shifted old representables with both mixed moving parities,
distinct odd colours, ordinary right precomposition by an odd exterior
coefficient, and empty words at zero cutoff. Full CI remains the integration
gate. Bundling the inverse as a homogeneous old-module natural map and
transporting the chosen mate to exact content and original weight remain
subsequent obligations.
