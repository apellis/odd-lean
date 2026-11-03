# Ordinary-right mixed crossing kernels

This develops the arbitrary-module tensor step of Brundan–Ellis (1.12),
[DeformedActionAssembly](DeformedActionAssembly.md) §4, from the checked
full-coefficient quotient decoder and representable mate comparison.

For `A = append i` and `B = append j`, the source coefficient kernel is

    K(v,t) = ∫ˢ Hom(A s,t) ⊗ Hom(v,B s).

`MixedIndResKernel.equiv` identifies `K(-,t) ⊗ N` with the existing balanced
induction by `A` after restriction along `B`, for any old module `N`.
Evaluation and identity insertion give both quotient roundtrips. Its right
action is literal ordinary precomposition on the second factor.

`MixedIndResKernel.mateComponent` has the prescribed ordered formula

    [g ⊗ b] ↦ A(b) ≫ cross(s) ≫ twist_e(B(g)),
    e = p(i)p(j).

Full crossing supernaturality proves lower balance. Ordinary-right
naturality follows from functor composition and associativity, with no sign
on `b`, including odd or inhomogeneous exterior coefficients.

The component inverse is constructed before any actual module-record
identification. `kernelSourceCoefficientIso` identifies the coefficient
functor with coefficient zero. `BalancedInduction.coefficientEquiv` acts on
this ordinary natural isomorphism directly at the balanced quotient.
`kernelCrossingEquiv` then applies canonical J and the full cyclotomic PBW
crossing equivalence. Its tensor formula agrees with the prescribed map,
so `kernelMateComponent_bijective` and `kernelMateIso` provide an isomorphism
of the literal ordinary-right coefficient kernels. Tensoring it with every
module uses the existing explicit `BalancedKernelTensor.equiv`; no flatness
or projectivity premise is introduced.

`ELVMixedMateLinear` also retains the ordered categorical mate on its
induced/restricted carriers. The coend source comparison is formed before
applying that map. `orderedMixedMateCoend_eq_linear` proves equality of
whole linear maps, and its tensor formula follows by evaluating that
identity. The positive distinct-colour crossing retains no equal-colour
minus sign; the total first-factor twist includes exterior coefficients.

The five producers and their concrete paired consumer pass strict scoped
checks. The consumer includes shifted input modules, mixed parities, two
distinct odd colours, ordinary-right exterior precomposition, empty words
and zero cutoff, and audits all 108 owned declarations. Full CI remains
the integration gate.

The whole-map identity is supplied by the scoped-checked
[DistinctModuleInverse](DistinctModuleInverse.md). Its homogeneous old-module
inverse and arbitrary input-module naturality are supplied by
[DistinctModuleIso](DistinctModuleIso.md). Exact-content/original-weight
transport and the full factor family remain subsequent obligations.
