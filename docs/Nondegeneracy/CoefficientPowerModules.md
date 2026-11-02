# The coefficient-power-annihilated module category

This constructs the old-module subcategory used for the paper's coefficient
power ideal in [SwappedNondegeneracy, §2](SwappedNondegeneracy.md), using
[CoefficientAnnihilation](CoefficientAnnihilation.md). The producer and paired
concrete consumer pass scoped Lean checks with warnings as errors and both
pinned compatibility settings. All 48 owned declarations pass the standard
axiom allowlist audit. Full CI remains the integration gate.

Let A be the full ELV coefficient algebra, choose a family of even coefficients
c_j and powers L_j, and define the literal two-sided ideal

    T=span_two_sided {c_j^L_j}.

`coefficientAnnihilator(M)` is the two-sided ideal of all coefficients whose
identity endomorphisms act by zero on every old module component. Its two-sided
closure uses the proved order e(a) composed with e(b)=e(b*a), rather than
commuting exterior coefficients. `coefficientPowerProperty(M)` is the exact
inclusion T contained in coefficientAnnihilator(M).
`coefficientPowerProperty_iff` proves this equivalent to annihilating the
displayed generators, so the condition concerns every element of T and every
module vector, not only chosen generators acting on the vacuum vector.

`CoefficientPowerModules` is the full subcategory of these old supermodules.
It inherits all even and odd supernatural maps, its additive and linear
structure, and the existing full-subcategory supercategory structure. The
coefficient annihilation results show the actual old induction and restriction
preserve its objects. Their restrictions are bundled superfunctors
`CoefficientPowerModules.induction` and `.restriction`, using the existing
`fullLiftSuperfunctor`. Their vector spaces, balanced quotients and module maps
are unchanged.

## Chosen maps and adjunction

`restrictMap` includes every old-module map between objects of this full
subcategory. `restrictIso` includes both literal maps of a supplied module
isomorphism, retaining its inverse products. Its hom and inverse identities
are recorded explicitly; no inverse is reconstructed.

`CoefficientPowerModules.adjunction` is the chosen ordinary old E/F
adjunction restricted to this category. The unit and counit components are
literally the existing components; both retain parity zero and both triangle
identities. The chosen induction dot is restricted via the existing
`fullLiftTrans`, with its original supernatural parity and literal components.

The concrete consumer uses a connected all-odd two-colour datum, cutoff four,
and the actual pulled-back weighted-empty representable. It proves the
elementary even coefficient square is annihilated, constructs the resulting
power-category object and applies its whole-ideal characterization. It checks
literal E/F objects, chosen unit/counit, both odd dots and the unchanged maps
of a supplied scalar isomorphism. This supplies a concrete object of the
subcategory; it does not identify the weighted quotient with T.

## Boundary

No finiteness of the coefficient family or positivity of the powers is needed
for these category restrictions. The paper's finite positive-power family is
an instance. The weighted/power ideal sandwich, comparison with literal
quotient-algebra modules and the actual vacuum evaluation kernel remain
separate. Parity-shift closure and full finite-family/crossing restrictions
must be supplied before using this category as the final factor target.
