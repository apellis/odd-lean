# Module normalization before Hom precomposition

For `SwappedActionAssembly.md`, §5 (A14), the prescribed last inverse row
must be used together with the same signed dot before Hom transport.
`ELVProbeCapModuleWindow` retains the regular empty probe as a module.
Its `moduleDot` is exactly the restricted induction dot whose evaluated
endomorphism occurs in the ground normalization window.

`unitDotColumn_cap` promotes the already proved component window to an
equality of module maps, on every object of the empty-content category.
`module_cap_dot_unit` expresses this as ordinary unit, power of that dot,
and prescribed cap. `moduleDot_odd_polynomial` proves the signed
`(D² + 1)^m = 0` relation on this same module endomorphism.

These statements require no left unit or triangle identities. They are
inputs to literal contravariant Hom precomposition; they do not identify
an entire Rouquier family, a transpose dot, or a mixed slide. The consumer
uses the regular rational probe at the two odd cutoffs 2 and 4, including
all powers in the normalization window and the top identity column.
