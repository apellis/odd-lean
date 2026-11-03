# Full moment operators on the literal power vacuum

This attaches the all-vector interpretation of the reservoir moments in
[SwappedVacuumNonpositiveBubbles, §2](SwappedVacuumNonpositiveBubbles.md)
to the actual regular A/T old vacuum.
`ELVCoefficientPowerMomentMaps` and its connected occupied consumer pass
scoped Lean checks with warnings as errors and both pinned compatibility
settings. All 25 owned declarations pass the standard axiom allowlist
audit. Full CI remains the integration gate.

`momentMap(i,N,n)` is the literal composite lambda D^n u as an
endomorphism of A/T, with the actual ordinary append unit, signed
induction dot and prescribed inverse row. Its value on 1 is exactly the
previously constructed `signedMoment`.

The ordinary unit respects the original coefficient action. The signed
dot is supernatural against that full coefficient action; a scalar
intertwining identity propagates this sign through every dot power.
Combining this with the inverse row's already proved coefficient law
proves `momentMap_coefficient`:

    momentMap_n([a]) = (−1)^((n+N−1)p_i |a|) [a] h_n.

No coefficient is moved past another without its sign.
`momentMap_mem` retains the total parity (n+N−1)p_i. Consequently h_n
has this parity in literal A/T. Homogeneous coefficients in A/T lift to
homogeneous coefficients of the original ELV coefficient algebra.
Its existing graded commutativity descends through the actual quotient,
including the defining ideal T. These facts convert the displayed right
factor to the original left multiplication and extend from homogeneous
to arbitrary vectors by the two parity projections.

Thus `momentMap_apply` and `momentMap_eq_mulLeft` prove, for every
exponent, either moving parity and every z in A/T,

    lambda D^n u(z) = h_n z,
    momentMap_n = leftMultiplication(h_n).

No ordinary commutativity of A/T or bubble-value hypothesis is used.
`momentMap_even`, `momentMap_odd` and `momentMap_first_odd` now turn the
complete scalar odd-colour series into literal endomorphism identities
on every coefficient vector. In particular the first higher map is
left multiplication by (−1)^(N+1)[δ_i] for every positive cutoff of an
odd colour.

The connected two-odd-colour consumer retains cutoffs four and five,
checks both complete endomorphism series at every coefficient index,
and verifies odd map parity at both cutoffs. The product of the two
independent exterior classes is proved nonzero in A/T using its actual
bounded coefficient injection and a unit-sign exterior basis product.
Applying the first map to the other odd coefficient therefore checks
both its multiplication order and nonzero value. Inputs 1+δ_j test the
same identities on inhomogeneous vectors. A mixed datum also checks
the all-vector identity for an even moving colour at every exponent.

The source-word whiskering of these maps must retain the induction
map's kernel twist. The probe numerator, identification with the mixed
inverse caps, final swapped bubbles and the vacuum evaluation-kernel
identity remain separate.
