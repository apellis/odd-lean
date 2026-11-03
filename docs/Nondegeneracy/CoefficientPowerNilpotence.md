# Fixed-content dot nilpotence for the literal power modules

This supplies the positive-dot input of
[SwappedNondegeneracy, §2](SwappedNondegeneracy.md) for the actual old
coefficient-power module category.
`ELVCoefficientPowerNilpotence` and its paired occupied consumer pass
scoped Lean checks with warnings as errors and both pinned compatibility
settings. All 13 owned declarations pass the standard axiom allowlist
audit. Full CI remains the integration gate.

Let T be the ideal of the prescribed even elementary powers in the full
ELV coefficient algebra. For finitely many colours, the proved sandwich
contains W_(R+1) in T, where R is `elvPowerWeightBound`. Consequently each
literal T-annihilated old module descends to the weighted old category at
bound R+1 on unchanged vector spaces and maps. This is descent along a
proved quotient arrow, not identification of the two coefficient ideals.

The existing `truncatedAppendDot_pow_zero` follows from the positive
integer degree and fixed-content support bound. At output content ν+[i],
balanced induction has only generators whose source content is ν:
every other coefficient arrow is zero by content conservation. Its signed
iteration formula therefore transfers the same source exponent to the
truncated coend dot, including the twist of the entire coefficient arrow.

The selected `appendWeightedModuleIso` is an invertible intertwiner of
this truncated dot with the original `actualInductionDot` on old
modules. `weightedOldInductionDot_pow_zero` transports the exponent
through that exact isomorphism. Restriction after weighted descent
recovers the original old action, so the conclusion concerns its original
signed dot. No arbitrary module is assumed finite dimensional or graded.

`coefficientPowerInductionDot_pow_zero` now states that, given a
symmetrizer and homogeneous parameters, for each ν and i there is e>0
such that

    actualInductionDot(i, M, w)^e = 0

for every literal T-annihilated module M and every old output word w
permuting ν++[i]. The exponent may depend on this fixed content. It does
not depend on M. There is no assertion of one exponent over an entire
weight fibre or over the unbounded category of words.

The connected asymmetric two-odd-colour consumer uses cutoff four and
fourth powers of every even elementary generator. It applies the result
to all power-annihilated modules, then to the actual old regular A/T
vacuum. Extraction proves that the third dotted unit on a surviving odd
coefficient class is nonzero. Thus the nilpotence exponent in this
occupied example must exceed three.

The mixed inverse caps, coefficient-series recovery and final swapped
vacuum action still require attachment. No vacuum evaluation-kernel
identity or all-height bubble theorem is asserted, and no nilpotence is
inferred from finite dimension alone.
