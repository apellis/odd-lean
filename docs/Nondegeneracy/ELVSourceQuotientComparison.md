# The literal old ELV quotient has its specified source kernel

`ELVSourceQuotientComparison.lean` proves the presentation comparison needed
to attach the word reversal of `SwappedVacuumCoordinates.md` §§5–6 to actual
reservoir Homs. All parameters and coefficients are the existing full ELV
ones. The result holds over an arbitrary commutative ground ring.

The coefficient step proves

`ker(elvHomQuotient) = ELVCoefficientRelationSpan`.

The same equality holds for the categorical coefficient quotient
`elvQuotientMap`. Surjectivity and tensor right exactness give the reverse
kernel containment. A pure coefficient-kernel tensor factors as an affine
unit-coefficient prefix followed by its coefficient at the target word.
This factorization introduces no coefficient/parity commutation assumption,
so applies to arbitrary full coefficients, including nonhomogeneous ones.
Length-mismatched contexts vanish in the actual affine category.

The cyclotomic step proves

`map(elvQuotientMap, ELVRelationSpan) = ELVOld.ideal`.

The forward direction uses the actual odd/even first-position generators.
The reverse direction lifts every full coefficient/context multiplier through
the surjective quotient map. Pulling back this image gives

`comap(elvQuotientMap, ELVOld.ideal) = ELVRelationSpan`.

Thus `sourceToOldHom`, the existing coefficient quotient followed by the
literal old ideal quotient projection, has kernel exactly `ELVRelationSpan`.
Its target is definitionally an actual `OldCategory` Hom; no replacement
quotient or flatness premise is introduced.

The paired consumer instantiates the coefficient and full old kernels at the
asymmetric two-odd-colour datum with Cartan entries −2 and −4. It explicitly
types the target as an actual old category Hom. At cutoff zero it proves that
the odd source tensor `delta_false` times the empty identity is nonzero by
the joint coefficient/affine PBW basis and belongs to the actual quotient
kernel through the retained odd top relation.

Verification: strict pinned producer and paired consumer checks passed.
The consumer audits all 17 producer-owned declarations, including private and
generated ones, against `propext`, `Classical.choice`, and `Quot.sound`.

Literal coefficient-power augmentation and attachment of this kernel to the
half-turn's bounded detection are subsequent steps. This kernel theorem does
not identify a vacuum evaluation or assert nondegeneracy.
