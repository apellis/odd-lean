# Two odd coefficient actions on the old vacuum

`scripts/NonVacuity/ELVVacuumTwoOddCoefficients.lean` tests the coefficient
order underlying [CoefficientAnnihilation](CoefficientAnnihilation.md) and
the old-vacuum moment calculations. The consumer passes the pinned strict
Lean check with warnings as errors and both compatibility settings.

Use the connected all-odd asymmetric two-colour datum, cutoff four, and
the actual empty-word old representable M. Let e(a) be the literal old
coefficient endomorphism at the empty word. Both actual actions on the
identity vector are evaluated:

    M(e(b))(M(e(a))(1))=e(b*a).

For the distinct odd generators delta_false and delta_true, reversing
the two actions negates the resulting vector. One ordered product is
proved nonzero after both the ELV coefficient quotient and the old
cyclotomic quotient, so this sign test is occupied.

For nonzero occupancy, the exterior basis multiplication rule expresses
the two singleton product as a unit-sign times an exterior basis vector.
The existing bounded coefficient injection preserves that weight-two
product at cutoff four. There is no old cyclotomic relation at the empty
word. An explicit affine-empty PBW coordinate and tensor right unitor
then detect the coefficient tensor identity.

These are the literal category and covariant-representable multiplication
conventions; odd coefficients cannot be reordered as a commutative ground
ring. The consumer does not identify a weighted or swapped factor vacuum,
its normalized caps, or a bubble-series evaluation.
