# Polynomial coefficient-extraction cap on the power vacuum

This computes the coefficient-extraction candidate in `SwappedVacuumNonpositiveBubbles.md`, §§3–4, on the original literal coefficient-power vacuum. It does not identify the candidate with the mixed inverse cap: that still requires the specified mixed slide, probe polynomial and chosen inverse data.

Write u for the ordinary unit, D for the actual signed induction dot and λ for the prescribed last inverse row, with target A/T. For the odd probe polynomial g(T)=(T²+1)^M define

    polynomialCap = λ ∘ (D²+1)^M,
    polynomialCapMoment_n = λ ∘ (D²+1)^M ∘ D^n ∘ u.

These are the maps in `ELVCoefficientPowerPolynomialCap`. The closure is an endomorphism of the entire ground-ring module A/T, including all odd and inhomogeneous vectors.

`polynomialCapMoment_sum` proves the ordered binomial identity

    polynomialCapMoment_n
      = Σ_(j=0)^M choose(M,j) · momentMap_(2j+n).

Only the single operator D and central natural-number coefficients enter this expansion. No commutativity of the coefficient algebra A/T is assumed.

At zero external height the reservoir cutoff is N=2M>0. Every lower even power 2j<N is below the top extraction degree N−1, so the actual inverse-row window kills it on every input vector. The monic top term gives `polynomialCapMoment_zero_height`:

    λ ∘ (D²+1)^M ∘ u = momentMap_N.

For an odd colour, the proved all-vector first higher moment is left multiplication by (−1)^(N+1)δ. Since N is even, `polynomialCapMoment_zero_height_odd` identifies the candidate closure exactly with L_(−δ), using the original exterior coefficient and its original left multiplication order. No cap rescaling or bubble value is supplied as a premise.

The consumer uses the connected all-odd datum at cutoffs four and six with positive elementary powers. Its independent odd generators have a nonzero product in the actual quotient, proved by the exterior basis and bounded coefficient injection. Applying the first candidate closure to the other odd generator gives −δ₀δ₁≠0; reversing colours gives +δ₀δ₁. An inhomogeneous input is also checked. Every owned producer declaration is audited.

The next attachment is to prove that this polynomial functional is the prescribed mixed principal-inverse cap. That is the role of the existing principal recovery theorem once the actual mixed maps and their slide are constructed; none are assumed to exist here.
