# Identifying the raw mixed coefficient

**Scoped-checked; full CI pending.** The producer and its paired even/odd consumer pass with warnings as errors and the pinned compatibility settings. The consumer audits all seven owned declarations, including generated declarations, against `propext`, `Classical.choice` and `Quot.sound`.

The same-colour mixed crossing in SwappedActionAssembly §2 (A6) uses an inverse-first odd coefficient. `elvRawMixedCoefficient` was constructed numerator-first on every arbitrary pre-induction functor. Equality should be established from the prescribed identity and the already proved denominator unit, without unfolding either choice of unit or normalizing entire functor endpoints.

`elvRawMixedCoefficient_eq_of_even_identity` and `elvRawMixedCoefficient_eq_of_odd_identity` state the needed uniqueness on the actual full-ELV weight-module target. A single identity suffices: right composition by a unit is injective. The even identity has value the identity morphism; the odd identity has value the literal probe dot minus the reservoir dot. No homogeneity premise on the candidate coefficient is needed.

`elvRawMixedCoefficient_odd_inverseFirst` then compares the raw odd coefficient with the inverse-first formula. The latter satisfies its one-sided identity by the unit inverse product. This argument does not reorder the coefficient algebra or add a commutation hypothesis.

At the prescribed mate specialization `Z = ΠH ≫ F`, the existing even and odd coefficients satisfy the same identities. `elvMixedEvenCoefficient_eq_raw` and `elvMixedOddCoefficient_eq_raw` identify them with that raw specialization. Finally `elvRawMixedMateDot_isIso` combines the two moving parities, retaining the same raw coefficient and both chosen Hom shifts.

The paired consumer applies these comparisons and the parity-unified mate theorem to degree-six even and odd probe actions over the rationals, with both Hom shifts nontrivial. Its arbitrary-input odd example does not assume a restriction factorization. Full factor-family and concrete `ProbeReservoir` assembly remain separate.
