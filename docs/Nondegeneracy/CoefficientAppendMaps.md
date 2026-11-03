# Coefficient maps and appended source words

This supplies the source-word coefficient compatibility required by `SwappedVacuumCoordinates.md`, §6, following `CoefficientModuleMaps.md`.

`coefficientModuleAction_induction` identifies append induction of the full coefficient module endomorphism with the original coefficient action on the induced module. `coefficientModuleAction_restriction` gives the corresponding restriction identity. Both hold for arbitrary coefficients, including inhomogeneous ones.

The induction proof works separately with each homogeneous projection b of a coefficient. On a balanced tensor, induction of its module map gives

    twist_p(h) ⊗ M(e(b))(m).

Balancing moves e(b) into the kernel. The coefficient slide then identifies this with

    (h ≫ e(b)) ⊗ m,

which is the target coefficient action. This keeps the whole-kernel parity twist and the original coefficient order.

`powerModuleCoefficientAction_induction` and `powerModuleCoefficientAction_restriction` descend these identities to the literal quotient A/T inside the preserved T-annihilated module category. They use quotient surjectivity and the preceding identities; no weighted algebra substitutes for A/T.

The paired consumer retains two independent occupied odd generators at cutoffs four and five. For append of the first colour, take the second odd coefficient as the tensor kernel and apply the genuine first odd coefficient module map. The signed result is the append unit of the ordered product δ₀δ₁. That vector is nonzero: the exterior/window argument proves δ₀δ₁≠0 in A/T, and the prescribed last inverse row after three dots proves injectivity of this append unit. This tests the source-whiskering sign on an occupied append object. The consumer also checks both quotient E/F identities and audits all four producer declarations.

These identities do not yet attach the chosen swapped cup/cap closure or its probe polynomial numerator.
