# Ordinary cups and caps under content extension

SwappedVacuumCoordinates §6 and DeformedActionAssembly §5 require the
same-colour matrices to use the chosen content induction and restriction
functors. Fix a content word ν and colour i. Write Lν for induction along
the full content inclusion, Eν and Fν for induction and restriction along
content append, and E and F for the established whole-old-category functors.
The chosen comparisons are

```
e_M : L(i::ν)(Eν M) ≅ E(Lν M),
ξ_N : Lν(Fν N) ≅ F(L(i::ν) N).
```

Here `e` is `oldContentAppendExtensionIso`; `ξ` is
`oldContentRestrictionExtensionIso`. Both were chosen using the existing
balanced induction composition maps and the inclusion unit/counit. The
inclusion is fully faithful, and its counit is invertible on the supported
modules in this comparison. No flatness hypothesis is involved.

`oldContentAppendRestrictionIso_unit` proves the ordinary cup square for
the selected restriction of `e`, including its inclusion unit. On a vector
b at s, its value is the old append unit applied to the inclusion unit of b.
Both moving parities and arbitrary inhomogeneous vectors are allowed.

For the cap square, the selected restriction comparison retains the exact
formula

```
ξ_N([g ⊗ b]) = [append(g) ⊗ b].
```

`oldContentRestrictionExtensionLinear` is its literal total component;
`oldContentRestrictionExtensionLinear_tensor` proves this formula.
`oldContentRestrictionExtensionComponent_one` makes its zero odd component
explicit, and `_zero` identifies its even component with that total map.

`oldContentAppendExtensionIso_counit_tensor` proves the square on every nested
generator, and `oldContentAppendExtensionIso_counit` gives the entire linear-map equality:

```
ε_(L(i::ν)N) ∘ E(ξ_N) ∘ e_(FνN) = L(i::ν)(εν_N).
```

The two sides are recorded as `oldContentCounitComparisonLinear` and
`oldContentInducedCounitLinear`. Their source and target are the same
literal coends, and their definitions retain the chosen comparison and
the prescribed degree-zero induction components.

The proof is the literal quotient calculation: flatten the chosen append
comparison, apply ξ on the inserted inclusion tensor, evaluate the old cap,
and use the inclusion balancing relation. Neither coefficients nor module
vectors are assumed homogeneous.

These identities identify the ordinary adjunction entries. Compatibility
of the chosen two-letter content comparison with the signed equal-colour
crossing, and then the source/target charts for the unit/cap matrix natural
isomorphisms, remain separate obligations. In particular the fixed-output
content matrix theorem alone does not identify the chosen content E/F
composites.
