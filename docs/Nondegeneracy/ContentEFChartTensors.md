# Literal tensors for the selected content E/F charts

The matrix comparison in DeformedMatrixComparison section 4 needs the
selected content E/F comparisons to retain the prescribed coefficient
arrows. These formulas are shared by the same-colour and distinct-colour
mate comparisons.

Write Lν for induction along the full content inclusion and Eν, Fν for
induction and restriction along append. The chosen comparison

```
ρ_M : Eν M ≅ R(i::ν)(E(Lν M))
```

includes the actual fully faithful inclusion unit. The theorem
`oldContentAppendRestrictionLinear_tensor` computes its existing raw total
component:

```
ρ_M([g ⊗ b]) = [g ⊗ [id ⊗ b]].
```

There is no homogeneity hypothesis on g or b. The old arrow g is unchanged.

For a module N at content i::ν, the preceding Eν Fν chart uses the chosen
E comparison and then old E applied to the selected restriction-extension
comparison ξ_N. The theorem
`oldContentEFRestrictionNaturalIso_hom_app` records exactly these maps;
`oldContentEFRestrictionLinear_apply` computes their action with the
degree-zero induced component. Its use of that component is justified by
the already verified zero odd component of ξ_N.

`oldContentEFRestrictionLinear_tensor` gives the resulting complete chart:

```
[g ⊗ b] ↦ [g ⊗ [id ⊗ b]],
```

where the inner tensor now lies in L(i::ν)N, at the object obtained by
appending i to the source of g. Thus it is the actual inclusion unit for
the original N vector, rather than an unspecified source equivalence.
`oldContentEFRestrictionLinear` is, by definition, the total component of
the previously selected whole E/F natural isomorphism.

The consumer applies these formulas to mixed representables with both
moving parities, the original append dot as a coefficient arrow, and the
vacuum preceding edge. These charts do not depend on a height sign or a
finite matrix count. Attaching the independently prescribed mate and the
finite parity/product matrices remains the downstream step.
