# Signed-height residual inversion

This is the matrix step of SwappedHomInversion §§4–6 and the six
subcases of ProbeWindowInverse §3. Let `r` be the reservoir cap height
and `p` the probe cap height, so the fused height is `r + p`.
The comparison must distinguish the sign of `p` as well as the signs of
`r` and `r + p`.

| Fused window | Reservoir window | Probe window | Reference map |
|---|---|---|---|
| cap | cap | cap | case (c), nonnegative probe height |
| cap | cap | unit | case (c), negative probe height |
| cap | unit | cap | case (a) |
| unit | cap | unit | case (d) |
| unit | unit | cap | case (b), nonnegative probe height |
| unit | unit | unit | case (b), negative probe height |

`CentralInverse/ResidualComparisonNegative` supplies the two
negative-probe attachments absent from `ResidualComparison`:
`isIso_posMap_of_cap_of_cup_window` and
`isIso_negMap_of_cup_of_cup_window`. They use the already proved
`isIso_caseC_of_neg` and `isIso_caseB_of_neg`. The latter reference map
uses the prescribed negative rows; its sign comparison negates both
off-corner blocks. These are the negative-height arguments already
written in ProbeWindowInverse, not extra hypotheses on the probe.

`CentralInverse/SeparatedClosures` derives the three closed residual
errors from the finite bend equations. Write

```
z_r = x^(-r-1) ; v,     w_s = u ; y^(-s-1),
Dx = -Σ_r q^(r+1) • (z_r ; uR_r),
Cx =  Σ_s q^(s+2) • (vR_s ; w_s).
```

If every chosen reservoir principal closure `uR_r ; jR ; vR_s` lies
in `J₁`, and the outside probe windows lie in `J₀`, distribution gives

```
Dx ; jR ; vR_s ∈ J₁,
uR_r ; jR ; Cx ∈ J₁,
Dx ; jR ; Cx = -Σ_r Σ_s q^(r+1) q^(s+2) •
  (z_r ; uR_r ; jR ; vR_s ; w_s) ∈ J₁.
```

The declarations `separated_cap_closure`, `separated_unit_closure`,
and `separated_closed_error` prove these memberships without grading
any surrounding morphism. The two series may have different finite
lengths. The paired coefficient consumer uses a nonzero square-zero
ideal over `ZMod 9`, odd sign `q = -1`, three terms in each series, and
a nonzero mixed closed error.

The literal negative augmented map has minus all four principal
entries, but unchanged unit columns. `pureSourceSign` is the diagonal
`(-1, -1, 1)` on its source. Its square is the identity, and
`pureSourceSign_comp_negMap` identifies its composite with precisely
that signed matrix. Thus `isIso_negMap_neg_principals` transfers the
inverse after the unchanged normalized probe slide has been used.

`CentralInverse/SignedResidualWindows` collects these calculations.
Its two inversion theorems use integral heights and split into all six
rows of the table. They assume the specified local factor windows,
reservoir principal closures and off-window contractions, and the
finite bend series. They derive every mixed closed error and then lift
through the jointly nilpotent coefficient ideal. They do not assume
residual invertibility. `J₀` is required to contain every morphism;
this is supplied by the chosen content coefficient ideal.

The intended concrete attachment is `Sigma/PaddedResidualInversion`.
It uses the chosen ELV coefficient, the whole-output padded bend series,
`ReservoirWindowCoefficientIdeal`, and the normalized OLD probe windows.
The output content is fixed before choosing the series length and the
coefficient-ideal bound. Product assembly of the resulting finite-matrix
inverses therefore does not require a uniform bound over the weight
fibre. Exact support is retained on the input Hom object, and no
injectivity of content-to-weight is used.

`SeparatedClosures` and its concrete consumer pass strict scoped checks;
all nine owned declarations pass the standard axiom audit.
`ResidualComparisonNegative` and its concrete pair pass with five audited
declarations. `SignedResidualWindows` and its paired rational-module
consumer pass with all 22 declarations audited, exercising both signed
height theorems with every hypothesis proved. The actual supported ELV
matrix attachment and full integration remain separate gates.
