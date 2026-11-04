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

`Sigma/PaddedResidualInversion` attaches these statements to the chosen
ELV coefficient. `SupportedSectors.centralFactorMatrix_content_isIso`
proves both signs of the literal padded factor matrix on every supported
Hom input and every output content, at the actual sector weight. Its
inputs are the specified datum and parameters, a positive symmetrizer,
homogeneity, and the supported input object; it assumes no bend,
contraction, closure, residual inverse, or nilpotence equation. The
finite index type used by the chosen factor construction is retained.

`SupportedSectors.centralAugmentedMatrix_isIso` then applies the literal
factor comparison squares and `RegularReservoir.isIso_of_eval`. It gives
invertibility of the actual `augPosMat` for nonnegative fused height and
`augNegMat` for nonpositive fused height, including both zero-height
maps. The output content is fixed before choosing the series length and
the coefficient-ideal bound. Product assembly therefore requires no
uniform bound over a weight fibre. The series length need only dominate
the reservoir window size: all principal closures are available at
arbitrary dotted indices, so fused windows longer than the series are
also covered.

The paired consumer retains the nonzero selected tensor path for two odd
colours whose contents collide in root weight, and applies both concrete
zero-height augmented inverses at the tensor vacuum. Exact support is
retained on the input Hom object. The theorem neither identifies
colliding content blocks nor supplies `ProbeReservoir.CentralInvertible`
on arbitrary unsupported objects of the raw Hom category.

The remaining presentation interface is objectwise leftward inverse
extraction on supported inputs. The existing raw `Generators` and
`LeftwardData` types allow conditional inverse entries at every object,
with zero used when an augmented matrix is not invertible. On supported
inputs the checked central matrices select the inverse branch; the
remaining local inverse identities, their naturality and parity in
supported contexts, and their attachment to the defining relations must
retain that support restriction.
