# The actual probe-to-reservoir central mixed block

`Sigma/ProbeToReservoirBend` attaches the `XP → YR` entry `Dx` in
[CentralMatrixAttachment](CentralMatrixAttachment.md). For matrix
applications the displayed region weight is `ν = P.wt t`. The entry
comparison holds at every sector and every full Hom object.

Producer and occupied consumer pass strict scoped checks with warnings
as errors and both backward transparency flags disabled. The consumer
audits all 51 producer-owned declarations against the standard axiom set.

The actual source path uses two probe strands `Eᵢ Fᵢ`, and the target
uses two reservoir strands `Fᵢ Eᵢ`. Both paths are constructed on every
sector, including `(0,0)`. The existing general sigma-entry calculation
forces intermediate sides `R,R,P,P`. Its crossing entry is the actual
RP coefficient `c.a`.

`probeCapFactorIso` and `capImage_probe_factor` identify the source path
and its cap with the canonical shifted precomposition adjunction. This
preserves the `T.leftAdjoints` normalization used by the generators.
`probeToReservoirCoefficientIso` transports the complete formal right
sector of the RP coefficient. `probeToReservoirCoefficient` conjugates
the given `c.a` by that computed object chart.

The native `probeToReservoirBend` is the whole-map word

    ηR(EP(FP Z)) ; FR(a_native(FP Z)) ; FR(ER(εP Z)).

Here the reservoir unit and probe counit are their specified shifted
adjunction components. `sigmaEntry_probeToReservoir` proves that the
actual entry is this word through the fixed probe-cap and reservoir-cup
charts. Computed object and weight transports are eliminated in a
normalized value lemma before instantiation. The coefficient chart is
constructed from `c.a`, and the proof evaluates the actual three
cup/cross/cap layers. No operator-comparison or detection premise occurs.

`sigmaEntry_probeToReservoir_negative` retains the minus of the negative
augmented matrix: its entry, conjugated by the same charts, is the
negative native bend. There is no height or positive-content assumption
on either formula, so height zero and the boundary corners are retained.

The paired consumer constructs complete positive-level asymmetric
two-odd ELV factors, both multicolour records, and their selected
adjunctions. At `(0,0)` it checks both odd colours and both signs, with
identity coefficient data and the prescribed reservoir-dot coefficient
data. It proves that the RR source edge and PP target edge are absent
there and that the fused height is zero. The literal regular-power
empty-word input contains an independently surviving product of the two
odd coefficient classes. These coefficient data carry no inverse
assertion; the consumer does not construct the required unit-dot probe
or a `CentralInvertible` instance.

The reverse `XR → YP` bend, probe principal comparison, complete matrix
chart square, and positive residual coefficient-ideal memberships remain
separate obligations. The present formula preserves arbitrary `Z`; no
full-weight uniform nilpotence bound is inferred from contentwise bounds.
