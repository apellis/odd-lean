# Attaching the actual central augmented matrix

**Status: proposed written attachment, not a Lean theorem.** The abstract
matrix inversion, chosen factor inverses and contentwise coefficient
bounds listed below are established inputs. The literal comparison from
the swapped forward matrix to those inputs, and its residual coefficient
memberships, remain obligations of SwappedActionAssembly §6 and
SwappedHomInversion §§3–6. In particular no concrete ELV instance of
`ProbeReservoir.CentralInvertible` is supplied here.

Fix a colour `i`, a sector `t`, an object `Z : P.H t`, and the actual
weight `ν = P.wt t`. Put `H = D.h i ν`. The restriction to this weight is
essential: the fused window count belongs to this sector. The checked
interface `ProbeReservoir.centralInvertible_of_isIso` in
`Sigma/AugmentedMatrix.lean` still asks
for invertibility of the actual `augPosMat` when `0 ≤ H` and `augNegMat`
when `H < 0`, at every such `Z`.

Let `δ` be one output reservoir content block and let `Eδ` denote the
induced evaluation functor on the finite matrix category. Name the pure
reservoir and pure probe source objects `XR`, `XP`, and the corresponding
target objects `YR`, `YP`; let `O` be the evaluated identity-path object.
The path-to-factor comparisons must give specified source and target
matrix isomorphisms `S+`, `T+`, `S-`, `T-`. The required literal squares
are

    S+.hom ; Eδ(augPosMat c i ν t t Z) = M+ ; T+.hom,
    S-.hom ; Eδ(augNegMat c i ν t t Z) = M- ; T-.hom.

Here `S` points from the model source to the evaluated path source, and
`T` points from the model target to the evaluated path target. With
matrix entries indexed by source and then target, the model maps are

    M+ : XR ⊕ XP → YR ⊕ YP ⊕ O^H,
          XR ↦ [sR, Cx, vR(a)],
          XP ↦ [Dx, sP, rowP(a)],

    M- : XR ⊕ XP ⊕ O^(-H) → YR ⊕ YP,
          XR ↦ [-sR, -Cx],
          XP ↦ [-Dx, -sP],
          Oa ↦ [uR(a), colP(a)].

The positive map is `ProbeWindow.posMap`. The negative map is
`ProbeWindow.negMap` with the displayed negative principal entries;
applying its inversion results must retain these signs, or prove the
specified sign-diagonal comparison first. The minus in `augNegMat` is
part of its definition. The equal-colour crossing signs and normalized
probe left adjunction are also fixed by the existing constructions;
they are not free matrix normalizations.

All path indices and all window indices must occur in these squares.
For a first source comparison one may treat the case where both pure
paths exist. The absent-path cases must then use the proved zero corners
and their explicit charts. At `H = 0` the positive augmented map has an
empty extra window; this case must remain in the result.

The smallest next component is the reservoir window row. For every
`n : ℕ`, identify

    epsEntry c i n ν (reservoir-reservoir path) (empty path) Z

with the prescribed `homContentPostCap ... n Z`, through the actual
roundtrip-path endpoint chart. The companion `etaEntry` identity gives
the `homContentPostCup ... n Z` columns. The statements include `n = 0`
and the entire coefficient carriers. They require collapsing `compList`
for the actual dot/cap or unit/dot word; the finite inverse theorem is
not an input to this calculation. Neither entry uses the unknown mixed
crossing coefficient. `RouquierHomPostPowers` already proves
`homContentPostCap_coordinates` and `homContentPostCup_coordinates` for
the prescribed adjunction. `ELVOld.elvRouquierFamily_adj` in
`ELVRouquierFamily.lean` retains that adjunction definitionally.
`ELVWeightCapRowFamily` and
`ELVWeightLocalInverse` retain the whole chosen cap/unit windows and their
input naturality; supported and absent-content inverse modules supply
the corresponding boundary cases.

The remaining principal matrix entries require the literal pure-factor
mate comparisons and both mixed diagonal bends. The regular-probe
formulas of `ELVProbeCentralBend` and `ELVProbeCentralSlide` identify
specific evaluated bends, with their given dots, unit and cap. They do
not give the required squares on every arbitrary `Z : P.H t` or every
probe content. A regular-input formula alone cannot be substituted for
that whole-map comparison without a proved detection argument.

After the actual square, `CentralInverse/TwoSector` performs the
reservoir cap/cup elimination. `CentralInverse/ResidualComparison`
compares its probe residual with the four invertible window reference
maps. Its explicit obligations include the finite bend expansion
(`hCx` or `hDx`), the off-window contractions (`hout`), and positive
coefficient-ideal membership of the closed errors. In the positive
cap-window case these include

    Dx ; jR ; Cx ∈ J1,
    Dx ; jR ; vR(a) ∈ J1.

The negative cases also require the corresponding closures
`uR(a) ; jR ; Cx ∈ J1`. The degree-zero memberships of window and
inverse reference entries follow from `ProbeWindow.mem_coeffIdeal_zero`
once the chosen content coefficient ideal and endpoint charts are
identified. The existence of an ideal or a nilpotence bound does not
establish the positive memberships for the actual mixed coefficient and
chosen inverse `jR`.

For homogeneous parameters and a positive symmetrizer,
`ELVOld.contentModuleCoefficientIdeal` in `ELVCategoryCoefficients.lean` supplies a
jointly nilpotent coefficient ideal on functors into the actual
exact-content all-module category. Its bound comes from
`contentCategory_end_bounded` and `contentModule_coefficient_eq_zero`.
This avoids replacing the chosen category with an endomorphism algebra.
`ELVContentModuleBound` supplies the corresponding bounded-support and
coefficient-error results for the regular-algebra route when needed.

These bounds may vary with `δ`. Use
`RegularReservoir.isIso_of_component_coefficient_error` in
`CentralInverse/ProductCoefficients.lean`
where its product-module targets match, or its `isIso_of_eval` inverse
assembly on the literal product. Inverses assemble after each content
matrix is proved invertible. No common nilpotence exponent over an
entire weight fibre is required. In particular,
`ProbeReservoir.homCoefficientIdeal` in
`CentralInverse/ReservoirCoefficients.lean` requires a
`RouquierGrading.BoundedAbove` input on the whole weight object; that
input is not supplied by the existing contentwise bounds and should not
be assumed for this attachment.
