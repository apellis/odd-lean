# Reservoir closures in the source coefficient image

The positive-degree input to the central inverse argument must concern
coefficients of the chosen reservoir action. It is not a grading of all
morphisms between arbitrary, ungraded reservoir modules.
[ELVCategoryCoefficients](../../OddMath/QuiverHecke/CyclotomicAction/ELVCategoryCoefficients.lean)
defines `ContentCoefficient`, `contentRealize`,
`contentCoefficientDegree` and `contentModuleCoeffGrading`. The last
object grades only the realization image of central families on the
exact-content source category. Its `contentModuleCoefficientIdeal` is
jointly nilpotent at fixed content, by `contentCategory_end_bounded` and
`contentModule_coefficient_eq_zero`.

Fix the acting scalar family `A`, its homogeneity proof, a symmetrizer
`sy`, the truncated reservoir parameters, and a central content `β`.
Let `W` be the chosen `elvRouquierFamily`, at a highest weight satisfying
the cutoff pairing. Let `x` be the weight of `β` and use the adjacent
steps `x-αᵢ → x → x+αᵢ`. Write `y` for the principal inverse entry of the
chosen local record: `invPos.f'` or `invNeg.f'` in its applicable height
range. At height zero either orientation has the same principal inverse.
For nonnegative integers `r,s`, the actual closure is

\[
 t_{r,s}=(\eta_2;\,x_2^r F_2);\,y;\,(F_1x_1^s;\,\varepsilon_1).
\]

Every unit, counit, dot, and principal inverse in this formula is the
one selected by `W`. For a weight block `δ` of content `β`, the direct
attachment statement needed by the coefficient ideal is

```text
∃ c : ContentCoefficient D A cutoff N β,
  c ∈ contentCoefficientDegree D A cutoff N β sy hA
        (2 * sy.d i * (r + s + 1)) ∧
  ∀ M : ELVWeightProduct D A cutoff N Λ x,
    t_rs.total M δ = (contentRealize D A cutoff N β c).total (M δ).
```

The displayed statement is a proof target, not an existing declaration.
It keeps the literal chosen whole-weight closure and its exact-content
output. Equivalently, after constructing its natural exact-content
attachment `Cβ(r,s)`, the last conjunct is
`contentRealize c = Cβ(r,s)`. Since `sy.pos i` and `r+s+1 > 0`, this
witness has strictly positive degree and supplies the required generator
of the existing coefficient ideal.

The next sharp degree statement is pointwise on representables. For
`v : ContentCategory D A cutoff N β` and either parity `q`, it asks for

```text
ModuleYoneda.evaluate D A cutoff N β
  (contentRepresentable D A cutoff N β v)
  (Cβ(r,s).app q (contentRepresentable D A cutoff N β v))
  ∈ truncatedDegree D A cutoff sy hA N
      v.obj.word v.obj.word (2 * sy.d i * (r + s + 1)).
```

`ModuleYoneda.evaluate` evaluates a module map at the identity of `v`.
[ELVModuleYoneda](../../OddMath/QuiverHecke/CyclotomicAction/ELVModuleYoneda.lean)
already supplies `homEquiv`, `fromElement`, `evaluate_fromElement`,
`fromElement_evaluate`, `app_formula` and the parity-projection formula.
These retain the total-parity twist. They are the reconstruction tools
for a source central family and its action on every exact-content module;
the represented degree assertion above remains to be proved.

The native matrix comparisons identify the prescribed maps, but their
existing grading assertions do not supply this integer degree.
[ELVModuleMatrixInverse](../../OddMath/QuiverHecke/CyclotomicAction/ELVModuleMatrixInverse.lean)
constructs `moduleUnitMatrixIso` and `moduleCapMatrixIso`, their literal
forward maps, and their even inverses.
[ELVWeightedMatrixInverse](../../OddMath/QuiverHecke/CyclotomicAction/ELVWeightedMatrixInverse.lean)
transports these through the canonical source, target, and finite-family
charts. `weightedModuleUnitMatrixIso` and
`weightedModuleCapMatrixIso` therefore use the specified old inverses.
`ELVInductionKernelGrading`, `ELVGradedKernelEquivalence` and
`ELVParityMatrixCoordinates` prove statements about the `ZMod 2` sum
parity. They do not prove integer homogeneity of the decoded inverse.

The needed matrix step is to give the represented forward finite matrix
its integer source and target shifts, prove that it is homogeneous of
degree zero, and conclude that its inverse, hence its decoded principal
entry, is homogeneous of degree zero. The unit and cap shifts then give
`2*sy.d i*(r+s+1)` for the closure. This should be attached to the actual
represented coefficient kernels and their chosen inverse, using existing
graded inverse linear algebra where applicable. No grading on arbitrary
module morphisms is required.

The principal entry is determined by the finite forward matrix. The
`SuperSumInvFrom.hom_ext` and `SuperSumInvTo.hom_ext` lemmas in
[AugmentedInverseNaturality](../../OddMath/SKM/AugmentedInverseNaturality.lean)
supply the relevant detection identities. Thus final choices of
outside-window inverse rows are irrelevant to the principal comparison.
The naturality constructor explicitly zero-extends those unconstrained
rows; it retains the principal inverse.

[SKM.RouquierGrading.closure_mem](../../OddMath/SKM/RouquierGrading.lean)
proves the desired degree formula when an entire `RouquierGrading` is
already supplied. Its `graded` field grades all morphisms of each Hom
category. That structure has not been supplied on the all-module
reservoir target and cannot be inferred from the parity-only matrix
comparisons. The source-coefficient-image statement above is the
precise attachment needed here.
