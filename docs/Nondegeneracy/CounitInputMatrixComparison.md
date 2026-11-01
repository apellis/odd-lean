# Canonical source and counit input-matrix comparison

This attaches the checked arbitrary-Hom input inverse to the fixed categorical
source, counit and induction dot from DeformedMatrixComparison, section 3.
Moving colour j is odd; both old words are arbitrary, and all supplied
polynomial/exterior coefficient classes remain.

## The literal coefficient source

The moving coefficient module packages exactly coefficient(D.parity j).
Its induced carrier is literally Source(j,v,t). An even pointwise-identity
module isomorphism compares it to coefficient(1) before induction.
`coefficientOneSourceEquiv` is the component of the induced module iso.
Its construction transports the actual modules, rather than equality-casting
an entire coend.

The total component of the fixed `shiftedSourceParityIso), followed by this
comparison, gives `shiftedSourceCanonicalEquiv` from the actual
Ind(Res(oldRepresentable(v))) component at t to Source(j,v,t). The inverse
uses the same module iso. `shiftedSourceCanonicalEquiv_counit` retains the
actual adjunction counit square. No chosen source equivalence is an input.

## Fixed categorical cap and dot

On the coefficient(1) induction, the contraction is the actual shifted
counit followed by full output parity, and the input dot is the actual
induction dot after the actual source grading. The coefficient shift
contributes its minus on tensors. Transport through the fixed coefficient
module iso defines `actualSourceInputContraction` and
`actualSourceInputDot` on literal Source.

The new comparison proves their tensor and q-generator formulas, then

    actualSourceInputContraction = offDiagonalInputContraction
    actualSourceInputDot = offDiagonalCrossingInputDot.

These are `sourceInputContraction_eq` and `sourceInputDot_eq`.
The whole old coefficient is twisted, including exterior coefficients.
The equalities are proved from the constructed counit/dot maps on all
balanced classes; no comparison equality is assumed.

## Transferring the inverse

`offDiagonalShiftedInputMatrix` uses the prescribed cyclotomic crossing
and rows formed from those fixed categorical E and X maps. Its equality to
the checked input matrix gives `offDiagonalShiftedInputMatrixEquiv`
at every negative or zero height. No second triangular elimination proof
is needed.

The concrete consumer uses the same connected mixed B2 case with three
cap rows and positive cutoffs as the input-matrix consumer. It checks both
inverse products and both operator equalities. The canonical-source consumer
uses different mixed endpoint orders and checks both inverse products and
the actual counit square. All included producers/consumers passed scoped
warnings-as-errors checks with the pinned transparency options. Owner axiom
audits cover the comparison, source component equivalence, cap input and
coefficient module declarations.

Full CI and its global axiom audit remain integration gates. The matrix
here is the shifted input matrix. Higher ordinary-counit row sign/twist
normalization, the ordered mate's common-row minus, and naturality/whole
module realization are the separate remaining attachments.
