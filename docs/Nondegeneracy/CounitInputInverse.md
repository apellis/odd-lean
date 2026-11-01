# Ordinary dotted-counit input inverse

DeformedMatrixComparison (5) gives the cap-row change of coordinates. The
input inverse from DeformedRouquierMatrix, section 4, therefore gives an
inverse on the induction-restriction carrier itself.

For an odd moving colour j and arbitrary old words v,t, put J equal to
shiftedSourceCanonicalEquiv. The output change is crossing negation and, in
row r, the whole-output twist oldTwist(r+1) followed by multiplication by
the unit (-1)^choose(r+1,2). This scalar is (-1)^(r(r+1)/2), including the
source parity shift.

The declarations are:

- shiftedCapRow_normalization: the prescribed scalar and whole-output twist
  turn the shifted contraction/input-dot row into the ordinary adjunction
  counit after the ordinary induction-dot power.
- counitInputRowEquiv and counitInputOutputEquiv: these are invertible changes
  of the specified output coordinates.
- sourceInputDot_iterate_carrier: all powers intertwine with the induced
  coefficient-module equivalence.
- counitInputMatrixEquiv: composition of the canonical source equivalence,
  the checked shifted input inverse, and that output change.
- counitInputMatrixEquiv_fst: the first component is exactly -toCyclotomic(Jz).
- counitInputMatrixEquiv_cap: every other component is literally the ordinary
  adjunction counit applied to the corresponding ordinary induction-dot power.

The degree condition is outputSDegree = endpointQPDegree + m. The result
includes m=0 and uses only the existing commutative coefficient ring; there
is no field, dimension, flatness, assumed source equivalence, presumed
operator equality, or mate-equality hypothesis.

The producers and concrete consumers pass scoped builds with warnings as
errors. The new consumer uses distinct mixed-B2 endpoint orders, positive
cutoffs and three cap rows; it checks both inverse identities, the first
component, every ordinary counit row and the nontrivial row-two sign.
Full CI and its global audit remain integration gates.

The first component is deliberately stated as -toCyclotomic after J. Its
identification with the ordered categorical same-colour mate under
upperHomEquiv remains a separate proof. A componentwise linear equivalence
does not alone assert the complete module-valued categorical decomposition.
