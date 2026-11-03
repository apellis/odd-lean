# The full homogeneous half-turn and its literal boundary quotient

`SwappedVacuumCoordinates.md` §§4–5 uses a signed affine word reversal `U`
with full exterior coefficients, target parameters `parameterTwist D Sc`,
and weight −1 on equal-colour crossings. The existing modules
`HalfTurn/Mirror`, `SuperFlip`, and `Composite` already construct this map
through the actual contextual presentation ideal. In particular, the
mixed quadratic and corrected braid verifications hold for general permitted
interior parameters; they are not assumed compatibility hypotheses.

The existing `CornerIdeal`, `Involution`, `IdealIdentification`, and
`CoefficientGenerators` modules prove that the full coefficient linear map
`htCoef` is bijective and identifies the transformed last-boundary ideal
with the first-boundary ideal for the twisted parameters, together with
any specified homogeneous coefficient generators. These are source results
predating this batch. Their seven producers have now passed strict pinned
source checks and an audit of all 332 owned declarations, including private
and generated declarations, with only the repository's allowed axioms.

The new `HalfTurn/Homogeneous.lean` fills the remaining homogeneous API:

* `htPres_mem_parity` and `htPres_comp` extend the diagram formulas to all
  homogeneous affine morphisms by a same-parity diagram span induction.
* `htCoef_mem_parity` preserves total coefficient-plus-affine parity.
* `htCoef_comp` reverses arbitrary homogeneous coefficient-extended
  compositions with the sign of the two total parities. Its coefficient
  commutation input is the separately proved supercommutativity of the
  full polynomial/exterior algebra. No odd coefficient is specialized.

`HalfTurn/QuotientEquivalence.lean` then uses the existing ideal image
identity to descend `htCoefEquiv` to the literal quotient Homs:

`coefficientHom(Sc;s,t) / K_(N,T)`

is linearly equivalent to

`coefficientHom(parameterTwist Sc;reverse t,reverse s) / (I_N + (T))`.

The representative formulas are exactly `htCoef` forward and `htCoefInv`
backward. This statement preserves the distinction between the two
boundary ideals; it does not identify the first-boundary quotient with
itself under reversal.

The paired consumer `QuiverHeckeHalfTurnHomogeneous.lean` uses two odd
colours with off-diagonal Cartan entries −4 and a nonzero interior
coefficient `s(2,2)=2`. It checks the target value −2, the corrected braid
and mixed quadratic compatibility, the actual descended contextual
functor, and the equal-colour crossing in arbitrary contexts. Two odd
coefficient factors on even identities test the total-parity minus sign.
The quotient equivalence is instantiated with both an even and an odd
specified coefficient generator.

Verification: both new producers and the paired consumer passed strict
pinned checks. The consumer audits all 351 declarations owned by the seven
existing producers and the two new producers, including private/generated
declarations, against `propext`, `Classical.choice`, and `Quot.sound`.
No new axioms, proof placeholders, or increased elaboration budgets are used.

The remaining research task is to attach these maps to the chosen reservoir
and vacuum observations and prove the needed surviving coefficient bounds;
this batch does not assert the odd nondegeneracy conjecture.
