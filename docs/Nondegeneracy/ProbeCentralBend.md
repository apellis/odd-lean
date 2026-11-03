# The mixed diagonal and its evaluated central bend

Source: SwappedHomInversion §3 (A6), (3)–(5), and
SwappedVacuumNonpositiveBubbles §1 (1). These results concern odd colours
and the actual regular-probe evaluation, before identification with the
complete chosen swapped matrix.

`evaluatedMixedDiagonal` is the prescribed rational A6 expression on the
native mixed induced module. Its probe dot is exactly `shiftedPreDot`,
including its canonical source-parity sign. It is not the unsigned
`coordinatePreDotPower 1`. `shiftedPreDot_isUnit` and
`diagonalPreDot_isUnit` use its signed probe polynomial only on this
regular-probe carrier. No inverse on all OLD modules is asserted.
`diagonal_dots_exchange` retains the actual super-interchange sign.

The given fixed-content reservoir grading proves
`diagonalPostDot_pow_zero` and `evaluatedPostDot_pow_zero`. These use a
positive symmetrizer, homogeneous parameters and finite colours, and work
on every module at the specified content. No module finite-dimensionality
hypothesis or uniform bound over a weight fibre is used.

`evaluatedMixedBend` is the chronological composite of the given post
unit, restricted A6 diagonal and induced prescribed shifted pre-cap.
`evaluatedMixedBend_constructed_counit` identifies that cap with the exact
two-morphism counit of the finite-local pre-Hom adjunction when its two
adjacent Rouquier records, squares and braid are supplied. The two native
cap-normalization signs remain in that construction; its unit is unchanged.
The local records themselves are not constructed here.

`evaluatedMixedDiagonal_odd_expansion` proves the finite rational expansion.
`evaluatedMixedBend_odd_expansion` gives its central entry in chronological
order as

    sum_(r<2n) (-1)^r x^(-r-1) ; v ; u ; y^r,

where x is the SAME raw pre-E dot, v the prescribed shifted cap, and u,y
the given reservoir unit and restricted dot. The proof retains inverse
powers before the cap; the only inverse-power interchange uses the even
integer r(r+1). `evaluatedMixedBend_odd_slide` then proves

    s ; y + x ; s = v ; u

for this exact evaluated bend, by a finite telescoping identity and the
actual contentwise nilpotence. A mate slide is not an input assumption.

Both producers and their paired consumer pass strict scoped Lean checks.
The audits cover all 51 and 18 owned declarations, including private and
generated declarations, using only the standard three axioms. The paired
asymmetric two-odd-colour consumer uses `VacuumTensor.probeFunctor` on the
literal A/T reservoir with cutoffs four and six and probe exponents one
and two. A tensor-right-unitor detector proves a surviving exterior class
tensored with the original probe unit nonzero. On that SAME tensor vacuum,
the raw pre-dot is proved distinct from the unsigned coordinate dot using
the opposite top-window signs. The reservoir kernel supplies all exponents
for the actual finite expansion and signed slide. Full-package CI remains
the integration gate.

Identification of this evaluated formula with the complete chosen swapped
crossing/mate and its inverse rows remains open. In particular no normalized
bubble formula, action-faithfulness claim, or final vacuum-observation datum
is asserted by these component calculations.
