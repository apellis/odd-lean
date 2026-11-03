# Bounded half-turn coordinates in actual regular-power word values

`HalfTurn/PowerWordCoordinates.lean` composes the proved full half-turn
with the native source map of `ELVPowerWordCoordinates`. Its target is an
actual induced regular A/T word value:

`powerWordModule(parameterTwist Sc, reverse t)(reverse s)`.

`powerWordHalfTurnCoordinate_eq` exposes its two operations: the actual
old-Hom half-turn, then the original balanced coend generator h tensor 1.
The full exterior coefficient algebra is fixed by the half-turn, and the
literal elementary-power exponents are unchanged.

`powerWordHalfTurnCoordinate_ker` computes the kernel exactly as the
transformed last-boundary ideal with those source powers. This combines the
proved actual coend presentation kernel with the contextual half-turn ideal
identification; no action-faithfulness or vacuum-evaluation kernel is assumed.

The bounded detection theorem uses precisely

`d + 2 * choose(length(s), 2) < N`,

with every strand cutoff and every elementary-power weight at least N.
The scheduled versions use the original `reservoirLevel` and `vacuumCutoff`
and prove both actual-coordinate injectivity and the required high-window
kernel containment. The models and cutoffs may be chosen for an individual
source word pair and degree window.

The paired consumer proves the literal power-weight inequalities over the
asymmetric two-odd-colour datum and detects a nonempty two-strand joint PBW
vector with the product of both exterior basis generators. Its target is
explicitly typed as the reversed/twisted actual regular-power word value.
The shared consumer audits all 69 declarations owned by the two producers.
Strict pinned source and consumer checks passed, with only the repository's
allowed axioms and no increased proof budgets.

These are native source coordinates in actual word values. The remaining
chosen-action evaluation comparison must use the complete contracted
parity, including the A/T coefficient, when expressing signed right
multipliers and chronological composition.
