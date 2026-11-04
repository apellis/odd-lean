# Intrinsic integer grading of the represented finite inverse

This is the represented-coefficient homogeneous inverse step (G8) in
[DeformedGradedAction](DeformedGradedAction.md). It concerns the actual
finite unit/cap matrices. It does not place an integer grading on maps
between arbitrary ungraded modules.

The source modules and their integer degrees are fixed before taking an
inverse. The old category uses `oldDegree`; the represented lower loop
uses `IndResKernel.integerDegree` on the literal balanced quotient of
`Hom(Js,t) ⊗ Hom(v,Js)`. Its degree is the sum of the two Hom degrees.
`ELVKernelEntryDegrees` proves that the prescribed signed mate has degree
`-2dᵢ`, while the ordinary dotted cap rows and unscaled dotted unit
columns have degree `2dᵢr`.

Write a shift by `a` with degree `n` equal to the original degree `n+a`.
The positive matrix has source coordinates

| Coordinate | Module | Shift |
|---|---|---|
| `none` | represented lower loop | `+2dᵢ` |
| `some r` | `Hom(v,t)` | `-2dᵢr` |

Its target is the unshifted `Hom(Jv,Jt)`. The negative matrix has the
unshifted represented lower loop as source and target coordinates

| Coordinate | Module | Shift |
|---|---|---|
| `none` | `Hom(Jv,Jt)` | `-2dᵢ` |
| `some r` | `Hom(v,t)` | `+2dᵢr` |

Both literal forward matrices preserve degree zero in these shifted
coordinates. In `IntegerMatrixGrading`, finite shifted products retain
their original coordinate projections and form an internal direct sum.
A homogeneous map commutes with these projections, by induction on the
source's homogeneous summands. Injectivity then shows that the inverse
of a degree-zero linear equivalence commutes with the same projections.
This proves inverse degree preservation without defining any degree by
transport through the matrix.

`ELVKernelMatrixInteger` applies this argument to the existing actual
matrices and their proved content-height bijectivity. The raw
`positiveKernelEquiv` and `negativeKernelEquiv` are literally
`LinearEquiv.ofBijective` of those maps. Positive principal extraction
is projection at `none` after the inverse. Negative principal extraction
inserts at `none` before the inverse. Both principal inverse maps send
an upper Hom of raw degree `n` to represented kernel degree `n+2dᵢ`.
Every old source and target is retained, including off-content sectors;
height zero uses the actual empty secondary coordinate family.

The paired consumer tests the unequal symmetrizer `(2,1)`, positive,
negative and zero heights, and off-content sources. A one-strand odd
identity is independently nonzero by the truncated odd detection theorem;
its actual positive inverse is nonzero and has the prescribed shifted
degree. Both new producers are audited against the repository axiom
allowlist.

The next attachment identifies these raw principal inverse entries with
the principal entry of the chosen reservoir local record through the
existing finite kernel tensor coordinates and inverse uniqueness. The
raw inverse degree theorem alone does not assert that identification or
the positivity of the resulting reservoir closure.
