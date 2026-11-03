# Integer degrees of the represented finite matrix entries

`ELVKernelEntryDegrees` proves the integer degrees of the prescribed
forward matrix entries on the intrinsic grading of
`ELVIndResKernelInteger`. The source grading is the sum of the two Hom
factor degrees of the actual balanced quotient.

For an intrinsic input of degree `n`, the actual signed mate has degree
`n - 2*sy.d i`, the induction dot has degree `n + 2*sy.d i`, its `m`th
power has degree `n + 2*sy.d i*m`, and the ordinary counit has degree
`n`. Consequently the actual ordinary dot/cap row has degree
`n + 2*sy.d i*m`. The actual unscaled unit/dot column sends an old Hom
of degree `n` into the upper Hom of degree `n + 2*sy.d i*m`.

The declarations are `actualMateKernelComponent_degree`,
`actualDotKernelComponent_degree`,
`actualDotKernelComponent_power_degree`,
`actualCounitKernelComponent_degree`,
`actualCapKernelComponent_degree`, and
`actualUnitKernelComponent_degree`.
Their operators are the existing literal kernel maps, including the
negative mate, total-parity twists, and prescribed unit-column scalar
signs. No inverse or integer-homogeneity premise is used. The only
global degree inputs are the actual symmetrizer and homogeneous
parameters.

These statements supply the entry input to the shifted finite forward
matrix. With `GradedSuperspace.shift a` defined by degree `n` equal to
old degree `n+a`, its positive source shifts are `2*dᵢ` on the
represented lower loop and `-2*dᵢ*m` on the identity rows; the upper Hom
target is unshifted. The negative source is unshifted, and its target
shifts are `-2*dᵢ` on the upper Hom and `2*dᵢ*m` on the identity rows.
Establishing the shifted matrix inverse and comparing its principal
entry to the chosen whole-weight local record are subsequent steps.
No grading of all morphisms between ungraded modules is asserted.

The paired consumer uses the actual asymmetric two-odd rational data
with symmetrizer `(2,1)`, both append colours and a mixed word. It checks
each operator on the intrinsic degree-zero identity tensor, retains
all natural dot exponents, and verifies that the actual counit on that
tensor is the source identity. The two colours have integer dot degrees
`4,2` and mate degrees `-4,-2`, despite having the same super parity.
