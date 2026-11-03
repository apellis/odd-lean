# The equal-colour mate under content reindexing

This note describes the single-coend comparison required to attach the
transported inverse coordinates to the selected stored-target fields in
Brundan–Ellis (1.13)–(1.14).

Let the standard append functors be `J₀ : ν → i :: ν` and
`K₀ : i :: ν → i :: i :: ν`. Let `h₁ : (i :: ν).Perm ν₁` and
`h₂ : (i :: ν₁).Perm ν₂` prescribe the target append functors
`J : ν → ν₁` and `K : ν₁ → ν₂`. Write `R₁` for the module reindexing
associated with `h₁`. The lower loop comparison is the lower append
comparison; the upper comparison is the upper append comparison followed
by restriction along `K`.

For an arbitrary standard intermediate module `N`, the mate
square compares the standard mate at `N` with the target mate at `R₁ N`.
This orientation keeps the target module of the upper append comparison
literal and avoids simplifying a reindexing round trip inside a coend.

On a generator `[g ⊗ b]` of the lower loop, the ordered grid mate has value
`[-γ(s) twist(K₀(g)) ⊗ b]`. The lower and upper append comparisons keep the
coefficient arrow and module vector and change only the source object's
permutation certificate. Consequently both sides of the square have the
same negative crossed coefficient, with the twist of the complete arrow
retained. Equality follows by the coend's linear-map extensionality.

`ELVProbeReindexMate.oldReindexLoopLinear_mate` proves this square as an
equality of complete coend linear maps. The lower and upper comparison
tensor formulas are `oldReindexLowerLoopLinear_tensor` and
`oldReindexUpperLoopLinear_tensor`. The physical crossing wrapper is
`oldAppendToEqualCross`, with its supernatural degree supplied without a
comparison assumption.

The paired consumer applies the square to both colour parities on a
mixed-content scalar-evaluated regular probe and its parity shift, at a
concrete stored-content word. Identification of dotted unit and counit rows
is a further input to the stored-target local record; a mate square alone
does not finish that record.
