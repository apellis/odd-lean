# Given signed dot powers on the selected cap source comparison

DeformedMatrixComparison (1), (2), (5) compares dotted unit and cap rows by
powers of their original signed induction dot. The chosen cap source
comparison contains the lower scalar append isomorphism followed by
induction of the literal restriction equality. Transport of the one-letter
append dot alone does not include that second map.

`probeMappedAppendLinear_dot` proves the dot square for the checked mapped
append comparison, with an independent scalar-evaluated old source module
and an even ordinary module isomorphism. Its generator formula maps the
old coefficient arrow without changing its order, retains its full parity
twist, and leaves the inner module comparison on the same vector. Evenness
is an intermediate premise; the canonical restriction equality discharges
it in the actual cap source.

`probeMappedAppendLinear_dot_pow` transports every nonnegative power of that
same signed dot. No polynomial change of generators or scalar normalization
is introduced. The odd pair-of-dots sign is already contained in the given
operator's iterates.

The consumer uses the canonical restricted mixed scalar probe
regular module, proves its coefficient-evaluation class and the evenness of
the literal restriction identity, and instantiates both moving parities and
vacuum at arbitrary powers. The producer and consumer pass the strict pinned checks, including the
owned-declaration axiom audit.

The named next use is comparison of the actual dotted cap rows, followed by
their canonical shifted target coordinates. The source (5) output parity
involution and odd cap scalar remain explicit through
`OperatorPowerComparison`; the even case has identity correction. This note
does not identify normalized cap rows with the unshifted counit alone or
assert the assembled inverse matrix comparison.

## Proposed attachment of the cap rows

For an old module `N` at content `i :: ν`, write `R = Res_J N`, let `O`
be its ordinary scalar descent, and let `C_t` be the selected lower source
comparison (lower append followed by induction of the literal restriction
equality). Put `D₀` for the given old dot on `Ind_J R` and `D₁` for the
ordinary dot on `Ind_T Res_T O`. The checked power theorem gives
`C_t D₀^n = D₁^n C_t` with the canonical even restriction isomorphism.

The next source obligation is to identify `v_t ε_T C_t = ε_J`, where `v_t`
is the identity-on-vectors value isomorphism and the two counits are the
chosen ordinary adjunction counits. `ProbeCounitComparison` already proves
this equality for its four-leg presentation. It remains to attach that
presentation to the mapped-append source map without reintroducing late
coend instance conversions. Composition then gives
`v_t ε_T D₁^n C_t = ε_J D₀^n` for every actual dotted cap row. The unit
columns use the already checked chosen unit formula and the same powers.

The canonical shifted target/source coordinates must then be attached to
these row identities. The old kernel normalization in
`ELVShiftedCapRows.shiftedCapRow_normalization` and
`ELVKernelMatrixEvaluation` already keeps the source (5) scalar and whole
output parity, including its twisted actions, when identifying the old
normalized kernel row with the actual module cap. Its old representable is
not itself scalar-evaluated; applying scalar-module descent directly to that
representable would require a false coefficient-evaluation premise. The
route is through the proved actual module cap row and its chosen content
chart, preserving that kernel normalization. No naked output parity map is
tensored as though it were an ordinary bimodule map.
