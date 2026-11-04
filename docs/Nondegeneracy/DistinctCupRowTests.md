# Actual finite row tests for the distinct cup words

`SKM/RouquierDistinctCupRowTests` attaches the finite-row calculation
of Brundan–Ellis Lemma 7.1 to the original cup words and the prescribed
distinct target chart. It uses the edges and local cup conventions of
`RouquierDistinctCupTests`.

The dotted right cap passes through the actual right mate by
`distinctCrossMate_dottedCap`. This is the rectangular right-adjunction
cap pitchfork with the original dot powers. Moving the upper dot power
through the mate contributes a Koszul sign; the actual iterated upward
dot-slide relation contributes the same sign. Their product is one.
No cap comparison or cyclicity hypothesis is introduced.

`distinctCupLeft_row_reduce` identifies every original left cup row,
closed by the right unitor, with the literal lower cup, upward double
crossing and lower dotted cap. In the strict range
`h_i(b)>d_ij`, `distinctCupLeft_row_of_gt` then gives

    t_ij · (if n=(h_i(d)-1).toNat then id(E_j) else 0).

The original right cup first cancels the actual inverse target chart.
`distinctCupRight_row_of_pos` evaluates its closed row directly by the
upper local inverse relation, with coefficient one. These two values
supply the finite tests for the scaled raw cup identity; principal tests
are supplied by `RouquierDistinctCupTests`.

The consumer uses the constructed rational two-odd probe family with
Cartan entries `(-2,-4)`, upper finite-row widths four and two, and
leading units one and minus one in the opposite colour orders. It
checks every dotted-cap transport, every raw row reduction and every
finite left and right row, and retains nonzero probe append vectors.
All owned declarations are audited against the standard axiom allowlist.
