# The sideways crossing on original weight products

For Brundan–Ellis (1.11)–(1.12),
`SKM.crossMate_piscat_eq_rectangular` identifies the presentation's ordered
cup–crossing–cap with the rectangular mate in the actual PiSCat target.
The four weight corners are independent; the unit and counit are those of
the two supplied even right adjunctions. No rescaling is introduced.

`elvActionCrossMate_eq` applies this equality to the prescribed ELV weight
crossing. The reversed colour indices and edge order match the already
constructed rectangular inverse exactly. Thus `elvActionCrossMate_isIso`
supplies the precise distinct-colour inversion field required by
`RouquierMulticolour`, without an inverse or compatibility premise.

The producer and concrete consumer pass strict checks. The consumer uses
connected mixed colours, both orders of distinct odd colours, zero cutoff,
actual shifted representable inputs, both whole inverse products and inverse
naturality against the odd parity isomorphism. All five owned declarations
use only the three standard Lean axioms. The full presentation action and
its faithfulness remain separate constructions.
