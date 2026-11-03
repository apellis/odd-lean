# Proposed whole principal content matrix square

The accompanying Lean source and consumer are history-only, unchecked
checkpoints for Brundan–Ellis (1.13)–(1.14). Neither is imported or
exported by the checked library. The intended producer module is
`OddMath.QuiverHecke.CyclotomicAction.ELVContentPrincipalSquare`.

The source retypes the chosen crossing into the literal upper content
before introducing the module variable. The crossing-family equality and
the native mate factory's equality to the given principal map check.
The proof rewrites the given map before evaluating module components.
This aligns the upper content's preadditive and linear instances.

The restriction-square evaluator retains explicit canonical source and
target objects in its equality transport. Its comparison with the raw
target map now joins successfully. The remaining failure is the next
join, `hCL.trans hRaw`, between that evaluated target chart and the raw
mate equality. This still exceeds the default recursion limit. No budget
was raised, no map or sign was replaced, and no compatibility or inverse
hypothesis was introduced. The consumer remains unverified.

The cap module square has been extracted and separately checked in
`ELVContentCapRowSquare`; this checkpoint does not contain that result.
The principal square and the supported canonical local inverse transport
remain open. The constructed global local inverses can be transported
through the chosen even charts once the principal field is attached.
