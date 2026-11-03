# The prescribed dotted unit and counit rows under reindexing

For Brundan–Ellis (1.13)–(1.14), the same two append-adjunction comparisons
must preserve every row of the local inverse matrix. `ELVProbeReindexRows`
uses the standard central content `i :: ν`, its stored representative `ν₁`,
and the stored upper representative `ν₂`, with their given permutations.
The input module is arbitrary and the target module is its literal
certificate reindexing.

`oldAppendReindexIso_cap` and `oldAppendReindexIso_unit_row` retain the
original counit and unit. Their proofs reduce the already proved composite
adjunction squares through the identity unit/counit of certificate
reindexing. No new bending or normalization data are chosen.

`oldAppendReindexIso_capDotRow` and
`oldAppendReindexIso_unitDotColumn` then preserve the actual dot powers for
every exponent, including zero. The lower formula compares reindexing of
the standard cap row with the lower append comparison followed by the
stored-target cap row. The upper formula compares reindexing of the
standard unit column followed by the restricted upper append comparison
with the stored-target unit column. The previously checked dot square
and elementary functorial power identities prove these whole module-map
equations. No row-comparison, inverse or matrix relation is assumed.

The exact producer and paired consumer pass strict checks. All 36 owned
declarations pass the standard axiom allowlist. The consumer applies both
base and all-exponent statements to reordered mixed contents, both colour
parities, and a parity-shifted regular evaluated probe module.

Together with the chosen mate comparison, these are the generator squares
needed to attach the transported inverse entries to the prescribed local
fields. Evaluated/natural field transport, the canonical local constructor,
absent-lower-predecessor sectors and whole-weight assembly remain separate.
