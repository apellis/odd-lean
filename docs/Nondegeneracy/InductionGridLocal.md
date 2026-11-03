# Local records from the prescribed old-content matrices

Brundan–Ellis (1.7)–(1.8), (1.13)–(1.14) uses the ordinary induction
adjunction, its specified dot, the negative physical equal crossing,
and the inverse entries of the prescribed finite unit or cap matrix.

`inductionModuleLoc` assembles these exact fields. Its matrix
isomorphisms are intermediate inputs. `oldContentLoc` supplies
the constructed prescribed old matrix inverses on every input module,
and the literal old quotient slides, removing those inputs. Its local
height is minus the intermediate content height. `oldContentLoc_cross_square`
is a separate square-zero equation on the same chosen two-morphism.

`inductionModuleCross_slide_left` and `inductionModuleCross_slide_right`
lift the module slides to the whole induction functor. Total components
first detect the outer natural transformation, then the underlying module
map. The inner and outer dot comparisons retain the chosen flattening,
and the crossing remains its prescribed negative.

All three producers and their concrete consumers pass strict scoped
checks with owned-declaration axiom audits. The mixed-parity consumer
checks both strict height directions, the zero-height overlap, and
finite inverse-entry products. Full integration verification remains
separate. No complete family or normalized left-adjunction conclusion
is asserted here.

The next restriction carries this local record to the full scalar-evaluated
probe subcategory, using the same unit, counit, dot and crossing. Its
inverse entries remain module maps because this is a full subcategory.
The existing adjacent left-adjunction theorem can then use this record
and the constructed empty local record. Its prescribed normalized
counit retains the fixed scalar relative to the raw top inverse row;
the canonical pre-Hom comparison supplies the second scalar. None of
these fields is rescaled.

The source head `2652d0a76a9ee31ee3c669eb1ad35736b837fee4` passed the
full build, global axiom audit and all concrete consumers in
[#1014](https://github.com/apellis/odd-lean/pull/1014)
([CI run](https://github.com/apellis/odd-lean/actions/runs/41691819623)),
merged at `2c1306c4`.
