# The selected principal entry of the weight local matrices

The Brundan–Ellis (1.13)–(1.14) local inversion fields use the Rouquier
mate of the prescribed equal-colour weight crossing.
`rouquierMate_piscat_app` expands that map with its existing upper cup
and lower cap, and `rouquierMate_piscat_eq_rectangular` proves equality
of the whole two mate conventions in the actual PiSCat target.
No homogeneity restriction is placed on the middle crossing.

`elvWeightRouquierMate_eq` identifies this selected local principal
field with the rectangular weight mate already used by the content
coordinate transport. `elvWeightRouquierMate_mem` gives its required
parity p_i, and `elvWeightRouquierMate_app_block` retains the literal
upper unit, given signed crossing and induced lower counit at every
output block. Both adjacent weight steps retain their own adjunction.

Both producers and paired concrete consumers pass scoped strict checks,
with all 14 owned declarations audited. The tests use the actual
nontrivial equal-colour weight crossing for both moving parities,
parity-shifted representable inputs and empty truncation.
Full CI remains the integration gate. This identifies the chosen
principal field; the finite parity matrices and their local inverse
entries remain to be assembled.
