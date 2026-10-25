# Odd dot translation and the height-parity boundary

Research calculation supporting BE2 Section 8. This gives a partial mechanism
for adding exterior bubble coefficients; it does not construct a full
translated multicolour action or prove a separating family exists.

## Local algebra and inverse coordinates

Let `d` be an odd, square-zero coefficient, supercentral relative to the
action. For an odd dot `x`,

\[
(x+d)^{2m}=x^{2m},\qquad
(x+d)^{2m+1}=x^{2m+1}+x^{2m}d.
\]

The ring module `OddMath/Diagrams/OddNilHecke/DotTranslation.lean` proves
these formulas and preservation of the odd nilHecke dot-slide when both
dots are translated by the same coefficient. The independent exterior
coefficient anticommutes with the odd crossing as required.

At positive height `h`, let the source inversion matrix have cap rows
`v_r=v x^r`, `0≤r<h`. After translation, the rows become

\[
v'_r=\begin{cases}v_r,&r\text{ even},\\
v_r+v_{r-1}d,&r\text{ odd}.
\end{cases}
\]

The coefficient has been moved past the even cap `v_(r−1)` in the second
case, so no super sign is omitted. This row operation is invertible by
replacing `d` with `−d`; it is lower unitriangular. Moreover, it fixes the
coordinates of the last inverse column `e`, since every correction contains
`v_(r−1)e=0`. The crossing coordinate does not change.

`OddMath/SKM/OddDotTranslation.lean` proves the inverse row operation and
last-column calculation in a preadditive category. The native theorem
`etaP_shifted_cap_coordinates` supplies these coordinates for the actual
source's normalized left cup using BE2 (2.13). Consequently, wherever the
translated full inversion has been constructed, uniqueness of its inverse
identifies its normalized left cup with this unchanged column. The file
does not construct the translated full presentation or that action.

## Which bubble can change

At odd positive height `h=2m+1`, the normalized left cup is even. Its
naturality therefore moves `d` through it without a sign, and the
degree-zero bubble has value one. The preceding power formula gives

\[
\beta'(\delta)=\beta(\delta)+d.
\]

The generic theorem `odd_moment_shift` proves this implication, with the
required naturality and bottom-bubble identity explicit. In the same
component, the polynomial generator `e_r` uses `2r+h−1` dots, an even
number. Its value is unchanged by `even_moment_fixed`.

Thus, **conditional on a reduced action separating the polynomial
coefficients and on the translated full action**, this construction can add
an independent exterior coefficient in an odd-height component. For several
odd colours one would retain separate `d_i` and verify the mixed relations;
one shared exterior variable cannot detect their products.

At positive even height the odd bubble has an even number of dots. The last
inverse column is still unchanged, and the power formula leaves the bubble
unchanged. At height zero the source mate and adjunctions themselves remain
unchanged, so `Vσ⁻¹U` is unchanged. Therefore translation of a reduced action
does not create a nonzero odd bubble in these components. The dual
negative-height cup-column argument has the same predicted parity boundary,
but is not yet formalized here.

For an odd root, every Cartan entry in its row is even. Hence its coroot
height parity is constant under adding simple roots. Moving elsewhere in
the same root-lattice component cannot convert the even-height problem
into the odd-height case. The actual even-degree reservoir deformation in
`CoupledBubbleEvaluation.md` addresses a different, necessary case.

## Verified boundary

The supporting source identities and ring/category lemmas are checked in
Lean, with the concrete consumers and axiom audit in
`scripts/NonVacuity/OddDotTranslation.lean`. These include a nonzero
exterior matrix model and the actual source inverse coordinates at height
three. Preservation of every mixed-colour braid and categorical relation,
the full translated 2-functor, and polynomial coefficient separation remain
construction obligations. The square calculation alone does not prove them.
