# Joining independent odd-colour actions

This note describes the parity convention behind
`disconnected_tensor_action.py` and its all-cutoff extension. Work with two
rank-one actions in a strict parity-complete envelope, normalized so the
disconnected crossing polynomial is Q_ij=1. Arbitrary native parameter
rescalings and the formal Lean action interface are separate comparisons.
The interacting Cartan case is not covered.

## Functors and transformations

Write the two height coordinates as (h_i,h_j); E raises its height by one
and F lowers it by one. On the external supertensor product of the two
categories, set

\[
 E_i=E\boxtimes1,\quad F_i=F\boxtimes1,\qquad
 E_j=\Pi^{h_i}(1\boxtimes E),\quad
 F_j=\Pi^{h_i}(1\boxtimes F).
\]

Use the parity-envelope convention that Pi acts on a homogeneous map f by
(-1)^|f| f. A product object has an additional parity shift s. Thus applying
either j functor to a map of its **declared** parity p contributes the
factor (-1)^(h_i p), including maps whose oddness comes from opposite
source and target parity shifts.

The units and counits are the external lifts of the given even adjunction
maps. The dot component is (-1)^s times the ordinary lifted i dot, and
(-1)^(s+h_i) times the ordinary lifted j dot. The same-colour crossing
component is (-1)^s times its ordinary lift for **either** colour; adding
an extra h_i factor to the j crossing would be wrong. Mixed crossings are
the canonical underlying identity between functor composites differing by
one parity shift. They are odd maps, even though their unshifted matrix is
an identity.

This uses independent coefficient algebras and genuine rank-one bubbles
from each factor. It does not adjoin exterior spectators and declare them
to be bubbles.

## Closed signs and upward coherence

For an upward word w, put

\[
 S(w)=s+h_i\#\{j\text{ in }w\}
       +\#\{(a,b):a<b,\ w_a=j,\ w_b=i\}\pmod2.
\]

After identifying the underlying word functor with the colour-grouped
external product, its parity shift is S(w). Every dot, and every adjacent
same-colour crossing, is (-1)^S(w) times its canonical grouped operator.
For an adjacent mixed crossing at positions r,r+1 (zero based), its
underlying scalar is (-1)^A_r(w), where

\[
 A_r(w)=\sum_{a<r,\ w_a=j}
       \bigl(h_i+\#\{b>a:w_b=i\}\bigr)\pmod2.
\]

These formulas follow by summing the signs contributed by the outer
whiskering functors. They give a direct check of all upward relations:

- A mixed swap changes S by one, so its dot slides have the required
  minus sign, including distant dots. Swapping back leaves A_r unchanged,
  giving the quadratic identity Q_ij=1.
- Two disjoint mixed swaps change the later prefix sign by one. This gives
  far anticommutation. For a mixed and a same-colour crossing, the change
  of S gives the same sign. Two same-colour operators use the original
  odd nilHecke relation or supertensor interchange.
- For each of iij, iji, jii, ijj, jij, jji, the two braid paths have the same
  scalar and the same single canonical same-colour operator. The all-equal
  braid is inherited from its rank-one factor.

The script derives these operators by functor whiskering; it does not
attach the grouped-word sign formula independently to another action.

## Adjunction and inversion

For each colour, the extra parity shifts in FE and EF cancel. Units and
counits are even, so their triangle identities are the tensor lifts of the
rank-one triangles.

The same-colour EF mate simplifies to (-1)^s times the ordinary external
lift of the rank-one mate. For colour j, the raw crossing at the F_j-shifted
object supplies (-1)^(s+h_i), and the outer F_j acting on that odd map
supplies (-1)^h_i; the h_i factors cancel. The same calculation applies
to the dotted identity summands in the nonzero-weight inversion block.
Consequently the given rank-one inversion isomorphisms remain isomorphisms.

The mixed EF mates are invertible as well. The two factors act on separate
categories, so their mate composites contract to the relevant adjunction
triangle. With the script's order convention, the mate E_j F_i -> F_i E_j
has underlying scalar +1; E_i F_j -> F_j E_i has scalar (-1)^(h_i+1).
Their source and target have opposite parity shifts. Thus the isomorphisms
are actual mates of the same upward crossings, not separately chosen
mixed inverses.

These reductions give the all-cutoff construction from genuine rank-one
actions, under the specified strict parity-envelope conventions. Turning
it into a native theorem still requires the categorical product/envelope
and action interfaces; finite matrix checks alone are not that theorem.

## Checked finite instance

The script uses the two independent cutoff-two towers of dimensions
2,4,8, retaining a nonzero exterior coefficient in each. It now checks:

- all 32 admissible upward words of lengths two through four across all
  nine tower weights, including braids and distant anticommutation;
- every legal adjunction triangle and every same-colour inversion block,
  including the two boundary weights;
- every nonzero mixed EF inversion corner in that grid;
- actual middle-weight bubbles of rank eight on the sixteen-dimensional
  product object, with product rank four, zero squares and zero
  anticommutator;
- supernaturality of all four middle-weight mate maps for all sixteen
  homogeneous regular-module basis endomorphisms.

At the middle object the bubbles are precisely
-L_delta tensor 1 and -P_i tensor L_delta, where P_i is the first-factor
parity operator. Hence their product is nonzero and comes from the
reconstructed cup/inverse-mate/cap composites. The higher-cutoff extension
uses the published rank-one actions, not a claim that this one finite
instance detects arbitrary coefficient degrees.

## Fixed-weight consequence within the disconnected scope

Combine this construction with `RankOneFixedWeightSeparation.md`, choosing
large cutoffs independently in the two factors. Mixed crossings are
invertible, so a boundary word can be put into colour-grouped order by a
fixed invertible crossing composite. Upward operators between grouped
words reduce to the external supertensor product of the two monochromatic
operator spaces, with the corresponding parity shifts. Their vacuum
coefficient algebras are independent factors as well.

Over the stated field, the tensor product of the two bounded coefficient
coordinate injections remains injective. Hence the source-level fixed
weight separation argument extends to this normalized two-colour
**disconnected** setting. The parity shifts change only invertible signs;
they do not identify the two exterior generators or kill their product.
This is conditional on the published rank-one inputs and the categorical
envelope comparison just described, not a newly compiled native
multicolour independence theorem. A nonconstant connected crossing
polynomial requires additional action and inversion arguments.
