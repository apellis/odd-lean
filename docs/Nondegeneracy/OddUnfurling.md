# Odd unfurling: a Grassmannian–spectral synthesis

Research note, 2026-10-25. This records a proposed construction and its explicit
obligations, not a proof of general odd nondegeneracy. No new Lean theorem is
claimed here. Repository baseline: `5b698faee17e176c871cd07ee272b89585148617`;
Categorification pin: `777be9ef0d1f66354e185afbde208119f5255bb3`.

Subsequent concrete progress is recorded in
[CoupledBubbleEvaluation.md](CoupledBubbleEvaluation.md): a native Lean
formula identifies the height-zero odd bubble with an inverse-mate
coefficient, and the actual finite exterior coupling evaluates it nontrivially.
That calculation tests the first coupling coefficient, not the full proposal.

## What really worked in the even repository

The user's recollection is correct. `OddMath/SKM/EvenBridge/EvenNondegeneracy.lean`
uses `Categorification.KL3.Diagram.calculusNondeg`; the dependency's
`Categorification/Diagrams/KL3/Nondegeneracy.lean` supplies this through
`KLR.Unfurling.GenericFields.calculusNondeg_charZero` followed by integral
descent. `KLR/Unfurling/GenericNondeg.lean` supplies its evaluation and categorical
bubble scalar law, rather than leaving them as theorem hypotheses.

The reusable proof boundary is `KLR/Unfurling/Nondeg.lean`'s `UnfurledEval`:
evaluate a bounded finite relation, separate upward crossing/dot terms by a
triangular action, and then separate bubble coefficients. Its ordinary field
valued bubble map must change in the odd setting. An ordinary field with trivial
odd part kills every odd bubble parameter.

This source distinction matters: the existing even theorem assumes even datum,
compatible symmetrizable Cartan data and finite colours. Copying its construction
does not establish the broader BE2 Section 8 parameter/datum scope.

## Primary sources and their precise contributions

Brundan–Kleshchev, [arXiv:2203.14149v3](https://arxiv.org/pdf/2203.14149v3),
Theorem 13.2 constructs the odd rank-one Grassmannian bimodule action.
Corollary 13.4 computes its bubble evaluation, after evaluating a bimodule
endomorphism at 1 and applying the specified quotient map: it is the canonical
map from the universal bubble algebra to its finite quotient. Theorem 13.5
uses arbitrarily large quotients to separate a finite relation among decorated
matchings. This supplies a rank-one coefficient detector, not a general-rank
action or arbitrary mixed-colour compatibility.

Webster, [arXiv:1603.06311v4](https://arxiv.org/pdf/1603.06311v4),
Theorem 3.13 proves ordinary diagrammatic nondegeneracy. Section 6 separates a
finite relation using generic spectral representations. Lemma 6.2 and
Proposition 6.5 relate original and unfurled completed upward algebras; extending
this to a categorical action requires adjunction and inversion as well as upward
relations. The v4 paper also presents a less technically demanding proof in
Section 3; the repository cites v3, so theorem numbers should not be silently
identified across versions.

Kang–Kashiwara–Tsuchioka,
[arXiv:1107.1039v2](https://arxiv.org/pdf/1107.1039v2), Theorem 3.13 gives a
Clifford enlargement relating quiver Hecke superalgebras and suitable
quiver Hecke–Clifford corners. Their signed label involution and completed
algebras provide a candidate algebraic language. This is not already a
categorical odd unfurling theorem: the theorem does not supply the necessary
cups, caps, bubble law or mixed inversion for our proposed action.

## A local calculation constraining any construction

An odd dot cannot be translated by a nonzero even scalar while preserving
parity. Instead use the even coordinates

\[
z_r=x_r^{1+p(i_r)}.
\]

For odd colour this is the squared dot. These coordinates commute in the
skew-dot algebra; they need not be central in the full crossing algebra.
Complete the dot algebra in finitely many simultaneous spectral blocks and
track the transport of blocks by crossings.

On an odd block `x²=a+t`, with `a` a nonzero even scalar and `t` topologically
nilpotent, work first in characteristic zero and adjoin a square root of `a`.
The formal series `s=sqrt(a+t)` is even and invertible. Then

\[
c=s^{-1}x,\qquad c^2=1,\qquad |c|=1.
\]

Thus a nonzero block is Clifford-enhanced. It is not obtained by replacing an
odd dot by an ordinary nilpotent dot. The zero block remains qualitatively
different. This is a local statement about the dot algebra; extension across
crossings remains to be constructed.

There is a second, concrete restriction already proved in Lean.
`OddMath/Diagrams/OddNilHecke/Intertwiner.lean` defines

\[
\Delta=y^2-x^2,\quad g=\Delta(y-x)-\Delta^2\tau
\]

and proves

\[
g^2=-\Delta^2(x^2+y^2),\quad gx=-yg,\quad gy=-xg.
\]

For squared spectra `(a,b)`, this operator is invertible whenever both
`b-a` and `a+b` are units in the completed coefficient ring. Indeed its
square then is a unit, which implies that the operator itself is a unit.
A construction using this `g` as invertible transport should choose labels
avoiding opposite squared spectra as well as coincident ones. Algebraically
independent labels satisfy these finite open conditions, so this restriction
does not by itself obstruct the generic strategy. On a block with `a+b=0`,
this particular operator cannot be made invertible
merely by multiplying it by a unit. Its norm alone does **not** prove that no
other useful crossing or equivalence exists there. Such blocks must either
remain interacting vertices of the enlarged diagram or receive a separate
construction.

## Proposed construction: retain nilpotent reservoirs

The useful synthesis is asymmetric. Retain a zero/nilpotent Grassmannian sector
for each odd colour to detect its odd bubble generator. Add generic nonzero
squared-dot sectors to distinguish strand operators. Do not try to detect
all bubbles by evaluating only at ordinary nonzero spectral points.

This refines the branch's existing two-factor design, with a nilpotent factor
and an invertible-dot factor. It does not supply a new coupling of those
factors. Its contribution is to identify the Clifford structure of the
spectral factor and sharpen the coefficient-detection obligation on the
nilpotent reservoir.

This prescription is also motivated by a sharper obstruction found in the
parallel action stream: some deformed odd cyclotomic presentations impose
`d χ_(n/2)=0` in even cyclotomic degree. Inverting that last coefficient kills
the odd deformation parameter `d`. See `ExteriorActionProgress.md` for the exact
source conventions and calculation. This is an obstruction to that proposed
deformation, not a claim that an invertible odd operator universally kills an
independent odd parameter. A Clifford algebra supertensored with an exterior
algebra is an immediate counterexample to the latter claim.

The first target should therefore be finite, with characteristic-zero even
generic scalars and an honest exterior coefficient algebra:

\[
S=k(\mathbf a)\otimes_k\Lambda(\epsilon_i\mid i\in I_{\mathrm{odd}}).
\]

Only colours and bubble indices in the proposed finite relation are needed.
The exterior generators must remain distinct; replacing all of them by one
odd parameter destroys products such as `δ_i δ_j`.

The proposed stages are:

1. Construct completed upward algebras using squared spectra at odd colours,
   ordinary spectra at even colours, and Clifford factors on nonzero odd
   blocks. Check all crossing relations, including three-strand braids.
2. Prove a bounded triangular basis-image statement with unit diagonal over
   `S`; do not infer it merely from a polynomial representation for the
   undeformed upward algebra.
3. Couple these blocks to the Grassmannian reservoir actions. Supply actual
   adjunction maps, parity shifts, mates and same-colour inversion matrices.
   Tensor products of rank-one actions alone do not define mixed-colour
   crossings.
4. Compute the vacuum bubble action. Prove injectivity on the finite set of
   bubble monomials used, including every exterior product. BK's quotient
   calculation supplies the model for this proof at each rank-one reservoir;
   preservation under the coupling is an additional theorem.
5. Apply bounded separation, then the independent upward-to-oriented reduction.

Steps 1–4 are outstanding, not disguised assumptions already discharged by BK
or KKT. In particular, a Morita superequivalence of upward algebras need not
transport the chosen traces or normalized cups and caps automatically.

The next concrete coupling lemma should compute the normalized bubble map
from the actual coupled caps and cups, with a formula of the form

\[
\beta_{\mathrm{coupled}}(\delta_i)
 =u_i\delta^{\mathrm{res}}_i,
\qquad
\beta_{\mathrm{coupled}}(e_{i,r})
 =v_{i,r}e^{\mathrm{res}}_{i,r}
   +\text{terms lower in a specified triangular order},
\]

where `u_i` and `v_(i,r)` are even units in a fixed probe/base coefficient
algebra, independent of the reservoir variables being substituted, and the
lower terms involve only earlier reservoir variables in the specified order
and have a controlled coefficient/dot weight. More general diagonal
coefficients would require an explicitly proved invertible substitution;
being arbitrary even units alone is insufficient. These are proposed
formulas to prove, not assumptions
justified by taking a product of the two existing actions. One must specify
the order, verify multiplicativity and super signs, and check that the
reservoir exterior monomials remain independent. The weighted finite-quotient
bounds in `UpwardSeparation.md` would then preserve the required finite
coefficient span. Combined with the same action's triangular operator-image
formula, this would establish joint coefficient/operator detection; separate
detection in two unrelated factors is insufficient.

## The exact finite separation lemma to consume

Here is the elementary proof architecture, independent of speculative action
existence. Let `P` be the abstract bubble algebra and consider a finite relation

\[
\sum_{b\in B_0}D_b\,p_b=0
\]

among upward crossing/dot diagrams `D_b`, with `p_b` in a specified finite
dimensional subspace `V ⊂ P`. Suppose an actual action supplies:

* a coefficient map `φ:P→S` injective on `V`;
* an `S`-free target with linearly independent operator coordinates indexed by
  the necessary finite set of `b`;
* a triangular image formula whose diagonal coefficients are units and whose
  coefficient action is right multiplication by `φ(p_b)` with the prescribed
  super signs.

Order the finite support compatibly with triangularity. The extremal
coordinate gives a unit times `φ(p_b)=0`, hence `p_b=0`. Repeat after removing
that term. This proves independence of the given finite family. No domain
assumption on `S` is needed: exterior zero divisors are harmless when the
diagonal entries are units. The essential requirement is a free coefficient
module, not an ordinary scalar-valued character.

This is the right replacement for the even `UnfurledEval` consumer. It isolates
the hard mathematical task: producing the action and its basis-image formula,
not re-proving this short elimination argument.

## Go/no-go experiment and scope

Before implementing a global unfurled root datum, build the two-colour test
over `Λ(ε_i,ε_j)`: retain one nilpotent reservoir for each odd colour, add
generic Clifford probes, verify the `iji` braid and one mixed inversion,
and compute the image of `δ_i δ_j`. Success requires a nonzero coefficient
of `ε_i ε_j`; checking only the individual `δ_i` is insufficient. The
experiment must also specify how its generic probe blocks interact with the
reservoirs; otherwise it is only a list of compatible-looking factors.

This path deserves an independent stream, but not an exclusive commitment.
It attacks exactly the categorical coefficient-separation gap left by upward
PBW. Stop expanding its formal infrastructure if the first two-colour
coupling fails. Even a successful symmetrizable homogeneous pilot does not
settle all BE2 Section 8 data: nonsymmetrizable input, arbitrary permitted
parameters, source supercommutative base rings, characteristic restrictions,
and integral descent remain separate scope obligations.
