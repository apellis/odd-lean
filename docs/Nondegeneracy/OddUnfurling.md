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

`OddMath/SKM/EvenBridge/EvenNondegeneracy.lean`
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

## The isomeric categorical bridge: useful but reduced

Brundan–Savage,
[Isomeric Heisenberg and Kac–Moody categorification I](https://pages.uoregon.edu/brundan/papers/isomericI.pdf),
provides relevant categorical Clifford architecture. Section 5.1 assumes
symmetrizable homogeneous data. Section 5.2 defines the isomeric category
`V(g)` with **odd bubbles equal to zero**, relation (5.13); Remark 5.1 names
the variant omitting this relation the non-reduced category. Condition
(IKM4) uses generators with purely even supercenters. Thus Theorem 6.11's
reduced action does not supply our full exterior coefficient detector.

The reusable ingredients are the prescribed adjunction (IKM1), upward
Clifford relations (IKM2), and explicit inversion matrices (5.12)/(IKM3).
For odd vertices these matrices have both plain and Clifford-token identity
components; the inverse-crossing normalization uses `−γ_i²` and adjunction
components use `γ_i`, with `γ_i²=2`. A translation to SKM must track these
factors rather than identify the matrices literally.

Remark 6.12 expressly leaves evaluated left cups/caps and dotted bubble
formulas uncomputed. Theorem 6.11 also treats its specified spectral Cartan
types and parameters, not all Section 5 data. The next useful extension for
our purpose is therefore a **non-reduced** categorical comparison retaining
odd coefficients, followed by its normalized bubble calculation. The paper
is not a theorem of general odd nondegeneracy.

## All-content cyclotomic projectivity audit

The next prerequisite is an odd-coefficient extension of KKO
[arXiv:1206.5933v2](https://arxiv.org/abs/1206.5933), Section 8, rather than
another spectral ansatz. ELV Theorem 4.5 supplies its rank-one version.
Here all odd cutoffs are **even integers** and independent exterior
parameters satisfy the ELV top-coefficient relations. This paragraph
records a conditional proof route, not a completed multicolour action.

Write the polynomial for an odd colour as
`f_i(t) = C_i(t²) - t d_i q_i(t²)`, with `d_i²=0` and
`d_i χ_(i,m)=0`. The latter relation is needed for its normality law;
the identity
`(C_i(t²)+t d_i q_i(t²)) f_i(t) = C_i(t²)²`
needs only square-zero, skew commutation of `t,d_i`, and commuting even
coefficients. It is checked abstractly in `CyclotomicNorm.lean`.
The separate odd-cutoff factorization is not covered by this argument.

In KKO's split algebra `B[t; parity]`, `t d_i` commutes with every
homogeneous element of `B`: the two Koszul signs cancel, including for
other independent parameters `d_j`. Thus `f_i` commutes with `B` while
remaining generally noncentral with respect to `t`. The source of `P`
must carry the ELV translated polynomial action; changing the old
`B`-action is not justified by this observation.

KKO (8.14)--(8.17) suggest that the same intertwiner calculation gives
`QP = f_i(t) G_i(t²)`. Transport of the odd coefficient and its odd dot
has matching signs, so their product acquires no extra sign. This must
still be proved as an equality in the actual quotient bimodule for all
contents. The symmetric dot-square product `G_i` is the other norm
factor, with invertible leading coefficient. The companion `PQ` identity
is also required; it cannot be inferred merely from a small matrix test.

Conditional on these two identities and the PBW descriptions of `K₀,K₁`,
there is a useful projectivity route. After tensoring with **any** left
`B`-supermodule, wordwise PBW coordinates make the leading part of `QP`
an invertible coefficient times a shift of polynomial degree. Hence it
is injective, and so is `P` after that base change. Since `K₀,K₁` are
projective over `B`, the resulting Tor calculation makes `coker P` flat
over `B`. This is an arbitrary-module argument, not a fibrewise criterion.
One must use the even, `B`-linear norm operator in this argument: the odd
operator `t` alone does not descend as an ordinary `B`-linear operator.

The companion norm identity annihilates the cokernel by `f_i G_i`.
Multiplication by the conjugate factor therefore supplies the **central
monic** annihilator `C_i(t²)² G_i(t²)²` (after unit normalization).
Its polynomial quotient is finite free over `B`; a finite presentation
over the split polynomial algebra consequently yields a finite
presentation over `B`. Flat plus finitely presented gives projective.
This avoids incorrectly treating `f_i G_i` itself as central. The exact
image/kernel statement still requires the deformed analogue of KKO
Lemma 8.2, in addition to the two norm identities.

Even a successful all-content action does not by itself solve fixed-weight
separation in general type. Dominant highest weights need not be cofinal
in a fixed root-lattice coset, especially in affine or indefinite type.
The rank-one fixed-weight rectangle argument does not remove this
obligation. A Webster comparison or a compatible highest/lowest-weight
construction may still be needed after the categorical extension.

### Ideal decomposition and intertwiner signs

There is a direct PBW proof of the deformed Lemma 8.2(i). Put
`f = Σ_i f_i(x₁)e(i,...)`. Each polynomial has even total parity.
It commutes with crossings `τ₂,...,τ_n` and with dots `x_k`, `k>1`:
in an exterior-coefficient term the signs from its odd dot and odd
coefficient cancel. On each first-colour idempotent the normality rule
for `x₁` is the ELV translation by `2d_i`; coefficients themselves
supercommute with the even `f`. Consequently `f` normalizes the entire
polynomial coefficient algebra.

Choose PBW reduced words using the left cosets of the subgroup generated
by `s₂,...,s_n`, with representatives `1,s₁,s₁s₂,...,s₁...s_n`.
Move polynomial coefficients across `f` by normality, and move subgroup
crossings across it by commutation. Any discrepancy between a chosen
reduced word and this factorization is a sum of terms of smaller crossing
length; induction applies to those terms. This proves
`R f R = Σ_(a=0)^n R f τ₁...τ_a`.
This argument uses independent `d_i`; it never equates different colours'
parameters. For part (ii), multiply by `e(β,i)` on the right. Every
representative with `a<n` lies in the old `R(β)` algebra, so its term
belongs to `R f R(β)e(β,i)`; only `a=n` remains. The reverse containment
is immediate from the two-sided ideal. This proves the asserted ideal
decomposition. Identifying its last summand with the precise balanced
image of `P` still requires the deformed analogue of (8.3)--(8.4).
These statements are not yet native Lean theorems.

For the norm calculation, the local sign issue can also be separated
from quotient bookkeeping. If an odd intertwiner satisfies
`x g = -g y`, `d g = -g e`, `q g = g r`, and `C g = g D`, then
`(C-xdq)g = g(D-yer)`. Both this identity and its all-positive version
are kernel-checked as `even_cutoff_transport_neg/pos` in
`CyclotomicNorm.lean`. In the coefficient-supercentral case `e=d`;
there is no new translated coefficient. This is the local ingredient
in (8.17), not a proof of the entire inductive (8.14) quotient identity.

### A shorter projectivity route using the even square variable

There is a better ordering of the preceding proof obligations. In
[Kang--Kashiwara, arXiv:1102.4677v4](https://arxiv.org/abs/1102.4677),
Lemma 4.19 derives the companion `PQ` identity using an already-known
monic annihilator. Deriving that annihilator only from `PQ` would be
circular. Our conjugate identity supplies an independent starting point.

For each odd colour, `C_i(x₁²)²` vanishes in the deformed cyclotomic
quotient. For an even colour use `f_i(-x₁)f_i(x₁)` and normalize its
leading sign. Taking the product over the finitely many colours in the
content gives a monic polynomial `g(x₁²)` annihilating the quotient.
KKO Lemma 7.3 propagates precisely such an annihilator to all other dot
squares. Its different-colour step uses the leading unit of `Q`; its
same-colour step uses the square-variable identity in Lemma 7.2. These
calculations involve even coefficients and therefore remain valid after
adjoining independent exterior parameters and imposing their top
relations. No flatness of that coefficient extension is needed for an
identity to survive the extension. This also avoids assuming that the
chosen cutoff vector is realized by a dominant weight in a fixed coset.

Now restrict the split variable to `s=t²`. The ELV twist fixes it:
`(t-2d_i)²=t²`. Both polynomial actions are therefore actions of the
ordinary central polynomial algebra `B[s]`, and `P` is `B[s]`-linear.
The skew algebra `B[t;parity]` is free of rank two over `B[s]`, so the
PBW projective modules `K₀,K₁` remain projective after restriction.
Once the exact sequence and the `QP` injectivity argument are in place,
the sequence is a projective resolution of length one over `B[s]`.
Apply Kang--Kashiwara Lemma 4.18 with the independently obtained central
monic annihilator in `s`. Its explicit splitting argument yields
projectivity over `B`, without needing `PQ` or an arbitrary-base-change
argument. This paragraph is a paper-level conditional application of
that lemma; the full deformed bimodule sequence is not formalized here.

Finally, to obtain `PQ`, prove the commuting square between the norm
operators and `P`, and use
`QP` to show that `PQ-A₀` vanishes on `im P`. It factors through the
cyclotomic cokernel. Every such `B[s]`-linear map into `K₀` vanishes:
the cokernel has a monic annihilator, whereas monic multiplication is
injective on the PBW projective module `K₀`. This is exactly the
torsion-versus-torsion-free argument of Lemma 4.19, now applied to the
even square variable. It avoids cancelling a non-surjective `P`.

The prospective parity extension should be kept separate. At an odd
cutoff, `f=(d-x)q(x²)` becomes `-u q(u²)` after `u=x-d`; odd-dot
translation preserves squares. A mixed family of even-cutoff ELV
reservoirs and translated ordinary odd-cutoff reservoirs may therefore
handle different odd-height components. It still requires the full
categorical translation and mixed-family action; the even-cutoff audit
above does not already prove those statements.

### All-content norm audit, with map conventions

Keep KKO (8.2)'s underlying right-`B` modules, with even cutoffs at odd
colours, and use (8.5)'s `P` and Proposition 8.4's `Q`. Give `P` the
ELV semilinearity `P(zt)=P(z)(t-2d_i)` rather than asserting its original
polynomial linearity. The following checks isolate the coefficient
extension from the original affine calculations.

* **`Q` descent.** Relations (8.13) move each old dot and crossing across
  `g_n...g_1`. A homogeneous base coefficient moves across that product
  with the same parity sign already supplied by `Π_i^{p(β)}` in the
  codomain. Thus adjoining independent `d_j` does not add a translation
  to `Q`. In particular, transported old cyclotomic relations vanish
  in the source-side quotient. The dot-polynomial action of `Q` remains
  the one in Proposition 8.4.
* **`QP` induction.** In the different-colour step (8.15), the affine
  crossing square and transport of `Q_{i,j}` are unchanged. In the
  repeated odd-colour step, the new polynomial enters through (8.17).
  The matching-sign transport above moves its entire even expression
  to `f_i(x₂)` with the original sign. All subsequent uses of (8.10)
  are affine identities. The two cancellations after (8.17) remain
  valid: in first-dot PBW coordinates their multipliers have leading
  coefficient a sign unit. They do not require the exterior base to
  be a domain. Consequently the same induction gives the (8.5) norm
  formula with `a_i` replaced by `f_i`.
* **Commuting norm square.** For odd `i`, the norm is
  `A_i(t)=f_i(t)G_i(t²)`. The translation fixes both `t²` and `td_i`,
  hence fixes `A_i`; every allowed `Q_{i,j}` is even in the odd
  variable. For even `i`, ordinary polynomial linearity applies.
  Thus `P A₁=A₀ P` follows from the precise semilinearity, not from
  treating the odd-coefficient norm as central in `t`.
* **Companion norm.** The central-square annihilator argument above
  now proves `PQ=A₀` by factorization through `coker P` and monic
  injectivity on `K₀`.

These are a paper-level extension audit of the specified source proofs.
They depend on the deformed balanced `P` map and exact image/kernel
identification, the PBW module descriptions, and the source's parameter
hypotheses. The ring transport and translation identities are checked
in Lean; the all-content quotient bimodules and their norm identities
are **not** represented by native Lean declarations yet. This should
not be reported as an existing formal theorem of full SKM independence
or as the completed categorical inversion theorem of Section 9.

The companion [multicolour cyclotomic audit](MulticolourCyclotomicAction.md)
now supplies the missing paper-level balanced-`P` calculation: sliding
an old dot deletes a crossing only in the matching-colour case, and
sliding an old crossing produces a braid-correction term only in the
corresponding repeated-colour case. In each case the shorter prefix
moves that matching colour to the first position, putting the error
in the old cyclotomic ideal. Together these notes give a proposed
all-content even-cutoff projectivity argument with independent odd
parameters. The boundary is still the full categorical inversion
argument and its realization as an SKM action, plus native formalization
of the quotient maps. In particular this is not yet a solution of
fixed-weight SKM independence.
