# Cyclotomic deformation and lifting the local map

**Status: proposed mathematical arguments, not Lean theorems.** This resolves
which deformation statement can be asked in A0-deform of
NondegeneracyProof.md §4.2. Its unrestricted homogeneous-polynomial version is
false. The translated KKO subfamily has a general freeness argument. The
full mixed-cutoff ELV family still needs the deformed multicolour projectivity
argument; reduction modulo exterior parameters does not supply it.

## 1. Source hypotheses and the polynomial families

The sources used here are KKO I, arXiv:1206.5933v2, §§4, 7–9; KKO II,
arXiv:1303.1916v2, §8.3; and Ebert–Lauda–Vera (ELV),
arXiv:2203.14153v2, §§3.5–3.7, 4.6 and Theorem 5.9.

KKO I starts with a nonnegatively graded **ordinary commutative** coefficient
ring with 2 invertible. Its cyclotomic coefficients need not vanish: the
polynomial of degree N_i has coefficient c_(i;k) in degree k(α_i,α_i), but
c_(i;k)=0 for odd k when i is odd. The coefficient ring has no odd super
scalars. KKO II additionally assumes its degree-zero ring is a field of
characteristic different from two. Thus “KKO only treats a field and
undeformed polynomials” is too restrictive; “KKO allows arbitrary homogeneous
odd coefficients” is too broad.

Keep a finite compatible symmetrizable Cartan superdatum and the KKO
homogeneous Q parameters: the leading coefficient is a unit, the pair
symmetry holds, and an odd variable occurs only to even powers. Put
D_i=(α_i,α_i). At even colours use an arbitrary homogeneous monic polynomial
of degree N_i with **even** coefficients of degrees kD_i.
At odd colours the following are three different families.

* **KKO:** g_i(x)=C_i(x²) for N_i=2m, and g_i(x)=x C_i(x²)
  for N_i=2m+1; C_i is monic of degree m with even coefficients.
* **Translated KKO:** extend by independent odd d_i of degree D_i, and
  translate each odd-colour dot by −d_i. For odd N_i the polynomial becomes
  (x−d_i)C_i(x²). For even N_i it remains C_i(x²): translation cannot
  manufacture the even-cutoff ELV deformation.
* **ELV:** write C_i(z)=z^m+χ_(i,1)z^(m−1)+…+χ_(i,m), with
  deg χ_(i,r)=2rD_i. For N_i=2m>0 put q_i(z)=(C_i(z)−χ_(i,m))/z and use
  f_i(x)=C_i(x²)−x d_i q_i(x²), over
  A_i=k[χ_(i,1),…,χ_(i,m)]⊗Λ(d_i)/(d_iχ_(i,m)).
  For N_i=2m+1 use f_i(x)=(x−d_i)C_i(x²), over the same polynomial/exterior
  algebra **without** d_iχ_(i,m)=0. At cutoff zero use f_i=1 and omit d_i.

These are ELV (3.24)–(3.27), with the odd-degree polynomial multiplied by −1
to make it monic. For several colours take their **super** tensor product,
including the even-colour parameter rings; denote it by A. Independent odd
parameters anticommute and their products are not set to zero. Let J be the
ideal they generate. If there are r parameters, J^(r+1)=0, including after
the displayed ELV relations. A/J is a purely even polynomial parameter ring.
All even Q parameters are extended from the even base.

This is the accepted polynomial family for the arguments below, not a
classification of every polynomial that could support an action. A parity
condition alone is insufficient. Nor may A be replaced by a fraction field
of its even variables while claiming to retain every d_i: inverting
χ_(i,m) at even cutoff kills d_i.

## 2. A homogeneous exterior counterexample to unrestricted flatness

Let k be a field with 2 invertible, A=Λ_k(d,e,f), with all three generators
odd of degree D>0. Adjoin an odd variable x of degree D that supercommutes
with A; x itself is not square-zero. Impose the homogeneous, monic, even
relation

    p=x²−xd+ef=0.

This satisfies the parity and positive-degree requirements of §4.1 of the
main draft. In the two-sided quotient B, computing xp−px gives −2x²d.
Hence x²d=0. Multiplying p by d on the right gives x²d+efd=0, so def=0 in B.
But def is nonzero in A, and B/JB=k[x]/(x²) is nonzero.

The algebra B is finite over A: its defining monic relation reduces every
power of x to the A-span of 1,x. A is an Artinian local ring as an ungraded
associative ring. If B were flat over A, it would be finite projective and
therefore free. A nonzero free A-module cannot be annihilated by def. Thus B
is **not flat over A**, already at one odd strand. This is not a large-degree
or numerical test and is not a counterexample to the ELV family: precisely
the missing condition d(ef)=0 accounts for the failure.

A separate base-ring issue persists even for correct universal ELV
coefficients. At cutoff 2m, A_i itself is not flat over Λ(d_i) when m>0.
Indeed χ_(i,m) lies in ker(d_i:A_i→A_i) but not in d_i A_i. Tensoring the
inclusion (d_i)→Λ(d_i) with A_i would have to be injective for flatness,
whereas its induced map A_i/d_i A_i→A_i kills χ_(i,m). The vacuum algebra
is A, so “every block is free over the exterior subalgebra” cannot be the
universal ELV theorem. Freeness **over A** is the appropriate candidate.
ELV proves rank-one A_i-freeness (Theorem 5.9, Remark 5.10), not multicolour
freeness over an independent exterior/polynomial tensor product.

## 3. Normality, translation and the part that is free

For even ELV cutoff, using d_iχ_(i,m)=0 gives

    x f_i=f_i(x−2d_i),     a f_i=f_i a  (a in A).

The first-dot normalizer fixes coefficients, so its inverse translates x by
+2d_i. For odd cutoff, f_i is odd and instead

    x f_i=f_i(x−2d_i),     a f_i=(−1)^|a| f_i a.

The normalizer acts by the parity involution on coefficients and sends
x to x−2d_i; it is involutive. Its square-variable annihilator is
f_i²=x² C_i(x²)². At even cutoff the conjugate product gives C_i(x²)².
These even central monic square polynomials are the usable annihilators;
first-dot centrality is not available.

The simultaneous affine substitution x_a↦x_a−d_(ν_a) at chosen odd colours,
fixing coefficients, crossings and idempotents, preserves the KKO relations.
Odd squares are fixed; the extra terms in dot slides cancel by the signed
coefficient commutation. The repeated-outer odd braid numerator is a sum of
terms x^(2s)(x b−b z)z^(2t) with b even, so it is fixed too. This is the
argument already in OddCutoffAction.md, with local Lean identities in
ExteriorTranslationRelations.lean; those identities are not yet a bundled
affine equivalence. Translation respects strand inclusions and carries the
entire two-sided ideal generated by g_i to the one generated by f_i.
It therefore gives the compatible quotient-tower equivalence for the
translated KKO family. No flatness assumption enters this descent.

Here is a general freeness argument for that family. Let C be the purely
even, connected nonnegatively graded polynomial coefficient ring over k
containing the homogeneous parameters. KKO I Theorem 8.5 gives the
projectivity of each induction corner over the preceding cyclotomic block;
§7 gives finiteness over C. Induct on the content height. The vacuum is C.
For β≠0, decompose R^Λ(β) by its last-colour idempotents. Each summand
R^Λ(β)e(β−α_i,i) is a finite projective right R^Λ(β−α_i)-module. If the
preceding algebra is C-projective, a summand of a finite sum of its grading
and parity shifts is C-projective. Thus every block is finite graded
C-projective, without using any claimed cyclotomic PBW basis.

A finite graded projective module M over such a connected ring is graded
free: lift a homogeneous k-basis of M/C_+M to obtain a map F→M from a finite
graded free module. Graded Nakayama gives surjectivity. Projectivity splits
this map; hence its kernel K is a finite graded direct summand. Reducing the
split sequence shows K/C_+K=0, and graded Nakayama gives K=0. The splitting,
not Nakayama alone, is the independence argument.

Consequently, extending to C⊗Λ(d_i) gives a finite free module of the same
homogeneous rank, and the translation equivalence gives that freeness for
the translated family, at every content. The rank is that of the reduced
KKO block. Further coefficient specializations preserve this exhibited
basis. This covers arbitrary choices of cutoff parity if the even-cutoff
odd-colour polynomials remain undeformed KKO polynomials. It does **not**
cover nonzero even-cutoff ELV terms −xd_i q_i(x²).

The same induction would prove A-projectivity for the full ELV family once
its deformed induction corners are projective over preceding blocks. For
the connected graded universal A above, the splitting/graded-Nakayama proof
also works for graded supermodules, giving A-freeness. Thus A-freeness is a
consequence of the deformed KKO projectivity step, not an independent
shortcut around that step. ActionReview.md §§2–5 proposes the requisite
balanced P,Q construction, central-square-variable argument and opposite-side
projectivity. The all-content balanced deformed resolution remains the
specific missing construction; neither rank-one ELV nor translation proves
it in the mixed-cutoff multicolour case.

## 4. A sharper local lifting lemma

Let A be any coefficient superalgebra, J a homogeneous nilpotent two-sided
ideal, and u:M→N an even A-linear map (absorb parity shifts into M,N).
Assume that its reduction ū:M/JM→N/JN is an isomorphism and

    Tor_1^A(A/J,N)=0.

Then u is an isomorphism. No freeness assumption on M is needed. Indeed,
the cokernel C satisfies C/JC=0, whence C=0 by iterating the nilpotence of
J. In 0→K→M→N→0 the Tor hypothesis makes K/JK→M/JM injective.
Its image is ker(ū)=0. Thus K=JK, and nilpotence again gives K=0.
This works for arbitrary modules; finite generation is not needed here.
Flatness of N is a sufficient, stronger hypothesis.

Alternatively, for projective M,N lift ū^(-1) to an A-linear v. Both
vu−1 and uv−1 map into J times the appropriate module; their successive
powers map into successive powers of J. Finite geometric inverses give
both a left and a right inverse to u, which coincide. The lifting of v is
where projectivity is used. An isomorphism of reductions alone has no such
consequence: A→A/J is a counterexample.

## 5. Applying the lemma to the specified Rouquier map

At a fixed content and colour, take M,N to be the **representing
superbimodules** of the two sides of the required Rouquier matrix, with every
integer and parity shift included. Its components are the prescribed
cup–crossing–cap mate σ and the prescribed dotted counits or units. To use
§4 one must supply all of the following.

1. The two-sided quotient presentations reduce to the KKO quotient, including
   the same cutoff N_i and the transported Q parameters. This comparison
   follows from right exactness of coefficient extension on the presentation,
   not from a dimension count.
2. Strand inclusions and colour idempotents reduce to the specified ones.
   Their induction and restriction corners therefore base-change correctly.
   Balanced tensor products commute with coefficient extension; thus the
   composite EF and FE kernels do too, without first assuming flatness.
3. The chosen unit is tensor insertion and the chosen counit is multiplication.
   These formulas commute with base change, as do the signed dot and crossing
   multipliers. Their composites and whiskerings therefore carry σ to the
   **same** reduced cup–crossing–cap map, not just a map between isomorphic
   functors. Any additional adjunction used in the chosen orientation needs
   its own comparison; it cannot be chosen afresh after reduction.
4. Prove that this reduced matrix is invertible. An abstract KKO direct-sum
   decomposition is not enough. This is A1-map, with the presentation signs
   and parameter transport fixed before the comparison. In particular signed
   right multiplication is a super-opposite representation; the signs in
   ParameterTransport.lean cannot be dropped.
5. Prove Tor_1^A(A/J,N)=0 for the **target convolution kernel** (or prove
   both kernels projective). Algebra freeness by itself is not automatically
   freeness of a balanced tensor product over a nonsemisimple intervening
   algebra. A sufficient route is A-projectivity of blocks together with
   projectivity of the relevant induction/restriction corners over their
   adjacent blocks: split the relative projective module off finite shifted
   copies of that block, tensor, and obtain an A-projective summand.

An A-linear inverse to a bijective bimodule map automatically respects both
bimodule actions and the grading; tensoring it produces the natural inverse.
Thus no bimodule-projectivity over an enveloping algebra is required for the
lifting step. There is also no need to lift an unspecified natural inverse
in a functor category.

For the translated KKO subfamily the tower equivalence transports the
adjunction outright. Restoring the unshifted dots changes each odd power by
d_i times the preceding even power and leaves each even power fixed. After
the parity shifts this is an invertible unitriangular row/column operation
on the dotted entries; the mate itself is unchanged. This is precisely the
already proved operator mechanism in SKM/OddDotTranslation.lean. It transfers
a proof of the **specific** reduced map, not merely an abstract decomposition.
The cutoff degree stays N_i, its polynomial parity stays p(i)N_i, and the
height and number of dotted summands are unchanged, including height zero.

## Conclusion for A0-deform

* Arbitrary homogeneous exterior-coefficient polynomials: flatness is false.
* Translated KKO polynomials: general tower freeness follows as above, and
  deformation transport of the specified map is reduced to the undeformed
  A1-map comparison, with no extra nilpotent lifting hypothesis.
* Full ELV family, including even odd-colour cutoffs: use its actual ring A,
  not an independent polynomial/exterior ring. Rank-one A-freeness is in ELV;
  multicolour freeness still requires the deformed projective-resolution step.
  The precise local lifting input can be weakened to Tor vanishing for the
  target kernel, but no source-checked argument here establishes that vanishing
  independently of the same projectivity construction.

No general multicolour deformed local inversion, and no nondegeneracy theorem,
is asserted by this document.
