# Input-side prepend coordinates

## Status and precise assertion

This is a **proposed written proof, not a Lean-checked coordinate equivalence**.
The checked portion is `InputParabolic.lean` (unique input permutation and
reduced concatenation) and `CyclotomicAction/PrependCoordinates.lean` (the
specified crossing elements, coefficient terms, corner membership and their
right-old-algebra law). Neither file assumes a coordinate equivalence.

The target is the affine decomposition needed for Kang–Kashiwara–Oh,
*Supercategorification of quantum Kac–Moody algebras*, arXiv:1206.5933v2,
Lemma 8.1, used for cancellation in the repeated-colour case of Theorem 8.5.
This argument concerns the library's quiver Hecke supercategory over a
commutative ring k with datum D and its existing scalar datum Sc. Colours are
finite, as required for the units of `Hn`. There is no additional assumption
of a field, a domain, flatness, projectivity, monicity or an injective dot
operator. No grading-freeness assertion is made.

Fix i and n ≥ 0. Set

- B = `Hn D Sc n`, A = `Hn D Sc (n+1)`;
- φ = `prependAlgebra D Sc i n`, e = φ(1);
- C = {z ∈ A : ze=z}, the existing `InductionAlong.Corner φ`;
- x = `affineFirstDot D Sc i n`.

The claim proved below in ordinary algebra is a k-linear, right-B-compatible
bijection

    Φ : (Fin(n+1) × ℕ →₀ B) → C,
    Φ(b) = Σ_(j,m) c_j x^m φ(b_(j,m)).                         (1)

The right B-action on the source is coordinatewise multiplication. Right
linearity is ordinary, not super-linearity with an implicit parity shift.
The c_j need not be homogeneous as sums over colours.

## Permutation orientation and the index

In `Spanning.lean`, `cw σ = σ.reverse.map PG.cross`. Thus the chronological
crossings `cw(α ++ β)` execute β first and α second. The target word satisfies

    tgt(t,cw σ)[q] = t[(wordProd σ)⁻¹(q)].                     (2)

Let h : 1+n=n+1. A `Shuffle h` is u for which u⁻¹ is increasing separately
on the first block and on positions 1,…,n. Put d=u⁻¹. Then d preserves the
order of the old positions. It is determined by j=d(0): its values on
1,…,n are precisely the increasing enumeration of the complement of {j}.
Conversely this prescription for each j is a permutation whose inverse is
a shuffle. This establishes the indexing by Fin(n+1), including n=0.
Denote it by d_j. Chronologically, d_j moves the new first strand through
positions 0,…,j-1, leaving the old strands in their order. Any fixed reduced
word for this permutation can be used; the checked construction chooses
`canWord (n+1) d_j`.

Apply `parabolicEquiv h` to w⁻¹. It gives uniquely

    w⁻¹ = blockPerm h 1 a · u.

Inverting yields

    w = d_j · blockPerm h 1 v,       v=a⁻¹.                  (3)

Uniqueness follows by inverting a second such expression and applying
`blockPerm_mul_injective`; no diagram reflection is involved. Invariance
of Coxeter length under inverse and `length_blockPerm_mul` give

    length(w) = length(v) + length(d_j).                     (4)

Consequently the word

    canWord(n+1,d_j) ++ shiftWord 1 (canWord(n,v))

is reduced with product w. Its `cw` executes the old crossings first.
These are the checked `prependPermutationEquiv`,
`length_prependPermutation` and `prependCrossingWord_spec`.

## The crossing sums and the corner

For an old word ν, let ins_j(i,ν) be insertion of i at position j. Let
ψ_(j,ν) : i::ν → ins_j(i,ν) be the crossings of the selected reduced word
of d_j. In matrix conventions rows are targets and columns are sources;
matrix multiplication executes the right-hand diagram first. Define

    c_j = Σ_(ν : Word I n) E_(ins_j(i,ν), i::ν)(ψ_(j,ν)).      (5)

This finite sum is `prependShuffleElement`. It is not a sum over all
permutations, and it does not divide by a colour stabilizer. Repeated
colours cause no collapse of permutation indices in `basisNF`.
The diagonal idempotent e is the sum of the identities on i::ν. Orthogonality
of matrix entries proves c_j e=c_j and xe=ex=x. For m=0, x^0 is 1_A,
not e, but the final φ(b) in (1) makes this distinction harmless. For all m,

    (c_j x^m φ(b))e = c_j x^m φ(b).

This last equality is `prependPBWTerm_corner`. Multiplication on the right
by e projects a matrix to the columns i::s, so a scalar basis of C consists
of all `basisNF (i::s) t`, embedded into those matrix entries. This follows
entrywise from the finite-support matrix definition, not from a module
basis assumption.

## Scalar triangularity: explicit leading-index bijection

A scalar basis of B is obtained by placing each `basisNF s ν` in its matrix
entry (ν,s). Write such an old basis element as b_(s,ν,L,v), where L is its
sorted old-input dot list and v is its permutation. Its image in the (j,m)
summand of (1) is, chronologically:

1. dots on positions L+1 in i::s;
2. the old reduced crossings for v, shifted by 1;
3. m dots at position 0;
4. the selected reduced crossings for d_j.

Move the m new dots below the old crossings and then below the old dots.
Every old crossing has positions at least 1, so the new dot is disjoint
from it. Every old dot has positive position. These moves use only super
interchange signs and never the adjacent dot-crossing correction. The
resulting input dot list is

    L' = [0 repeated m times] ++ map (·+1) L.                 (6)

It is already sorted. The accumulated factor is a unit sign (for a
homogeneous old basis element, the interchange contribution is
(-1)^(m p(i) parity(b))). No coefficient is moved through an arbitrary
inhomogeneous algebra element in this argument.

By (4), the remaining crossings form a reduced word for
w=d_j blockPerm h 1 v. Reduced-word straightening to `canWord(n+1,w)`
changes this diagram by a unit leading sign and a finite combination of
normal forms whose permutation length is strictly smaller than length(w).
This is exactly the reduced-word `Approx`/straightening used by
`shElt_approx`; here the dots already precede all crossings. Correction
terms may carry more dots, but have fewer crossings. Thus each image has
a unit leading coefficient at

    (source i::s, target ins_j(i,ν), dot list L', permutation w).   (7)

The map of scalar indices in (7) is bijective, not merely injective:

- From any corner normal form with source i::s and permutation w, (3)
  uniquely recovers j and v.
- Its sorted input dot list uniquely recovers m as the number of zeroes
  and L by removing those zeroes and subtracting 1 from every remaining
  position. Validity of the original list gives positions <n in L.
- The old target ν is `tgt(s,cw(canWord(n,v)))`. Formula (2) and (3) give
  t=ins_j(i,ν), so this old normal form has the required endpoint.
- These operations invert (6) and (7) exactly. In particular, if a fixed
  target contains several occurrences of i, j is recovered from the
  permutation, not chosen from the word.

This proves both existence and uniqueness of the leading index using the
actual `basisNF` conventions.

## Spanning and independence, without tensoring scalar independence

Filter the corner scalar basis by permutation length. For spanning, use
strong induction on that length: subtract the inverse leading unit times
the corresponding image (7). The remainder is a finite linear combination
of normal forms of strictly smaller length; the induction hypothesis
expands each one. At length zero the remainder is zero. Hence every element
of C has a finite expansion (1).

For independence, expand a putative finite relation among the images in
old scalar basis elements. Choose a maximal permutation length among its
nonzero coefficients. At each leading index of that length, lower terms
from the selected images cannot contribute; the bijection (7) excludes
any second image with that leading index. Its scalar coefficient times a
unit is zero, so that coefficient is zero. This contradicts its selection.
The argument is valid over a ring with zero divisors, and is also valid
vacuously over the zero ring. It is the argument of `basisOfTriangular`.
It establishes injectivity of (1), not an assumption on it.

Define Ψ(z) by the unique finite expansion. Injectivity gives additivity
and k-linearity of Ψ and both round trips ΨΦ=id and ΦΨ=id. For every r∈B,
associativity and multiplicativity of φ give

    Φ(b r) = Σ c_j x^m φ(b_(j,m) r)
           = (Σ c_j x^m φ(b_(j,m))) φ(r) = Φ(b) φ(r).         (8)

No crossing is commuted with r here. The individual term law is checked as
`prependPBWTerm_right` and `prependPBWCorner_right`. Applying Ψ to (8)
gives Ψ(z φ(r))=Ψ(z)r. This completes the written right-B coordinate proof.

For the whole algebra C the coefficient domain really is free B. After
fixing one target word t, only j with t[j]=i occur, and the j coefficient
lies in e_(delete_j t) B. These are idempotent summands, not copies of B.
After fixing an old content β, (1) restricts instead to copies of the
unital content algebra B_β: all factors preserve content, so no mixing of
contents enters the triangular induction. These distinctions prevent a
false fixed-word freeness claim.

## Explicit balanced extension and coefficient action

For any unital left B-module M carrying a compatible k-action, form the
ordinary balanced tensor C ⊗_B M. This includes the existing integral
balanced presentation `InductionAlong.Ind`: the balancing relations for
scalar multiples of 1_B enforce the required k-balancing. Define

    F : (Fin(n+1) × ℕ →₀ M) → C ⊗_B M,
    F(single_(j,m)(y)) = (c_j x^m e) ⊗ y,

    G(z ⊗ y)_(j,m) = Ψ(z)_(j,m) • y.                       (9)

The finite support of Ψ(z) makes G a finite tuple. Equation (8) proves
G((zφ(r))⊗y)=G(z⊗(r•y)), coordinate by coordinate. Thus G descends through
the actual balancing submodule. Expanding z proves FG(z⊗y)=z⊗y; using
Ψ(c_j x^m e)=single_(j,m)(1_B) proves GF=id. This constructs the inverse
maps and requires no flatness or preservation of injections by tensoring.

Take M to be the prescribed `qCoefficient D Sc i β a ha r` with B at its
actual affine height r+1. Its left B-action is the existing twisted
cyclotomic action; (9) uses this action, not an untwisted substitute. Its
right cyclotomic coefficient action commutes with the left action, so

    G(z ⊗ (y·c))_(j,m) = G(z⊗y)_(j,m) · c.                 (10)

This is the coordinatewise coefficient action. Neither (9) nor (10) is yet
implemented as a Lean equivalence. The new consumer checks the existing
`qCoefficientInsert_mul` together with the original corner term laws.

The checked first-dot square commutation gives

    (c_j x^m φ(b)) x² = c_j x^(m+2) φ(b).

Thus the square of the shifted right dot raises m by two, whereas a right
coefficient operator preserves m by (10). Their monic difference is
injective by inspecting the largest occupied m; the leading coefficient
is a unit identity map on M. Any use of an odd linear difference must
also identify its square and its coefficient operator on the prescribed
tensor; it is not inferred from scalar independence. These cancellation
identifications remain separate Lean obligations.

At n=0 there is one shuffle and one old empty-word idempotent; (1) is the
one-strand dot basis over B=H₀≃k. There is no old last dot in this case.
Nothing here asserts injectivity of a dot minus itself.

## Remaining formalization

Implement the leading-index bijection (6)–(7), its `Approx` statement and
matrix assembly; apply the checked triangular basis construction to obtain
existence and injectivity of (1). Define choice coordinates only after
these two results, prove both round trips, and then implement (9) for the
existing balanced quotient. The checked permutation and affine term laws
remove the need for a global reflection or super-opposite functor; they do
not themselves assert this remaining Lean coordinate theorem or full QP.
