# Corrected mixed braid under signed right multiplication

**Status: common-content operator braid checked in Lean.**
`ELVContentMixedBraid.contentMixedBraid_source_linear` formalizes §2 on
normalized common-content induction operators.
`ELVContentMixedPolynomial.contentMixedBraid_polynomial_linear` formalizes
the ordered original-Sc polynomial comparison in §3, including the full
residual twist and arbitrary-exponent support identity. The block-to-iterated
single-letter comparison in §4 is not supplied by these theorems. This does
not certify the other action data or assert a full SKM action.

The target is exactly `SKM/Presentation.lean`, `relation` at
`Rel.braidEq i j λ hij` (lines 264–278). The algebra input is the independent
quiver-Hecke presentation, `QuiverHecke/Presentation.lean`, `Rel.braidEq`,
transported to ordinary matrix multiplication by
`CyclotomicAction/BraidCorrection.lean`, `affineTriple_braid_correction`.
No action braid is assumed. The argument below applies before taking any
cyclotomic quotient.

## 1. Hypotheses and coordinates

Let k be the purely even commutative ground ring, D the given Cartan
superdatum, and Sc its prescribed scalar data. Retain the unit hypotheses
of Sc (in particular the prescribed invertibility of 2 at odd colours).
Let A be a supercommutative coefficient k-superalgebra. It may contain
independent odd parameters; it is not treated as an ordinary even scalar
ring. Work in the coefficient-extended affine algebra with scalar data
S = parameterTwist D Sc, or any homogeneous two-sided quotient of it.
The full-ELV quotients in `DeformedActionAssembly.md` are such quotients.

Fix distinct colours i,j, and put p=|i|, q=|j| in {0,1}. Every exponent
of (-1) below is read modulo 2. For an allowed coefficient c=c_(r,s) of
Q^Sc_ij, with r,s nonnegative integers, the support laws are

    pr = 0 mod 2,                 qs = 0 mod 2.             (1)

Thus r is even when i is odd, and s is even when j is odd. These are
separate restrictions, not merely pr+qs=0. For interior coefficients they
are `Sc.parity_of_ne_zero`; for leading terms they follow from
`SKM.parity_mul_dn`. Zero coefficients can be omitted. The coefficient
in S is

    c' = (-1)^T c,       T=pq+p floor(r/2)+q floor(s/2).     (2)

This is the existing `parameterSignExponent`/`parameterTwist`, including
the leading t_ij coefficient. No change of normalization is made.

Fix an old word of length n. Number the three appended algebra positions
1,2,3 (in the code n,n+1,n+2). Write their dots as x₁,x₂,x₃. On the
repeated-colour corner these have parities p,q,p. Write τ₁,τ₂ for the
crossings of algebra positions (1,2),(2,3), with word idempotents implicit.
Products are ordinary algebra products, not diagram-list concatenation.

An SKM word E_i E_j E_k acts by E_i applied after E_j after E_k.
Consequently its appended algebra tuple is (k,j,i): the SKM left strand
is algebra position 3, the middle is 2, and the right is 1. This is already
visible in `InductionComposition.lean`: `compositionCorner i j` uses
φ_i ∘ φ_j and hence appends j before i. A right multiplier reverses the
direction of its algebra diagram, as specified in `SuperCrossing.lean`.
Both reversals must be retained, even though the tuple (i,j,i) itself is
palindromic.

For homogeneous z put h=|z|, its TOTAL parity, including A. The operators
are R_a(z)=(-1)^(|a|h)za, with crossing R_τ at distinct colours and
−R_τ at equal colours. The dots are R_x. Sequential application of
homogeneous multipliers a₁,…,a_m gives

    (-1)^(h Σ|a_t| + Σ_(u<v)|a_u||a_v|) z a₁…a_m.          (3)

Induction on m proves (3), since the next input has parity h+Σ|a_t|.
In particular this does not replace h by the parity of the affine factor.

## 2. The named algebra relation and the crossing side

The algebra relation is

    B := τ₁τ₂τ₁ − τ₂τ₁τ₂
       = Σ_(r,s) Σ_(0≤b<r) (-1)^(p(q+b)) c'
                              x₁^(r−1−b) x₂^s x₃^b.     (4)

This is `affineTriple_braid_correction`, with its
`tripleBraidCorrection` definition: diagram composition is reversed by
matrix multiplication. For example its first product is
`L(j,i,i) * (R(j,i,i) * L(i,j,i))`. Each τ has the colour labels determined
by these corners; (4) does not multiply three copies of a fixed off-diagonal
matrix entry. The leading sum has r=D.dn i j, s=0; the interior sum has
the precise open-interval bounds in the presentation. Terms with r=0
have an empty correction, including the other leading monomial.

Let L be the image of the SKM first–second–first crossing diagram minus
the second–first–second diagram, in their displayed bottom-to-top order.
The algebra-position and corner table is

| SKM layers | successive right multipliers |
|---|---|
| left pair, right pair, left pair | R(i,i,j), L(i,i,j), R(i,j,i) |
| right pair, left pair, right pair | L(j,i,i), R(j,i,i), L(i,j,i) |

Here L(a,b,c) is the algebra diagram crossing the first pair of tuple
(a,b,c), and R(a,b,c) the second pair, exactly the names in
`BraidCorrection.lean`. In the first row the first multiplier has algebra
source (i,i,j) and target (i,j,i), so right multiplication starts on the
required (i,j,i) left ideal. This checks the direction, not only the indices.
The products in chronological right-multiplication order are respectively
τ₂τ₁τ₂ and τ₁τ₂τ₁, i.e. the negative of (4).

In either row the three multiplier parities are pq,p,pq. Their sum is p;
their pairwise-product sum is pq (the other two terms cancel). There is
exactly one equal-colour crossing, hence one additional minus sign. Thus

    L(z) = (-1)^(1+pq+ph) z (−B)
         = (-1)^(pq+ph) z B.                              (5)

The reversal minus and the equal-colour minus cancel. Omitting either
would already give the wrong even-colour correction.

## 3. Ordered dotted terms and arbitrary-exponent identity

For 0≤l<r set a=r−1−l. The target correction term has, in this exact
chronological order, l dots on the RIGHT i, s dots on j, and a dots on
the LEFT i. Their successive algebra multipliers are therefore

    x₁ repeated l times, x₂ repeated s times, x₃ repeated a times.

In particular the resulting ordered monomial is
M_l=x₁^l x₂^s x₃^a, not x₁^a x₂^s x₃^l. Formula (3) says that the
image of this dotted diagram on z is

    (-1)^(ph+H) z M_l,                                    (6)
    H = p binom(l,2)+q binom(s,2)+p binom(a,2)
          +pq s(l+a)+p la.

Indeed its total parity is p(l+a)+qs=p(r−1)+qs=p by (1).
Since binom(l+a,2)=binom(l,2)+binom(a,2)+la, and qs=0,

    H = p binom(r−1,2)+q binom(s,2)
      = p floor((r−1)/2)+q floor(s/2) mod 2.               (7)

The last equality uses the integer identity
binom(m,2) ≡ floor(m/2) mod 2, valid for every nonnegative m: write
m=2v+ε and subtract v to obtain the even integer 2v(v−1+ε).
There is no bounded-degree test in this argument.

The target coefficient multiplying (6) is (-1)^(p(q+l))c. Hence its
total sign exponent is

    E_target = ph+pq+pl+H.                                (8)

In (4), reindex b=a=r−1−l. This is an involution of {0,…,r−1} and
turns its ordered monomial exactly into M_l; no dot commutations occur.
Using (2) and (5), the algebra side's total exponent on z c M_l is

    E_algebra = pq+ph+p(q+a)+T = ph+pa+T.                 (9)

The required symbolic identity is

    pq+pl+H = pa+T mod 2.                                (10)

After inserting T and (7), the difference is

    p[(l+a)+floor((r−1)/2)−floor(r/2)].                   (11)

If p=0 it is zero. If p=1, (1) forces r=2v; since l<r, v≥1.
Then l+a=2v−1 and the bracket in (11) is
(2v−1)+(v−1)−v=2v−2, an even integer. This proves (10)
for arbitrary exponents on the entire admissible support. The argument
includes s=0 and hence the leading t_ij correction without a separate
normalization. For r=0 there is no l and both correction sums are empty.

Equations (8)–(10) prove termwise equality after the stated reindexing.
Summing over the finite prescribed support proves that the image of
`Rel.braidEq i j λ hij` is zero.

## 4. Odd coefficients, quotients, and scope

The common ph in (8) and (9) cancels for every homogeneous z, including
z with an arbitrary product of independent odd coefficients in A. The
parameters c belong to even k, so moving c past z introduces no sign.
No odd coefficient is moved through a dot in this proof. Equivalently,
replacing z by αz adds p|α| to BOTH exponents. This proves the required
A-superlinearity rather than accidentally proving only the even-coefficient
specialization. Additivity handles inhomogeneous elements.

The equality is affine and therefore survives every homogeneous two-sided
quotient, including the full-ELV ideal; no centrality of its generators,
flatness, or projectivity is used. Under the multiplication contractions of
iterated induction, the placed generators are exactly these R_x and ±R_τ:
for a dot on an inner tensor factor, its tensor sign and supercommutation
past the intervening outer factors combine to give its total R_x sign.
For a dot on an outer factor, commuting its appended generator past the
inner factors supplies the same sign. The identical computation with
parity pq gives the crossing formula. Thus (3) accounts for these signs
without an extra horizontal scalar. Tensoring the resulting right-linear
kernel identity with any module preserves the equality.

`GlobalBraidAlgebra.lean` supplies only equal-colour braid theorems; it
cannot discharge this comparison. `BraidOperators.lean`,
`cyclotomicSignedTriple_braid_correction`, supplies a corrected regular
operator identity for ordinary cyclotomic polynomials, but still leaves
(2), the position table, and (10) to compare with the specified SKM
relation. Its generic multiplier calculation is consistent with (3)–(5).
The new content here is that explicit arbitrary-exponent comparison.

The common-content mixed relation is now a Lean linear-map equality,
`contentMixedBraid_polynomial_linear`. The remaining passage from appended
blocks to iterated single-letter induction, other action relations and
weight assembly are not consequences of this equality alone. The proposed
action and integer grading in `DeformedActionAssembly.md` and
`DeformedGradedAction.md`, fusion, bubble normalization, fixed-weight
detection and nondegeneracy retain their separate proof obligations.